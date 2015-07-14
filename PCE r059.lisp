;;;  -*- mode: LISP; Syntax: COMMON-LISP;  Base: 10 -*-
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 
;;; Author      : Frank Tamborello
;;; Copyright   : (c) 2012, 2013 Frank Tamborello
;;; Availability: Public Domain
;;; 
;;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; This library is free software; you can redistribute it and/or
;;; modify it under the terms of the Lisp Lesser General Public
;;; License: the GNU Lesser General Public License as published by the
;;; Free Software Foundation (either version 2.1 of the License, 
;;; or, at your option, any later version),
;;; and the Franz, Inc Lisp-specific preamble.
;;;
;;; This library is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;; Lesser General Public License for more details.
;;;
;;; You should have received a copy of the Lisp Lesser General Public
;;; License along with this library; if not, write to the Free Software
;;; Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
;;; and see Franz, Inc.'s preamble to the GNU Lesser General Public License,
;;; http://opensource.franz.com/preamble.html.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 
;;; Filename    : pce.lisp
;;; Revision     : 59
;;; 
;;; Description : A model of systematic procedural error, particularly
;;;		postcompletion error.
;;;		Developed with ACT-R6 (r1227) and boost-chunks module v0.5a.
;;; 
;;; Bugs        : 
;;;
;;; To do       : 		
;;; 
;;; ----- History -----
;;;	2013.05.06	fpt	r050
;;;		1. Each step in the humans' task actually consumes anywhere from 2
;;;		to 10 s. Production RETRIEVE-NEXT-PROCEDURE-STEP schedules an
;;;		appropriate delay.
;;;		2. iti set to 1 since much of the delay at the order ticker was
;;;		actually due to subject performance, experiment iti really 1 s
;;;	2013.05.13	fpt	r051
;;;		1. During interruption, the model rehearses its place within the
;;;		primary task. See function check-for-int.
;;;		2. Switched off Trial's sjis.
;;;		3. Bug squashed: For some forgotten reason, process-completed-
;;;		subgoal was called from the end-of-interruption event in addition
;;;		to being called from advance-state. Only advance-state should
;;;		call it.
;;;	2013.05.16	fpt	r052
;;;		Add retrieval reference to trial via process-completed-subgoal 
;;;		500 ms prior to retrieval of the current step rather than at 
;;;		completion of the 
;;;		previous step. If procedure-steps are retrieved by a list 
;;;		walking algorithm as in Anderson et al. (1998), then trial 
;;;		should get bumps immediately preceding retrieval of the current 
;;;		subgoal's first step rather than upon completion of the prior 
;;;		subgoal's last step. This will matter when interruption occurs 
;;;		at subgoal boundaries, as in the postcompletion step.
;;;	2013.05.16	fpt	r053
;;;		Bug hunt: The model's imaginal buffer chunk no longer has wm
;;;		task chunks at the PCS... apparently because those are not
;;;		restored nor replaced at post-tracking resumption.
;;;		Reinstate-context now mods the imaginal buffer chunk
;;;		to have the wm task chunks if the task-id is 4 (B&B load cond).
;;;	2013.05.30	fpt	r054
;;;		Readjust added step latencies for the B&B phaser task:
;;;		Latency for step 3 should be 4.5 s.
;;;		Fire should remain at 9 s.
;;;		All other steps should have no additional latency.
;;;	2013.06.26	fpt	r055
;;;		1. Quick & dirty experimentation with interruption duration after
;;;		Altmann & Trafton (under review): 13.12, 22.02, & 31.91 s.
;;;		2. The UNRAVEL task has a flat structure, so process-completed-
;;;		subgoal is inappropriate
;;;		3. Moved interruption duration from a number hard-coded in
;;;		arith-int's initialization method to a slot of st-exp-window so it
;;;		can be referenced in arith-int's initialization method, make-data-
;;;		path, check-for-int when it creates, the model's rehearsal events,
;;;		and can be set by an argument in run-model.
;;;		4. *iti* moved to a slot of the st-exp-window, since its finish-
;;;		trial method is the only thing to use it.
;;;		5. Bug squash: A task step latency pause event remained in the
;;;		queue when the trial ended (because the model cycles back around
;;;		as far as retrieve-next-procedure-step after it performs the
;;;		last step) so that even fired during the next trial! 
;;;		Although giving the
;;;		task step latency pause event maximum priority and a descriptor
;;;		string is probably a good idea anyway, so I did that, too.
;;;	2013.07.08	fpt	r056
;;;		1. Set *step-names* back to a 10-step procedure
;;;		2. Set interruption onset rehearsals back to 3 at 1 s intervals
;;;		3. Run-model now takes keyword arguments instead of optionals,
;;;		including :m, which gets passed to the experiment window and
;;;		appended to the name of the data file. This makes it easier to 
;;;		run multiple models concurrently.
;;;		4. Check-state-update deleted and now advance-state ends the task
;;;		& trial by comparing state-num to length of the *step-names* 
;;;		list rather than checking the name of the state. This should
;;;		make things easier when running tasks of varying lengths.
;;;		5. Run-model now has an id keyword parameter, which gets passed
;;;		to the task window as the interruption duration (s).
;;;		6. Process-completed-subgoal reinstated after UNRAVEL test in 
;;;		r55.
;;;		7. Appropriately-lengthed pauses reinstated for steps of the
;;;		stock & phaser tasks
;;;	2013.07.08	fpt	r057
;;;		Attempted to explain the subjects' latency feature used by
;;;		Raj Ratwani's logistic regression model predicting PCE in terms
;;;		of retrieval latency at the PC step by adjusting declarative
;;;		chunk activations downward.
;;;		I concluded that my model's compatible with whatever Raj's model 
;;;		detects, but that behavior doesn't apparently fall naturally
;;;		out of my model. 
;;;	2013.07.30	fpt	r058
;;;		Since my Mac has 4 processor cores & Clozure CL supports threads,
;;;		divide the number of model runs given to run-model among 4
;;;		threads... But eventually I did see in the manual that Dan 
;;;		strongly recommends against trying to run ACT-R in threads.
;;;	2013.08.07	fpt	r059
;;;		1. Replace interruption for trial types 3 & 4 with 10-second step 
;;;		completion latencies. Fork from r56 not r57 or r58.
;;;		2. Moved some widget utilities to virtual-experiment-window:
;;;		widget-named, current-widget, & inside.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Load ACT-R
;; (load "/Users/frank/Documents/NRL/Error/actr6/load-act-r-6.lisp")

(defparameter 
    *step-names*
  '(first second third fourth fifth sixth seventh eighth ninth tenth))

(defvar *vis-locs*)

(defvar *exp* "The task environment.")

(defparameter *data-column-headings* "run	trial	kind	step	got	gediff	intrpt	crct	PCE	SCL")
; run#, trial#, trial-type/task-id, procedure step# (zero-indexed), the model's 
; action, got step# - expected step#, the step was/was not interrupted, the
; model's action was/was not correct, PCE was/was not committed, Step Completion
; Latency



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The Task Environment: The Stock Trader Task
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require :virtual-experiment-window)


(defclass st-exp-window (virtual-event-exp-window)
  ((n-of-k :accessor n-of-k :initarg :n-of-k :initform #(6 2 4 0 0))
   (single-trial :accessor single-trial :initarg :single-trial :initform nil)
   (iti :accessor iti :initarg :iti :initform 1)
   (int-dur :accessor int-dur :initarg :int-dur :initform 0)
   (m :accessor m :initarg :m :initform nil)))

;; the task's virtual window
(defclass stock-trader (procedure-window trial)
  (;; state-num before which the interruption occurs, zero-indexed
   (int-staten :accessor int-staten :initarg :int-staten :initform #(nil nil))
   ;; is the stock-trader currently experiencing an interruption?
   (interruption :accessor interruption :initarg :interruption :initform nil)))
;;   (kill-switch :accessor kill-switch :initarg :kill-switch :initform 0)))



(defclass st-action (proc-action)
  ((trial-kind :accessor trial-kind :initarg :trial-kind :initform nil)
   (interrupted :accessor interrupted :initarg :interrupted :initform nil)
   (got-num :accessor got-num :initarg :got-num :initform nil)
   (correct :accessor correct :initarg :correct :initform nil)
   (expected-got-diff :accessor expected-got-diff :initarg :expected-got-diff :initform nil)
   (pce :accessor pce :initarg :pce :initform nil)
   (info :accessor info :initarg :pce :initform nil)))


;; widgets of the task window
(defclass widget ()
  ((nick-name :accessor nick-name :initarg :nick-name :initform nil)
   (vwindow :accessor vwindow :initarg :vwindow :initform nil)
   (vis-loc :accessor vis-loc :initarg :vis-loc :initform nil)
   (vis-obj :accessor vis-obj :initarg :vis-obj :initform nil)))



(defun make-trials (num kind wind)
  (let (accum)
  (dotimes (i num accum)
          (push 
           (make-instance 
               'stock-trader 
             :out-path (data-file wind)
             :task-id kind
             :trial-kind kind)
                accum))))

(defun build-basic-trials (wind)
  (let ((stim-lst nil)
        (n (n-of-k wind))) ; n per kind
    (dotimes (k 5 (flatten stim-lst))
      (when (> (svref n k) 0)
        (push
         (make-trials (svref n k) k wind)
         stim-lst)))))

(defun order-stim-list (in-lst)
  (let ((lst (randomize-list in-lst)))
    (dotimes (i 7)
      (setf lst (randomize-list lst)))
    lst))

(defun do-stimgen (wind)
  (list 
     (let ((stim-lst (build-basic-trials wind)))
       (make-instance 'trial-block
         :size (length stim-lst)
         :trial-lst (if (> (length stim-lst) 1)
                        (order-stim-list stim-lst)
                      stim-lst)))))

(defmethod initialize-instance :after ((wind virtual-event-exp-window) &key)
  (setf (base-path wind) "/Users/frank/Documents/NRL/Error/PCE-Model-Data/"
        (block-lst wind) (do-stimgen wind)
        (nblocks wind) 1
        (write-type wind) :SS))

(defmethod make-data-path ((wind st-exp-window) type)
  (when (base-path wind)
    (make-pathname :directory (base-path wind)
                   :name
                   (format nil "model-data-~a" (m wind))
                   :type type
                   :version :newest)))

(defmethod setup-trial :after ((wind virtual-event-exp-window) (trl trial))
  (install-device trl)
  (proc-display :clear t)
  (unless (single-trial wind)
    (progn
      (goal-focus start-stock-trade-goal)
      (schedule-set-buffer-chunk 
       'imaginal
       (car (define-chunks-fct 
                (if (eq (task-id trl) 4)
                  `((isa task-state step start wm1 a wm2 b wm3 c))
                  `((isa task-state step start)))))
       0 :module 'imaginal))) 
;  (clear-buffer 'imaginal) ; r29
  (start-timing (timer (current-trial *exp*)))
  (model-output "~%Begin new trial.~%")
  (model-output "~%int-staten: ~A~%" (int-staten trl)))









(defmethod initialize-instance :after ((wind stock-trader) &key)
  "Initialize an instance of the stock-trader device class. Make the visual-object
  chunks, encapsulate them and the visual-location chunks in widgets. Set the
  state-vec from the keywords made for the nick-names of the widgets."
    (let
        ((vis-objs
          (define-chunks-fct
              (let ((vo nil))
                (dotimes
                    (i (length *step-names*) (nreverse vo))
                  (push
                   `(isa oval 
                         screen-pos ,(nth i *vis-locs*)
                         color blue)
                   vo))))))
      
      (let ((wgts nil))
        (dotimes (i (length *step-names*) (setf (widgets wind) (nreverse wgts)))
          (push
           (make-instance 'widget 
             :vwindow wind 
             :nick-name (intern (string (nth i *step-names*)) "KEYWORD")
             :vis-loc (nth i *vis-locs*) 
             :vis-obj (nth i vis-objs))
           wgts))))

;; set the state vector of the procedure-window
  (setf (state-vec wind) (make-array (length *step-names*)))
  (dotimes
      (i (length *step-names*))
    (setf (svref (state-vec wind) i) (nick-name (nth i (widgets wind)))))


;; set interruption state numbers according to kind, as encoded by task-id
;; For task 1, insert an interruption immediately preceding the PC step and 
;; some other random step,
;; For task 2, insert two interruptions at random steps, excluding immediately
;; preceding the PC step
;; For both, interruptions should not be before the first step.
    (labels
        ((ar-random-not (limit &optional (n 0))
           (do ((x (act-r-random limit) (act-r-random limit)))
               ((and (neq x n) (neq x 0))
                (return-from ar-random-not x)))))
      (case (task-id wind)
        (1 (setf (int-staten wind)
                 (vector
                  (ar-random-not (- (length *step-names*) 1))
                  (1- (length *step-names*)))))
        (2 (let
               ((first-int-pos (ar-random-not (- (length *step-names*) 1))))
             (setf (int-staten wind)
                   (vector
                    first-int-pos
                    (ar-random-not 
                         (- (length *step-names*) 1)
                         first-int-pos)))))
#|        ((or 3 4) (setf (int-staten wind)
                 (vector
                  (1- (length *step-names*))
                  nil))) |#
        )))

(defmethod finish-trial ((wind st-exp-window))
  (let ((curr-block (nth (cblock wind) (block-lst wind))))
    (incf (current-idx curr-block))
    (incf (completed-trials wind))
    (if (= (size curr-block) (current-idx curr-block))
      (finish-block wind curr-block)
      (schedule-event-relative 
         (iti wind)
         (lambda () 
           (progn
             (setf (current-trial wind)
                   (nth (current-idx curr-block) (trial-lst curr-block)))
             (setup-trial wind (current-trial wind))))))))

(defmethod finish-task ((wind procedure-window))
  (write-log wind)
  (finish-trial *exp*))

(defmethod state-check ((wind stock-trader) state-name &optional info)
  (declare (ignore info))
  (labels ((got-state-num (sn)
             (dotimes (i (length (state-vec wind)))
               (when
                   (eq sn (svref (state-vec wind) i))
                 (return-from got-state-num i)))))
    
    (let ((gsn (got-state-num state-name))
          (crct (if (eq (curr-state wind) state-name) 1 0)))
      (let ((st-act (make-instance 'st-action
                      :latency (round (start-stop-timer (timer wind)))
                      :expected (curr-state wind)
                      :got state-name
                      :got-num gsn
                      :correct crct
                      :pce (if (= (- (state-num wind) gsn) (1- (length (state-vec wind)))) 1 0)
                      :step-num (state-num wind)
                      :expected-got-diff (- gsn (state-num wind))
                      :trial-kind (task-id wind)
                      :interrupted (if (interruption wind) 1 0))))
        (push st-act (action-log wind))
        (case crct
          (1 (advance-state wind))
          (0 (proc-error wind)))))))

(defmethod advance-state ((wind stock-trader))
  (when (eq (state-num wind) (1- (length (state-vec wind))))
    (finish-task wind))
  (incf (state-num wind))
  (if 
      (or
       (eq (state-num wind) (svref (int-staten wind) 0))
       (eq (state-num wind) (svref (int-staten wind) 1)))
    (setf (interruption wind) t)
    (setf (interruption wind) nil))
  (when (interruption wind)
    (make-instance 'arith-int :mouse-pos (mouse-pos wind)))) 


; r31
(defmethod proc-error ((wind stock-trader))
;; get name of the PS chunk corresponding to the current state number
  (let
      ((ck (nth (state-num wind) *step-names*)))
;; mod the goal buffer chunk to reflect the current state's correct response
    (mod-buffer-chunk 'goal `(step ,ck))
    (mod-buffer-chunk 'imaginal `(step ,ck)) ; r40
;; add a reference to the correct step
    (push (mp-time-ms) (chunk-reference-list ck)))
;; call advance-state
  (advance-state wind))


(defmethod write-pa ((st-act st-action) &optional (strm t))
  (let ((out-lst 
         (list 
          (snum *exp*)
          (completed-trials *exp*)
          (trial-kind st-act)
          (step-num st-act)
          (got-num st-act)
          (expected-got-diff st-act)
          (interrupted st-act)
          (correct st-act)
          (pce st-act))))
    (terpri strm)
    (tab-output out-lst strm)
;; Tab-output writes a tab after every item, but reading an empty column into R is sort of annoying,
;; so write the last thing directly into the stream rather than through tab-output.
    (format strm "~S" (latency st-act))))

(defmethod write-events ((wind stock-trader) &optional (strm t))
    (dolist (p-act (reverse (action-log wind)))
      (write-pa p-act strm)))


;; Either this or delete write-block from virtual-experiment-window.lisp
(defmethod write-block ((wind stock-trader) (blk trial-block))
  nil)


;;;; ---------------------------------------------------------------------- ;;;;
;;;;   ACT-R Device Handler Methods
;;;; ---------------------------------------------------------------------- ;;;;

(defmethod build-vis-locs-for ((device procedure-window) vismod)
  (declare (ignore vismod))
  (labels ((wdgt-lst (lst)
             (if (null lst)
               nil
               (cons (vis-loc (car lst)) (wdgt-lst (cdr lst))))))
    (wdgt-lst (widgets device))))

(defmethod vis-loc-to-obj ((device procedure-window) vl)
  "Returns the vis-obj of the widget containing the vis-loc."
  (labels ((get-vis-obj (lst)
             (cond 
               ((null lst) nil)
               ((eq (vis-loc (car lst)) vl) (vis-obj (car lst)))
               (t (get-vis-obj (cdr lst))))))
  (get-vis-obj (widgets device))))
               

(defmethod device-move-cursor-to ((device procedure-window) loc) 
  (setf (mouse-pos device) loc))

(defmethod get-mouse-coordinates ((device procedure-window))
  (mouse-pos device))

(defmethod device-handle-click ((device procedure-window))
  (awhen (current-widget device (get-mouse-coordinates device)) 
         (progn
           (model-output "~%Model clicked ~A.~%" (nick-name it)) 
           (state-check device (nick-name it)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The Task Environment: The Arithmetical Interruption Task
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; the interruption task's virtual window
(defclass arith-int (procedure-window)
  ((widgets :accessor widgets :initarg :widgets :initform nil)
   (mouse-pos :accessor mouse-pos :initarg :mouse-pos :initform nil)
   (task-id :accessor task-id :initarg :task-id :initform 99))
  (:default-initargs
    :state-vec #(:sum)
    :start-time (mp-time)))

(defmethod initialize-instance :after ((wind arith-int) &key)
  "Initialize an instance of the arith-int device class. Make the visual-location and visual-object
chunks, encapsulate them in widgets, install the arith-int as ACT-R's device, and run the model."
  (let*
      ((vis-locs 
        (define-chunks-fct
            (let ((vl nil))
              (dotimes
                  (i 9 vl)
                (push
                 `(isa visual-location
                       kind text
                       color black
                       screen-x ,(+ 520 (* i 20))
                       screen-y 600
                       height 15
                       width 15)
                 vl))
            (dotimes
                  (i 5 (nreverse vl))
              (push
               `(isa visual-location
                     kind text
                     color black
                     screen-x ,(+ 520 (* i 40))
                     screen-y 620
                     height 15
                     width 15)
               vl)))))

       (addends
        (let (ads)
          (dotimes (i 5 ads)
            (push (act-r-random 10) ads))))
       
       (options
        (let (opts)
          (push (apply '+ addends) opts)
          (dotimes (i 3 (randomize-list opts))
            (push (act-r-random 50) opts))))

       (texts 
        `(,(nth 0 addends)
          +
          ,(nth 1 addends)
          +
          ,(nth 2 addends)
          +
          ,(nth 3 addends)
          +
          ,(nth 4 addends)
          =?
          ,(nth 0 options)
          ,(nth 1 options)
          ,(nth 2 options)
          ,(nth 3 options)))

       (vis-objs
        (define-chunks-fct
            (let ((vo nil))
              (dotimes
                  (i 14 (nreverse vo))
                (push
                 `(isa text 
                       screen-pos ,(nth i vis-locs)
                       value (string ,(nth i texts))
                       color black)
                 vo)))))

       (names '(add1 op1 add2 op2 add3 op3 add4 op4 add5 prompt opt1 opt2 opt3 opt4))

       (wgts (let ((w nil))
                (dotimes (i 14 (nreverse w))
                  (push
                   (make-instance 'widget 
                      :vwindow wind 
                      :nick-name (intern (string (nth i names)) "KEYWORD")
                      :vis-loc (nth i vis-locs) 
                      :vis-obj (nth i vis-objs))
                   w)))))
    (progn
      (setf (widgets wind) wgts)
      (install-device wind)
      (proc-display :clear t)
      (model-output "Begin interruption task.")

;; really just need to clear the visicon and replace the goal buffer chunk
      (schedule-event-relative 
       (int-dur *exp*)
       (lambda () 
         (progn
           (install-device (current-trial *exp*))
           (proc-display :clear t)
           (model-output "End interruption task.")
           (start-timing (timer (current-trial *exp*)))))))))



;;;; ---------------------------------------------------------------------- ;;;;
;;;;   Testing & Running 
;;;; ---------------------------------------------------------------------- ;;;;
; Stock :id 15, :k #(6 2 4 0 0)
; Phaser :id 9 :k #(0 0 0 10 10)
(defun run-model (&key (n 1) (id 15) (k #(6 2 4 0 0)) (m 0))
  "Do n runs of the model through the experiment with interruption duration of
id seconds and k trials of noWM-noINT, 
  noWM-PCINT, noWM-nonPCINT, noWM-PCINT, and WM-PCINT trials, respectively."
  (dotimes (i n)
    (progn
      (reset)
      (setf 
       *exp* 
       (make-instance 'st-exp-window :n-of-k k :snum i :int-dur id :m m))
      (format t "~%Run #: ~A~%" (snum *exp*))
      (run-experiment *exp*)
      (with-open-file 
          (strm 
           (out-path (current-trial *exp*))
           :direction :output 
           :if-exists nil
           :if-does-not-exist :create)
        (format strm "~A" *data-column-headings*))
      (run-until-condition (lambda () nil)))))


(defmethod finish-experiment :after ((wind virtual-experiment-window))
  (schedule-break-after-all :details "…the end."))

(defun show-int-staten ()
  (dolist (trl (trial-lst (car (block-lst *exp*))))
    (format t "~A~%" (int-staten trl))))





;;;;
;;;; Specialty Functions for the Model 
;;;;
(defun process-completed-subgoal ()
  (if (member (task-id (current-trial *exp*)) '(0 1 2))
    (when (member (state-num (current-trial *exp*)) '(0 4 8 9))
      (push (- (mp-time-ms) 500) (chunk-reference-list 'trial)))
    (when (member (state-num (current-trial *exp*)) '(0 4 7 9))
      (push (- (mp-time-ms) 500) (chunk-reference-list 'trial)))))


(defun check-for-int ()
  (when (eq 'arith-int (class-name (class-of (current-device))))
    (values
     (schedule-clear-buffer 'imaginal 0 :module 'imaginal)
     (schedule-clear-buffer 'visual 0 :module 'visual)
     (schedule-set-buffer-chunk 
      'goal
      (car (define-chunks-fct
               '((isa arith-int operator start))))
      0
      :module 'goal)
     (let (evt-lst)
       (dotimes (i 3)
         (push
          (schedule-module-request 
           'retrieval 
           (define-chunk-spec-fct
               '(isa episodic))
           (1+ i)
           :module 'declarative)
          evt-lst))
       evt-lst))))



;;;; ---------------------------------------------------------------------- ;;;;
;;;;   The Model
;;;; ---------------------------------------------------------------------- ;;;;

(defparameter *mas* 2.2)

(clear-all)

(define-model pce-59

  (sgp-fct 
   (list
    ;; model debugging & running
    :v nil :trace-detail 'low

    ;; central parameters
    :er t :esc t

    ;; declarative
;; :stock .3 :phaser-hi .3 :phaser-lo .9
    :ans .3
    :rt -99 
    :bll .5
    :mas *mas*
    :ol 4
;    :sact 'medium

    ;; episodic
    :boostq 4
    :boosti .05

;; :stock .95 :phaser-hi .8 :phaser-lo .3
    :imaginal-activation .8

    :do-not-harvest 'visual
    :do-not-harvest 'visual-location
    :do-not-harvest 'imaginal))

  (mapcar 
   'chunk-type-fct 
   '((stock-trade operator step)
     ((do-stock-trade (:include stock-trade)))
     ((scene-change (:include stock-trade)))
     ((resume (:include stock-trade)))
     (arith-int operator arg1 arg2)
     ((procedure-step (:include visual-location)))
     (episodic 
      "Episodic chunk that is created, encoded, and retrieved according to
           the Memory for Goals Hypothesis (Altmann & Trafton, 2002). Its
           goal slot stores a goal buffer chunk. It uses 
           gensym for the value of unique-name
           so that each episodic code is unique."
      context unique-name)
     (task-state step wm1 wm2 wm3)))



;; need visual-locations for the procedure-steps and the device
  (setf *vis-locs* 
        (add-dm-fct
            (let ((vl nil))
              (push
               `(isa visual-location
                     screen-x 50
                     screen-y 50
                     kind oval 
                     height 30 
                     width 50 
                     color blue)
               vl)
              (dotimes 
                  (j 2)
                (dotimes
                    (i 4)
                  (push
                   `(isa visual-location
                         screen-x ,(+ 100 (* 200 j))
                         screen-y ,(+ 150 (* i 100))
                         kind oval 
                         height 30 
                         width 50 
                         color blue)
                   vl)))
              (push
               `(isa visual-location
                     screen-x 350
                     screen-y 50
                     kind oval 
                     height 30 
                     width 50 
                     color blue)
               vl)
              (nreverse vl))))

  (add-dm-fct (let
                  ((cks 
                    `((start isa chunk)
                      (start-stock-trade-goal
                       isa do-stock-trade
                       step start
                       operator retrieve-ps) 
                      (trial isa procedure-step ; jig for starting a new trial
                             screen-x 50
                             screen-y 50
                             kind oval
                             color blue
                             height 30
                             width 50
                             value trial))))
                (dotimes
                    (i (length *step-names*) cks)
                  (push 
                   `(,(nth i *step-names*) 
                     isa procedure-step 
                     screen-x ,(chunk-slot-value-fct (nth i *vis-locs*) 'screen-x)
                     screen-y ,(chunk-slot-value-fct (nth i *vis-locs*) 'screen-y)
                     kind ,(chunk-slot-value-fct (nth i *vis-locs*) 'kind)
                     color ,(chunk-slot-value-fct (nth i *vis-locs*) 'color)
                     height ,(chunk-slot-value-fct (nth i *vis-locs*) 'height)
                     width ,(chunk-slot-value-fct (nth i *vis-locs*) 'width))
                   cks))))
  
;; set strengths of associations for the procedure-step chunks
;; reciprocal function of distance to succeeding step,
;; modulo number of steps, multiplied by :mas
  (add-sji-fct
   (let (sjis) 
     (push `(start ,(car *step-names*) ,*mas*) sjis)
     (push '(start start 0) sjis)
     (push '(trial trial 0) sjis)
     (dotimes
         (j (length *step-names*))
       (progn
         (dotimes
             (i (length *step-names*))
           (cond
            ((eq j i)
             (push `(,(nth j *step-names*) ,(nth i *step-names*) ,(* -1 *mas*)) sjis))            
            (t ;(< j i)
             (push `(,(nth j *step-names*) 
                     ,(nth i *step-names*) 
                     ,(* *mas* (/ 1 (- i j)))) sjis))))
;; trial's spreading activation
;;         (push `(,(nth j *step-names*) trial ,(* (expt *mas* -2) (/ 1 (- 10 j)))) sjis)
))
     sjis))


;; Assume the model is of trained behavior, and so PS chunks should have some references
  (sdp-fct 
   (let ((cks nil)
         (i 0)
         (cycles 4)
         (refs nil)
         (interval 90))
     (dolist
         (ck (cons 'trial *step-names*) cks)
       (push `(,ck :creation-time ,(* -1 cycles (+ 10 interval))) cks)
       (push
;; Trial needs four references per trial
        (if (eq ck 'trial)
          `(,ck :reference-list
                ,(dotimes
                     (j cycles refs)
                   (dolist
                       (k '(2 10 18))
                     (push (+ (* -1 100 cycles) (+ k (* interval j))) refs))))
          `(,ck :reference-list
                ,(dotimes
                     (j cycles refs)
                   (push (+ (* -1 100 cycles) (+ (* i 2) (* interval j))) refs))))
        cks)
       (incf i)
       (setf refs nil))))

  
  (start-hand-at-mouse)

  


;;;
;; Productions
;;;


;; Goal Resumption

(p resume-retrieve-episode
   =visual-location>
   	isa visual-location
	kind oval
        color blue
   =goal>
	isa scene-change
        operator scene-change
   ?retrieval>
	state free
==>
   +goal>
   	isa resume
	operator retrieving-episode
   +retrieval>
	isa episodic)

(p harvest-retrieved-episodic
   =goal>
   	isa stock-trade
	operator retrieving-episode
   =retrieval>
	isa episodic
        context =c
==>
   +imaginal> 
   	isa task-state
        step =c
   =goal>
        operator reinstating-context
)

(p reinstate-context
   =goal>
	isa stock-trade
        operator reinstating-context
   =imaginal>
	isa task-state
==>
   =goal>
	operator retrieve-ps
!eval! (when (eq (task-id (current-trial *exp*)) 4)
         (mod-buffer-chunk 'imaginal '(wm1 a wm2 b wm3 c)))
; !eval! (buffer-chunk imaginal)
)

(p retrieve-next-procedure-step
;; Do I want this to specifically be a do-stock-trade so that it's selected based on matching 
;; to goal chunk-type rather than competing with post-resumption-int-nav-heuristic on utility?
   =goal>
	isa stock-trade
        operator retrieve-ps
   ?episodic>
   	buffer empty ; r19
   ?retrieval>
	state free
==>
   =goal>
	operator pause
;        operator retrieving-ps
   +retrieval>
	isa procedure-step
; !eval! (buffer-chunk imaginal)
; !eval! (buffer-chunk goal)
!eval! (model-output 
        "Task state number (zero-indexed): ~A~%" 
        (state-num (current-trial *exp*)))
!eval! (process-completed-subgoal)
!eval! (unless 
           (eq 
            (state-num (current-device)) 
            (length (state-vec (current-device))))
         (schedule-event-relative
;; For each step the model pauses for median subject step completion time, 
;; then finishes that step
         (nth 
            (state-num (current-trial *exp*)) 
            (if (< (task-id (current-trial *exp*)) 3)
;; median financial task SCLs
              '(18 8 9.6 7.5 6 8.3 2.9 6.2 3.3 1) 
; Phaser's charge step depended upon waiting
; approximately 4.5 s for the charge meter to fill
; approx 10 s for shooting
              '(1 1 4.5 1 1 1 1 1 10 1)))
          (lambda ()
            (mod-chunk-fct 
             (no-output (car (buffer-chunk-fct '(goal))))
             '(operator retrieving-ps)))
          :module 'scheduling
          :details "Pause for task step latency"))
; !eval! (mp-show-queue)
)





;; Find
(p find-step-from-retrieved-ps
   =goal>
	isa stock-trade
	operator retrieving-ps
   =retrieval>
	isa procedure-step
        screen-x =x
        screen-y =y
        color =c
        kind =k
   =imaginal>  
	isa task-state
==>
   =goal>
	operator finding
        step =retrieval
   +visual-location> 
	isa visual-location
        screen-x =x
        screen-y =y
        color =c
        kind =k
   =imaginal>
	step =retrieval
; !eval! (buffer-chunk retrieval)
; !eval! (buffer-chunk goal)
)

;; Move
(p move-visual-attention-and-cursor
   "There's an oval, move visual-attention and the cursor to it."
   =goal>
	isa stock-trade
   	operator finding
   =visual-location>
   	isa visual-location
        color blue
        kind oval
   ?visual>
   	state free
   ?manual>
   	state free
==>
   =goal>
   	operator act
   +visual>
   	isa move-attention
   	screen-pos =visual-location
   +manual>
   	isa move-cursor
   	loc =visual-location
; !eval! (buffer-chunk retrieval)
; !eval! (buffer-chunk goal)
)


;; Perform the Step's Action
(p click-mouse
   =goal>
   	isa stock-trade
   	operator act
   =visual> 
	isa visual-object
        color blue
   ?manual>
   	state free
==>
   =goal>
   	operator acting
   +manual> 
	isa click-mouse
;   !eval! (schedule-break-relative 0)
;   !eval! (buffer-chunk goal)
;   !eval! (buffer-chunk imaginal)
)







(p encode-episodic
   =goal>
	isa stock-trade
	operator acting
   ?manual>
	state free
   ?episodic>
	buffer empty
   =imaginal>
   	isa task-state
        step =s
==>
   !bind! =uname (new-symbol "episodic")
   +episodic>
	isa episodic
        context =s
        unique-name =uname
   =goal>
	operator encoding-episode
; !eval! (buffer-chunk goal)
; !eval! (buffer-chunk imaginal)
)

(p episodic-encoded
   =goal>
   	isa stock-trade
	operator encoding-episode
   =episodic> 
	isa episodic
   ?retrieval>
	buffer empty
   ?retrieval>
	state free
==>
   -episodic>
   =goal>
	operator retrieve-ps
!eval! (check-for-int)
!eval! (when 
           (eq (state-num (current-device)) (length (state-vec (current-device))))
          (schedule-mod-buffer-chunk 
           'goal 
           '(operator wait-for-next-trial) 
           0 
           :module 'goal))
)


	



(p handle-scene-change
   ?visual>
	scene-change t
   ?manual>
	state free
   ?episodic>
   	buffer empty
   ?goal>
	buffer empty
==>
   +visual>
	isa clear
   +visual-location>
	isa visual-location
   +goal> 
	isa scene-change
        operator scene-change)






;;;; Interruption Task

(p start-int
   =visual-location>
	isa visual-location
        color black
        kind text
   =goal>
	isa scene-change
        operator scene-change
==>
   +goal>
	isa arith-int
        operator start
)

(p int1
   =goal>
	isa arith-int
        operator start
   =visual-location>
	isa visual-location
        kind text
        color black
   ?visual>
	state free
==>
   =goal>
	operator attend-arg1
   +visual>
	isa move-attention
        screen-pos =visual-location)

(p int2
   =goal>
	isa arith-int
        operator attend-arg1
   =visual>
	isa text
        value =val
==>
   =goal>
	arg1 =val
        operator find-arg2
   +visual-location>
	isa visual-location
        kind text
        color black)

(p int3
   =goal>
	isa arith-int
        arg1 =add1
        operator find-arg2
   =visual-location>
	isa visual-location
        kind text
        color black
   ?visual>
	state free
==>
   =goal>
	operator attend-arg2
   +visual>
	isa move-attention
        screen-pos =visual-location)

(p int4
   =goal>
	isa arith-int
        arg1 =add1
        operator attend-arg2
   =visual>
	isa text
        value =val
==>
   =goal>
	arg2 =val
        operator wait)

(p notice-scene-change-finish-int
   ?visual>
	scene-change t
   =goal>
	isa arith-int
==>
   -goal>)

)




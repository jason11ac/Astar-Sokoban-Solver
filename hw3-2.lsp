;
; CS161 Hw3: Sokoban
;
; *********************
;    READ THIS FIRST
; *********************
;
; All functions that you need to modify are marked with 'EXERCISE' in their header comments.
; Do not modify a-star.lsp.
; This file also contains many helper functions. You may call any of them in your functions.
;
; *Warning*: The provided A* code only supports the maximum cost of 4999 for any node.
; That is f(n)=g(n)+h(n) < 5000. So, be careful when you write your heuristic functions.
; Do not make them return anything too large.
;
; For Allegro Common Lisp users: The free version of Allegro puts a limit on memory.
; So, it may crash on some hard sokoban problems and there is no easy fix (unless you buy
; Allegro).
; Of course, other versions of Lisp may also crash if the problem is too hard, but the amount
; of memory available will be relatively more relaxed.
; Improving the quality of the heuristic will mitigate this problem, as it will allow A* to
; solve hard problems with fewer node expansions.
;
; In either case, this limitation should not significantly affect your grade.
;
; Remember that most functions are not graded on efficiency (only correctness).
; Efficiency can only influence your heuristic performance in the competition (which will
; affect your score).
;
;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; General utility functions
; They are not necessary for this homework.
; Use/modify them for your own convenience.
;

;
; For reloading modified code.
; I found this easier than typing (load "filename") every time.
;
(defun reload()
  (load "hw3.lsp")
  )

;
; For loading a-star.lsp.
;
(defun load-a-star()
  (load "a-star.lsp"))

;
; Reloads hw3.lsp and a-star.lsp
;
(defun reload-all()
  (reload)
  (load-a-star)
  )

;
; A shortcut function.
; goal-test and next-states stay the same throughout the assignment.
; So, you can just call (sokoban <init-state> #'<heuristic-name>).
;
;
(defun sokoban (s h)
  (a* s #'goal-test #'next-states h)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; end general utility functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; We now begin actual Sokoban code
;

; Define some global variables
(setq blank 0)
(setq wall 1)
(setq box 2)
(setq keeper 3)
(setq star 4)
(setq boxstar 5)
(setq keeperstar 6)

; Some helper functions for checking the content of a square
(defun isBlank (v)
  (= v blank)
  )

(defun isWall (v)
  (= v wall)
  )

(defun isBox (v)
  (= v box)
  )

(defun isKeeper (v)
  (= v keeper)
  )

(defun isStar (v)
  (= v star)
  )

(defun isBoxStar (v)
  (= v boxstar)
  )

(defun isKeeperStar (v)
  (= v keeperstar)
  )

;
; Helper function of getKeeperPosition
;
(defun getKeeperColumn (r col)
  (cond ((null r) nil)
	(t (if (or (isKeeper (car r)) (isKeeperStar (car r)))
	       col
	     (getKeeperColumn (cdr r) (+ col 1))
	     );end if
	   );end t
	);end cond
  )

;
; getKeeperPosition (s firstRow)
; Returns a list indicating the position of the keeper (c r).
;
; Assumes that the keeper is in row >= firstRow.
; The top row is the zeroth row.
; The first (right) column is the zeroth column.
;
(defun getKeeperPosition (s row)
  (cond ((null s) nil)
	(t (let ((x (getKeeperColumn (car s) 0)))
	     (if x
		 ;keeper is in this row
		 (list x row)
		 ;otherwise move on
		 (getKeeperPosition (cdr s) (+ row 1))
		 );end if
	       );end let
	 );end t
	);end cond
  );end defun

;
; cleanUpList (l)
; returns l with any NIL element removed.
; For example, if l is '(1 2 NIL 3 NIL), returns '(1 2 3).
;
(defun cleanUpList (L)
  (cond ((null L) nil)
	(t (let ((cur (car L))
		 (res (cleanUpList (cdr L)))
		 )
	     (if cur
		 (cons cur res)
		  res
		 )
	     );end let
	   );end t
	);end cond
  );end

; EXERCISE: Modify this function to return true (t)
; if and only if s is a goal state of a Sokoban game.
; (no box is on a non-goal square)
;
; Currently, it always returns NIL. If A* is called with
; this function as the goal testing function, A* will never
; terminate until the whole search space is exhausted.
;
; Returns true (t) if and only if s is a goal state of a Sokoban game
;
; goal-test uses recursion to check the top left corner square of a passed in state s for a box
; If the top left corner (first (first s)) is not a box, then it passed everything but the top left
; corner to goal-test again so that the whole state is checked for boxes recursively.
; This happens until the function finds a box (2) or the state gets reduced to null, in which T is returned.
(defun goal-test (s)
  (cond ((null s) T)
        ((isBox (first (first s))) nil)
        (t (goal-test (cleanUpList (cons (rest (first s)) (rest s)))))
  )
);end defun



; Returns the value of the r c square that is passed (0 through 6)
;
; get-square first checks to see if the c and r parameters are out of the bounds of s. If so, return a wall (1)
; If c and r are valid, first nthcdr is called with r to get a set of rows that starts with our row of interest and ends with
; the last row. Then first is called to get our row of interest by itself.
; Then nthcdr is called with c to get a list of values that starts with our square of interest and ends with the last value.
; first is then called on this to get our square of interest by itself.
(defun get-square (s c r)
  (cond ((or (or (< r 0) (< c 0)) (> r (- (length s) 1)) (> c (- (length (first s)) 1))) 1) ;Out of bounds means output 1 for wall
        (t (first (nthcdr c (first (nthcdr r s)))))
  )
)



; Returns a state where the c and r square of s is set to v
;
; set-square breaks up the given state (s) by rows and then by columns so that the given square (c, r) is
; isolated. Then it appends the columns of row r to both sides of (list v) to get our new row of interest.
; Then it appends the rows before and after our new row of interest to complete the new state.
(defun set-square (s c r v)
  (let* ((lengS (length s)) ;6
        (lengRow (length (first s))) ;5
        (end (nthcdr (+ r 1) s))    ; After our row of interest
        (row (first (nthcdr r s)))     ; Row of interest
        (start (butlast s (- lengS r)))  ; Before our row of interest
        (rowEnd (nthcdr (+ c 1) row))
        (rowStart (butlast row (- lengRow c)))
        (newRow (append rowStart (list v) rowEnd)))
        (append start (list newRow) end)
    )

)

; EXERCISE: Modify this function to return the list of
; sucessor states of s.
;
; This is the top-level next-states (successor) function.
; Some skeleton code is provided below.
; You may delete them totally, depending on your approach.
;
; If you want to use it, you will need to set 'result' to be
; the set of states after moving the keeper in each of the 4 directions.
; A pseudo-code for this is:
;
; ...
; (result (list (try-move s UP) (try-move s DOWN) (try-move s LEFT) (try-move s RIGHT)))
; ...
;
; You will need to define the function try-move and decide how to represent UP,DOWN,LEFT,RIGHT.
; Any NIL result returned from try-move can be removed by cleanUpList.
;
;

; Returns a list of sucessor states of s
;
; next-states first saves the column (x) and row (y) of the keeper in the given state (s)
; Then it creates a list of the four possible next moves, which are found using try-move.
; Each call to try move is passed the keeper's position and a given direction (up, down, left, right)
; Once result is set to the set of moves, cleanUpList is called to remove any non-valid moves (nil)
(defun next-states (s)
  (let* ((pos (getKeeperPosition s 0))
	 (x (car pos)) ; column (x)
	 (y (cadr pos)) ; row (y)
	 ;x and y are now the coordinate of the keeper in s.
   ;                  up                down              left              right
	 (result (list (try-move s x y 0) (try-move s x y 1) (try-move s x y 2) (try-move s x y 3)))
   )
    (cleanUpList result);end
   );end let
  );


; Returns a new state where the keeper made a move that does NOT involve a box or boxStar
;
; make-nobox-move first gets the values of the squares in each direction of the keeper.
; Then depending on whether the keeper is standing on a star (goal) or not, or is moving over a star or not,
; it returns a new state in which the keeper made one move with no box involved.
; This function returns this new state using nested set-sqaures that set each changed square accordingly.
(defun make-nobox-move (s x y d)
  (let ((keep (get-square s x y))
        (keepUp (get-square s x (- y 1)))
        (keepDown (get-square s x (+ y 1)))
        (keepLeft (get-square s (- x 1) y))
        (keepRight (get-square s (+ x 1) y)))
        ;
        (cond ((= keep 3)
                (cond ((and (= d 0) (= keepUp 0)) (set-square (set-square s x (- y 1) keeper) x y blank)) ;keeper steps off blank to blank
                  ((and (= d 1) (= keepDown 0)) (set-square (set-square s x (+ y 1) keeper) x y blank)) ;keeper steps off blank to blank
                  ((and (= d 2) (= keepLeft 0)) (set-square (set-square s (- x 1) y keeper) x y blank)) ;keeper steps off blank to blank
                  ((and (= d 3) (= keepRight 0)) (set-square (set-square s (+ x 1) y keeper) x y blank)) ;keeper steps off blank to blank
                  ;
                  ((and (= d 0) (= keepUp 4)) (set-square (set-square s x (- y 1) keeperStar) x y blank)) ;keeper steps off blank to star
                  ((and (= d 1) (= keepDown 4)) (set-square (set-square s x (+ y 1) keeperStar) x y blank)) ;keeper steps off blank to star
                  ((and (= d 2) (= keepLeft 4)) (set-square (set-square s (- x 1) y keeperStar) x y blank)) ;keeper steps off blank to star
                  ((and (= d 3) (= keepRight 4)) (set-square (set-square s (+ x 1) y keeperStar) x y blank)))) ;keeper steps off blank to star
              ((= keep 6)
                (cond ((and (= d 0) (= keepUp 0)) (set-square (set-square s x (- y 1) keeper) x y star)) ;keeper steps off star to blank
                  ((and (= d 1) (= keepDown 0)) (set-square (set-square s x (+ y 1) keeper) x y star)) ;keeper steps off star to blank
                  ((and (= d 2) (= keepLeft 0)) (set-square (set-square s (- x 1) y keeper) x y star)) ;keeper steps off star to blank
                  ((and (= d 3) (= keepRight 0)) (set-square (set-square s (+ x 1) y keeper) x y star)) ;keeper steps off star to blank
                  ;
                  ((and (= d 0) (= keepUp 0)) (set-square (set-square s x (- y 1) keeperStar) x y star)) ;keeper steps off star to star
                  ((and (= d 1) (= keepDown 0)) (set-square (set-square s x (+ y 1) keeperStar) x y star)) ;keeper steps off star to star
                  ((and (= d 2) (= keepLeft 0)) (set-square (set-square s (- x 1) y keeperStar) x y star)) ;keeper steps off star to star
                  ((and (= d 3) (= keepRight 0)) (set-square (set-square s (+ x 1) y keeperStar) x y star)))) ;keeper steps off star to star
    )
  )
)


; Returns a new state where the keeper made a move that does involve a box or boxStar
;
; make-box-move first gets the values of the squares in each direction of the keeper. Then it saves the
; values that are two moves away from the keeper in each direction so that it can be determined if a box can
; be moved or not. Then because a move with a box involves 3 spaces, each combination of 3 spaces is
; checked for a given direction (d). If a combination of keeper, stars and boxes is valid for a move, then 3 nested
; set-squares are used to change all 3 squares of the old state to a new state that is returned.
(defun make-box-move (s x y d)
  (let ((sqCenter (get-square s x y))
        ;
        (sqUp (get-square s x (- y 1)))
        (sqDown (get-square s x (+ y 1)))
        (sqLeft (get-square s (- x 1) y))
        (sqRight (get-square s (+ x 1) y))
        ;
        (sqUp2 (get-square s x (- y 2)))
        (sqDown2 (get-square s x (+ y 2)))
        (sqLeft2 (get-square s (- x 2) y))
        (sqRight2 (get-square s (+ x 2) y)))
        ;
          ;UP
    (cond ((and (= d 0) (= sqUp 2) (= sqCenter 3) (= sqUp2 4))
              (set-square (set-square (set-square s x (- y 2) boxstar) x (- y 1) keeper) x y blank))
                        ; keeper -> box -> blank
          ((and (= d 0) (= sqUp 2) (= sqCenter 3) (= sqUp2 0))
              (set-square (set-square (set-square s x (- y 2) box) x (- y 1) keeper) x y blank))
                        ; keeperstar -> box -> blank
          ((and (= d 0) (= sqUp 2) (= sqCenter 6) (= sqUp2 0))
              (set-square (set-square (set-square s x (- y 2) box) x (- y 1) keeper) x y star))
                        ; keeperstar -> box -> star
          ((and (= d 0) (= sqUp 2) (= sqCenter 6) (= sqUp2 4))
              (set-square (set-square (set-square s x (- y 2) boxstar) x (- y 1) keeper) x y star))
                        ; keeper -> boxStar -> star
          ((and (= d 0) (= sqUp 5) (= sqCenter 3) (= sqUp2 4))
                (set-square (set-square (set-square s x (- y 2) boxstar) x (- y 1) keeperStar) x y blank))
                        ; keeper -> boxStar -> blank
          ((and (= d 0) (= sqUp 5) (= sqCenter 3) (= sqUp2 0))
                (set-square (set-square (set-square s x (- y 2) box) x (- y 1) keeperStar) x y blank))
                        ; keeperstar -> boxStar -> star
          ((and (= d 0) (= sqUp 5) (= sqCenter 6) (= sqUp2 4))
                (set-square (set-square (set-square s x (- y 2) boxStar) x (- y 1) keeperStar) x y star))
                        ; keeperstar -> boxStar -> blank
          ((and (= d 0) (= sqUp 5) (= sqCenter 6) (= sqUp2 0))
                (set-square (set-square (set-square s x (- y 2) box) x (- y 1) keeperStar) x y star))


          ; DOWN
          ((and (= d 1) (= sqDown 2) (= sqCenter 3) (= sqDown2 4))
                (set-square (set-square (set-square s x (+ y 2) boxstar) x (+ y 1) keeper) x y blank))
                          ; keeper -> box -> blank
          ((and (= d 1) (= sqDown 2) (= sqCenter 3) (= sqDown2 0))
                (set-square (set-square (set-square s x (+ y 2) box) x (+ y 1) keeper) x y blank))
                          ; keeperstar -> box -> blank
          ((and (= d 1) (= sqDown 2) (= sqCenter 6) (= sqDown2 0))
                (set-square (set-square (set-square s x (+ y 2) box) x (+ y 1) keeper) x y star))
                          ; keeperstar -> box -> star
          ((and (= d 1) (= sqDown 2) (= sqCenter 6) (= sqDown2 4))
                (set-square (set-square (set-square s x (+ y 2) boxstar) x (+ y 1) keeper) x y star))
                          ; keeper -> boxStar -> star
          ((and (= d 1) (= sqDown 5) (= sqCenter 3) (= sqDown2 4))
                (set-square (set-square (set-square s x (+ y 2) boxstar) x (+ y 1) keeperStar) x y blank))
                          ; keeper -> boxStar -> blank
          ((and (= d 1) (= sqDown 5) (= sqCenter 3) (= sqDown2 0))
                (set-square (set-square (set-square s x (+ y 2) box) x (+ y 1) keeperStar) x y blank))
                          ; keeperstar -> boxStar -> star
          ((and (= d 1) (= sqDown 5) (= sqCenter 6) (= sqDown2 4))
                (set-square (set-square (set-square s x (+ y 2) boxStar) x (+ y 1) keeperStar) x y star))
                          ; keeperstar -> boxStar -> blank
          ((and (= d 1) (= sqDown 5) (= sqCenter 6) (= sqDown2 0))
                (set-square (set-square (set-square s x (+ y 2) box) x (+ y 1) keeperStar) x y star))


          ; LEFT
          ((and (= d 2) (= sqLeft 2) (= sqCenter 3) (= sqLeft2 4))
                (set-square (set-square (set-square s (- x 2) y boxstar) (- x 1) y keeper) x y blank))
                            ; keeper -> box -> blank
          ((and (= d 2) (= sqLeft 2) (= sqCenter 3) (= sqLeft2 0))
                (set-square (set-square (set-square s (- x 2) y box) (- x 1) y keeper) x y blank))
                            ; keeperstar -> box -> blank
          ((and (= d 2) (= sqLeft 2) (= sqCenter 6) (= sqLeft2 0))
                (set-square (set-square (set-square s (- x 2) y box) (- x 1) y keeper) x y star))
                            ; keeperstar -> box -> star
          ((and (= d 2) (= sqLeft 2) (= sqCenter 6) (= sqLeft2 4))
                (set-square (set-square (set-square s (- x 2) y boxstar) (- x 1) y keeper) x y star))
                            ; keeper -> boxStar -> star
          ((and (= d 2) (= sqLeft 5) (= sqCenter 3) (= sqLeft2 4))
                (set-square (set-square (set-square s (- x 2) y boxstar) (- x 1) y keeperStar) x y blank))
                            ; keeper -> boxStar -> blank
          ((and (= d 2) (= sqLeft 5) (= sqCenter 3) (= sqLeft2 0))
                (set-square (set-square (set-square s (- x 2) y box) (- x 1) y keeperStar) x y blank))
                            ; keeperstar -> boxStar -> star
          ((and (= d 2) (= sqLeft 5) (= sqCenter 6) (= sqLeft2 4))
                (set-square (set-square (set-square s (- x 2) y boxStar) (- x 1) y keeperStar) x y star))
                            ; keeperstar -> boxStar -> blank
          ((and (= d 2) (= sqLeft 5) (= sqCenter 6) (= sqLeft2 0))
                (set-square (set-square (set-square s (- x 2) y box) (- x 1) y keeperStar) x y star))


          ; RIGHT
          ((and (= d 3) (= sqRight 2) (= sqCenter 3) (= sqRight2 4))
                (set-square (set-square (set-square s (+ x 2) y boxstar) (+ x 1) y keeper) x y blank))
                                  ; keeper -> box -> blank
          ((and (= d 3) (= sqRight 2) (= sqCenter 3) (= sqRight2 0))
                (set-square (set-square (set-square s (+ x 2) y box) (+ x 1) y keeper) x y blank))
                                  ; keeperstar -> box -> blank
          ((and (= d 3) (= sqRight 2) (= sqCenter 6) (= sqRight2 0))
                (set-square (set-square (set-square s (+ x 2) y box) (+ x 1) y keeper) x y star))
                                  ; keeperstar -> box -> star
          ((and (= d 3) (= sqRight 2) (= sqCenter 6) (= sqRight2 4))
                (set-square (set-square (set-square s (+ x 2) y boxstar) (+ x 1) y keeper) x y star))
                                  ; keeper -> boxStar -> star
          ((and (= d 3) (= sqRight 5) (= sqCenter 3) (= sqRight2 4))
                (set-square (set-square (set-square s (+ x 2) y boxstar) (+ x 1) y keeperStar) x y blank))
                                  ; keeper -> boxStar -> blank
          ((and (= d 3) (= sqRight 5) (= sqCenter 3) (= sqRight2 0))
                (set-square (set-square (set-square s (+ x 2) y box) (+ x 1) y keeperStar) x y blank))
                                  ; keeperstar -> boxStar -> star
          ((and (= d 3) (= sqRight 5) (= sqCenter 6) (= sqRight2 4))
                (set-square (set-square (set-square s (+ x 2) y boxStar) (+ x 1) y keeperStar) x y star))
                                  ; keeperstar -> boxStar -> blank
          ((and (= d 3) (= sqRight 5) (= sqCenter 6) (= sqRight2 0))
                (set-square (set-square (set-square s (+ x 2) y box) (+ x 1) y keeperStar) x y star))
      )
  )
)


; Returns a new state if a given move is valid and returns nil otherwise
;
; try-move takes a state, keeper position and direction and returns a new state if the move is doable,
; and returns nil if it is not. First it checks to see if the move is into a wall using get-square, cause
; then just return nil. If not into a wall, try-move either calls make-nobox-move if a move does NOT involve
; a box or boxStar, or make-box-move if a move does involve a box or boxStar. This test is done using a cond
; statement.
(defun try-move (s x y d)
        ; Moving into wall
  (cond ((and (= d 2) (= (get-square s (- x 1) y) 1)) nil)
        ((and (= d 3) (= (get-square s (+ x 1) y) 1)) nil)
        ((and (= d 0) (= (get-square s x (- y 1)) 1)) nil)
        ((and (= d 1) (= (get-square s x (+ y 1)) 1)) nil)
        ; move with no box involved
        ((and (= d 2) (or (= (get-square s (- x 1) y) 0) (= (get-square s (- x 1) y) 4))) (make-nobox-move s x y 2))
        ((and (= d 3) (or (= (get-square s (+ x 1) y) 0) (= (get-square s (+ x 1) y) 4))) (make-nobox-move s x y 3))
        ((and (= d 0) (or (= (get-square s x (- y 1)) 0) (= (get-square s x (- y 1)) 4))) (make-nobox-move s x y 0))
        ((and (= d 1) (or (= (get-square s x (+ y 1)) 0) (= (get-square s x (+ y 1)) 4))) (make-nobox-move s x y 1))
        ; move with box involved
        (t (make-box-move s x y d))
  )
)






; EXERCISE: Modify this function to compute the trivial
; admissible heuristic.
;
; Trivial admissible heuristic that always returns 0
(defun h0 (s)
  0
  )

; EXERCISE: Modify this function to compute the
; number of misplaced boxes in s.
;
; Yes, h1 is admissible because it will take at least one move per box to move the boxes over a goal, giving us a goal state.
; Therefore, counting each non-goal box will give us a lower bound on the number of moves until a goal state.
; Moving each box has no effect on other boxes in the map and when all boxes are on goals, h1(s) = 0
(defun h1 (s)
  (cond ((null s) 0)
        (t (+ (count box (first s)) (h1 (rest s))))
  )
)



; EXERCISE: Change the name of this function to h<UID> where
; <UID> is your actual student ID number. Then, modify this
; function to compute an admissible heuristic value of s.
;
; This function will be entered in the competition.
; Objective: make A* solve problems as fast as possible.
; The Lisp 'time' function can be used to measure the
; running time of a function call.
;

; HELPER FUNCTIONS FOR h504487052

; Helper function for getBoxPosition
; Uses recursion to return a column of r if that column contains a box
; Based off of getKeeperColumn
(defun getBoxColumn (r col)
  (cond ((null r) nil)
	(t (if (isBox (car r))
	       col
	     (getBoxColumn (cdr r) (+ col 1))
	     );end if
	   );end t
	);end cond
)


; Returns a list indicating the position of the first box found (c r).
;
; Assumes that the box of choice is in row >= firstRow.
; The top row is the zeroth row.
; The first (right) column is the zeroth column.
; Based off of getKeeperPosition
(defun getBoxPosition (s row)
  (cond ((null s) nil)
	(t (let ((x (getBoxColumn (car s) 0)))
	     (if x
		 ;box is in this row
		 (list x row)
		 ;otherwise move on
		 (getBoxPosition (cdr s) (+ row 1))
		 );end if
	       );end let
	 );end t
	);end cond
  );end defun


; Helper function for getStarPosition
; Uses recursion to return a column of r if that column contains a star
; Based off of getKeeperColumn
(defun getStarColumn (r col)
  (cond ((null r) nil)
  (t (if (isStar (car r))
  	     col
  	   (getStarColumn (cdr r) (+ col 1))
  	   );end if
  	 );end t
  );end cond
)


; Returns a list indicating the position of the first star found (c r).
;
; Assumes that the star of choice is in row >= firstRow.
; The top row is the zeroth row.
; The first (right) column is the zeroth column.
; Based off of getKeeperPosition
(defun getStarPosition (s row)
  (cond ((null s) nil)
  (t (let ((x (getStarColumn (car s) 0)))
  	   (if x
  	 ;star is in this row
  	 (list x row)
  	 ;otherwise move on
  	 (getStarPosition (cdr s) (+ row 1))
  	 );end if
  	     );end let
  );end t
  );end cond
);end defun


; Returns a star position (c, r) if getStarPosition does not return null
; If it getStarPosition returns null, return (0)
(defun firstStarFunc (s r)
  (cond ((null (getStarPosition s r)) (list 0))
        (t (getStarPosition s r))
  )
)

; Returns the difference of car of fir and sec. If null, return 0 instead.
; Used to calculate the distance between two square coordinates (c, r)
(defun c (fir sec)
  (cond ((null (- (car fir) (car sec))) 0)
        (t (- (car fir) (car sec)))
  )
)

; Returns the difference of car cdr of fir and sec. If null, return 0 instead.
; Used to calculate the distance between two square coordinates (c, r)
(defun cc (fir sec)
  (cond ((null (- (car (cdr fir)) (car (cdr sec)))) 0)
        (t (- (car (cdr fir)) (car (cdr sec))))
  )
)


; Create a move efficient heuristic than h1 for A* search
;
; My goal with this heuristic was to:
; 1. Search the state (s) for the first found box
; 2. Search the area before and after the first box to find the closest star to this first box on either side of the box
; 3. Compare the distances from the box to both stars, take the shortest of these distances.
; 4. Add this shortest distance to the (- (value returned by h1) 1) for this state.
;
; This would give us a admissible heuristic that dominates h1(s), as instead of just adding 1 for this first box (like in h1), it would
; find the actual manhattan distance from the box to the closest star, making A* more efficient. Obviously finding the manhattan distance
; for each box to it's closest star would be more efficient, but finding one would definitely be improved over h1.
;
; My heuristic did not work though because you are not allowed to let a variable = nil in lisp. This is the error I keep getting when
; running my heuristic. (*** - -: NIL is not a number) This happens when a state (s) is passed in where there is no star or box.
(defun h504487052 (s)
  (let* ((boxNumber (- (h1 s) 1))
        ;
        (firstBox (getBoxPosition s 0)) ; (2, 2)
        (row (car (cdr firstBox)))
        (firstStar (firstStarFunc s 0)) ; (4, 5)
        (secondStar (firstStarFunc s row))
        ;
        (val1 (c firstBox firstStar))
        (val2 (cc firstBox firstStar))
        ;
        (val3 (c firstBox secondStar))
        (val4 (cc firstBox secondStar))
        ;
        (distance1 (sqrt (+ (* val1 val1) (* val2 val2))))
        (distance2 (sqrt (+ (* val3 val3) (* val4 val4)))))


        (cond ((< distance1 distance2) (floor (+ boxNumber distance1)))
               (t (floor (+ boxNumber distance2))))
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
 | Some predefined problems.
 | Each problem can be visualized by calling (printstate <problem>). For example, (printstate p1).
 | Problems are roughly ordered by their difficulties.
 | For most problems, we also privide 2 additional number per problem:
 |    1) # of nodes expanded by A* using our next-states and h0 heuristic.
 |    2) the depth of the optimal solution.
 | These numbers are located at the comments of the problems. For example, the first problem below
 | was solved by 80 nodes expansion of A* and its optimal solution depth is 7.
 |
 | Your implementation may not result in the same number of nodes expanded, but it should probably
 | give something in the same ballpark. As for the solution depth, any admissible heuristic must
 | make A* return an optimal solution. So, the depths of the optimal solutions provided could be used
 | for checking whether your heuristic is admissible.
 |
 | Warning: some problems toward the end are quite hard and could be impossible to solve without a good heuristic!
 |
 |#

;(80,7)
(setq p1 '((1 1 1 1 1 1)
	   (1 0 3 0 0 1)
	   (1 0 2 0 0 1)
	   (1 1 0 1 1 1)
	   (1 0 0 0 0 1)
	   (1 0 0 0 4 1)
	   (1 1 1 1 1 1)))

;(110,10)
(setq p2 '((1 1 1 1 1 1 1)
	   (1 0 0 0 0 0 1)
	   (1 0 0 0 0 0 1)
	   (1 0 0 2 1 4 1)
	   (1 3 0 0 1 0 1)
	   (1 1 1 1 1 1 1)))

;(211,12)
(setq p3 '((1 1 1 1 1 1 1 1 1)
	   (1 0 0 0 1 0 0 0 1)
	   (1 0 0 0 2 0 3 4 1)
	   (1 0 0 0 1 0 0 0 1)
	   (1 0 0 0 1 0 0 0 1)
	   (1 1 1 1 1 1 1 1 1)))

;(300,13)
(setq p4 '((1 1 1 1 1 1 1)
	   (0 0 0 0 0 1 4)
	   (0 0 0 0 0 0 0)
	   (0 0 1 1 1 0 0)
	   (0 0 1 0 0 0 0)
	   (0 2 1 0 0 0 0)
	   (0 3 1 0 0 0 0)))

;(551,10)
(setq p5 '((1 1 1 1 1 1)
	   (1 1 0 0 1 1)
	   (1 0 0 0 0 1)
	   (1 4 2 2 4 1)
	   (1 0 0 0 0 1)
	   (1 1 3 1 1 1)
	   (1 1 1 1 1 1)))

;(722,12)
(setq p6 '((1 1 1 1 1 1 1 1)
	   (1 0 0 0 0 0 4 1)
	   (1 0 0 0 2 2 3 1)
	   (1 0 0 1 0 0 4 1)
	   (1 1 1 1 1 1 1 1)))

;(1738,50)
(setq p7 '((1 1 1 1 1 1 1 1 1 1)
	   (0 0 1 1 1 1 0 0 0 3)
	   (0 0 0 0 0 1 0 0 0 0)
	   (0 0 0 0 0 1 0 0 1 0)
	   (0 0 1 0 0 1 0 0 1 0)
	   (0 2 1 0 0 0 0 0 1 0)
	   (0 0 1 0 0 0 0 0 1 4)))

;(1763,22)
(setq p8 '((1 1 1 1 1 1)
	   (1 4 0 0 4 1)
	   (1 0 2 2 0 1)
	   (1 2 0 1 0 1)
	   (1 3 0 0 4 1)
	   (1 1 1 1 1 1)))

;(1806,41)
(setq p9 '((1 1 1 1 1 1 1 1 1)
	   (1 1 1 0 0 1 1 1 1)
	   (1 0 0 0 0 0 2 0 1)
	   (1 0 1 0 0 1 2 0 1)
	   (1 0 4 0 4 1 3 0 1)
	   (1 1 1 1 1 1 1 1 1)))

;(10082,51)
(setq p10 '((1 1 1 1 1 0 0)
	    (1 0 0 0 1 1 0)
	    (1 3 2 0 0 1 1)
	    (1 1 0 2 0 0 1)
	    (0 1 1 0 2 0 1)
	    (0 0 1 1 0 0 1)
	    (0 0 0 1 1 4 1)
	    (0 0 0 0 1 4 1)
	    (0 0 0 0 1 4 1)
	    (0 0 0 0 1 1 1)))

;(16517,48)
(setq p11 '((1 1 1 1 1 1 1)
	    (1 4 0 0 0 4 1)
	    (1 0 2 2 1 0 1)
	    (1 0 2 0 1 3 1)
	    (1 1 2 0 1 0 1)
	    (1 4 0 0 4 0 1)
	    (1 1 1 1 1 1 1)))

;(22035,38)
(setq p12 '((0 0 0 0 1 1 1 1 1 0 0 0)
	    (1 1 1 1 1 0 0 0 1 1 1 1)
	    (1 0 0 0 2 0 0 0 0 0 0 1)
	    (1 3 0 0 0 0 0 0 0 0 0 1)
	    (1 0 0 0 2 1 1 1 0 0 0 1)
	    (1 0 0 0 0 1 0 1 4 0 4 1)
	    (1 1 1 1 1 1 0 1 1 1 1 1)))

;(26905,28)
(setq p13 '((1 1 1 1 1 1 1 1 1 1)
	    (1 4 0 0 0 0 0 2 0 1)
	    (1 0 2 0 0 0 0 0 4 1)
	    (1 0 3 0 0 0 0 0 2 1)
	    (1 0 0 0 0 0 0 0 0 1)
	    (1 0 0 0 0 0 0 0 4 1)
	    (1 1 1 1 1 1 1 1 1 1)))

;(41715,53)
(setq p14 '((0 0 1 0 0 0 0)
	    (0 2 1 4 0 0 0)
	    (0 2 0 4 0 0 0)
	    (3 2 1 1 1 0 0)
	    (0 0 1 4 0 0 0)))

;(48695,44)
(setq p15 '((1 1 1 1 1 1 1)
	    (1 0 0 0 0 0 1)
	    (1 0 0 2 2 0 1)
	    (1 0 2 0 2 3 1)
	    (1 4 4 1 1 1 1)
	    (1 4 4 1 0 0 0)
	    (1 1 1 1 0 0 0)
	    ))

;(91344,111)
(setq p16 '((1 1 1 1 1 0 0 0)
	    (1 0 0 0 1 0 0 0)
	    (1 2 1 0 1 1 1 1)
	    (1 4 0 0 0 0 0 1)
	    (1 0 0 5 0 5 0 1)
	    (1 0 5 0 1 0 1 1)
	    (1 1 1 0 3 0 1 0)
	    (0 0 1 1 1 1 1 0)))

;(3301278,76)
(setq p17 '((1 1 1 1 1 1 1 1 1 1)
	    (1 3 0 0 1 0 0 0 4 1)
	    (1 0 2 0 2 0 0 4 4 1)
	    (1 0 2 2 2 1 1 4 4 1)
	    (1 0 0 0 0 1 1 4 4 1)
	    (1 1 1 1 1 1 0 0 0 0)))

;(??,25)
(setq p18 '((0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0)
	    (0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0)
	    (1 1 1 1 1 0 0 0 0 0 0 1 1 1 1 1)
	    (0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0)
	    (0 0 0 0 0 0 1 0 0 1 0 0 0 0 0 0)
	    (0 0 0 0 0 0 0 0 3 0 0 0 0 0 0 0)
	    (0 0 0 0 0 0 1 0 0 1 0 0 0 0 0 0)
	    (0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0)
	    (1 1 1 1 1 0 0 0 0 0 0 1 1 1 1 1)
	    (0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0)
	    (0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0)
	    (0 0 0 0 1 0 0 0 0 0 4 1 0 0 0 0)
	    (0 0 0 0 1 0 2 0 0 0 0 1 0 0 0 0)
	    (0 0 0 0 1 0 2 0 0 0 4 1 0 0 0 0)
	    ))
;(??,21)
(setq p19 '((0 0 0 1 0 0 0 0 1 0 0 0)
	    (0 0 0 1 0 0 0 0 1 0 0 0)
	    (0 0 0 1 0 0 0 0 1 0 0 0)
	    (1 1 1 1 0 0 0 0 1 1 1 1)
	    (0 0 0 0 1 0 0 1 0 0 0 0)
	    (0 0 0 0 0 0 3 0 0 0 2 0)
	    (0 0 0 0 1 0 0 1 0 0 0 4)
	    (1 1 1 1 0 0 0 0 1 1 1 1)
	    (0 0 0 1 0 0 0 0 1 0 0 0)
	    (0 0 0 1 0 0 0 0 1 0 0 0)
	    (0 0 0 1 0 2 0 4 1 0 0 0)))

;(??,??)
(setq p20 '((0 0 0 1 1 1 1 0 0)
	    (1 1 1 1 0 0 1 1 0)
	    (1 0 0 0 2 0 0 1 0)
	    (1 0 0 5 5 5 0 1 0)
	    (1 0 0 4 0 4 0 1 1)
	    (1 1 0 5 0 5 0 0 1)
	    (0 1 1 5 5 5 0 0 1)
	    (0 0 1 0 2 0 1 1 1)
	    (0 0 1 0 3 0 1 0 0)
	    (0 0 1 1 1 1 1 0 0)))

;(??,??)
(setq p21 '((0 0 1 1 1 1 1 1 1 0)
	    (1 1 1 0 0 1 1 1 1 0)
	    (1 0 0 2 0 0 0 1 1 0)
	    (1 3 2 0 2 0 0 0 1 0)
	    (1 1 0 2 0 2 0 0 1 0)
	    (0 1 1 0 2 0 2 0 1 0)
	    (0 0 1 1 0 2 0 0 1 0)
	    (0 0 0 1 1 1 1 0 1 0)
	    (0 0 0 0 1 4 1 0 0 1)
	    (0 0 0 0 1 4 4 4 0 1)
	    (0 0 0 0 1 0 1 4 0 1)
	    (0 0 0 0 1 4 4 4 0 1)
	    (0 0 0 0 1 1 1 1 1 1)))

;(??,??)
(setq p22 '((0 0 0 0 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0)
	    (0 0 0 0 1 0 0 0 1 0 0 0 0 0 0 0 0 0 0)
	    (0 0 0 0 1 2 0 0 1 0 0 0 0 0 0 0 0 0 0)
	    (0 0 1 1 1 0 0 2 1 1 0 0 0 0 0 0 0 0 0)
	    (0 0 1 0 0 2 0 2 0 1 0 0 0 0 0 0 0 0 0)
	    (1 1 1 0 1 0 1 1 0 1 0 0 0 1 1 1 1 1 1)
	    (1 0 0 0 1 0 1 1 0 1 1 1 1 1 0 0 4 4 1)
	    (1 0 2 0 0 2 0 0 0 0 0 0 0 0 0 0 4 4 1)
	    (1 1 1 1 1 0 1 1 1 0 1 3 1 1 0 0 4 4 1)
	    (0 0 0 0 1 0 0 0 0 0 1 1 1 1 1 1 1 1 1)
	    (0 0 0 0 1 1 1 1 1 1 1 0 0 0 0 0 0 0 0)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
 | Utility functions for printing states and moves.
 | You do not need to understand any of the functions below this point.
 |#

;
; Helper function of prettyMoves
; from s1 --> s2
;
(defun detectDiff (s1 s2)
  (let* ((k1 (getKeeperPosition s1 0))
	 (k2 (getKeeperPosition s2 0))
	 (deltaX (- (car k2) (car k1)))
	 (deltaY (- (cadr k2) (cadr k1)))
	 )
    (cond ((= deltaX 0) (if (> deltaY 0) 'DOWN 'UP))
	  (t (if (> deltaX 0) 'RIGHT 'LEFT))
	  );end cond
    );end let
  );end defun

;
; Translates a list of states into a list of moves.
; Usage: (prettyMoves (a* <problem> #'goal-test #'next-states #'heuristic))
;
(defun prettyMoves (m)
  (cond ((null m) nil)
	((= 1 (length m)) (list 'END))
	(t (cons (detectDiff (car m) (cadr m)) (prettyMoves (cdr m))))
	);end cond
  );

;
; Print the content of the square to stdout.
;
(defun printSquare (s)
  (cond ((= s blank) (format t " "))
	((= s wall) (format t "#"))
	((= s box) (format t "$"))
	((= s keeper) (format t "@"))
	((= s star) (format t "."))
	((= s boxstar) (format t "*"))
	((= s keeperstar) (format t "+"))
	(t (format t "|"))
	);end cond
  )

;
; Print a row
;
(defun printRow (r)
  (dolist (cur r)
    (printSquare cur)
    )
  );

;
; Print a state
;
(defun printState (s)
  (progn
    (dolist (cur s)
      (printRow cur)
      (format t "~%")
      )
    );end progn
  )

;
; Print a list of states with delay.
;
(defun printStates (sl delay)
  (dolist (cur sl)
    (printState cur)
    (sleep delay)
    );end dolist
  );end defun


;(print (h504487052 p1))
;(format t "~%")
;(printState pTest)

;(printStates (sokoban p19 #'h1) .5)

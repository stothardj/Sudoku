#!/usr/bin/guile -s
!#

;    This program is free software: you can redistribute it and/or modify
;    it under the terms of the GNU General Public License as published by
;    the Free Software Foundation, either version 3 of the License, or
;    (at your option) any later version.
;
;    This program is distributed in the hope that it will be useful,
;    but WITHOUT ANY WARRANTY; without even the implied warranty of
;    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;    GNU General Public License for more details.
;
;    You should have received a copy of the GNU General Public License
;    along with this program.  If not, see <http://www.gnu.org/licenses/>.
;
;    Copyright 2010 Jake Stothard

;;;;;;;;;;;;;;;; General Functions ;;;;;;;;;;;;;;;;;;;;;
;; returns a list with items. min <= item < max
(define (range min max)
  (if (< min max)
      (cons min (range (+ min 1) max))
      '()
      )
  )

;; removes all elements in subtracted from ls
(define (list-subtract ls subtracted)
  (filter (lambda (item)
	    (not (memq item subtracted)))
	  ls)
  )

;; rotate a list of lists (ie matrix/board)
(define (rotate-matrix matrix)
  (if (or (null? matrix) (null? (car matrix)))
      '()
      (cons (map car matrix)
	    (rotate-matrix (map cdr matrix))
	    )
      )
  )

;;checks to see if all items in a list are unique
;;ignores matching lists
(define (has-duplicate ls)
  (and
   (not (null? ls))
   (or
    (and (not (list? (car ls)))
	 (memq (car ls) (cdr ls))
	 )
    (has-duplicate (cdr ls)))
   )
  )

;; take the first len symbols off the front of ls and return it
(define (sublist-front ls len)
  (if (zero? len)
      '()
      (cons (car ls) (sublist-front (cdr ls) (- len 1)))
      )
  )

;; take the last len symbols off the front of ls then return what is left
(define (sublist-back ls len)
  (if (zero? len)
      ls
      (sublist-back (cdr ls) (- len 1))
      )
  )

;;;;;;;;;;;;; Sudoku Specific ;;;;;;;;;;;;;;;;;;;;;

;; side effects are used for this so that it can be used interactively
(define continuation-stack '())

;; push continuation onto the continuation stack
(define (push-continuation thunk)
  (set! continuation-stack (cons thunk continuation-stack))
  )

;; backtrack to last place saved on continuation stack
;; returns false if there is no more possibilities
(define (backtrack)
  (if (null? continuation-stack)
      #f
      (let ((cont (car continuation-stack)))
	(set! continuation-stack (cdr continuation-stack))
	(or (cont) (backtrack))
	)
      )
  )

;; Backtrack until it returns false (meaning no more possibilties)
(define (repeat-backtrack)
  (and (backtrack) (repeat-backtrack))
  )

;; replace list with one possibility with terminal
(define (finalize item)
  (if (and (list? item) (not (null? item)) (null? (cdr item)))
      (car item)
      item
      )
  )

;; add all possibilities to X
(define (init-bind board)
  (let ((board-numbers
	 (range 1 (+ (length (car board)) 1))
	 ))
    (map (lambda (row)
	   (map (lambda (item)
		  (if (eqv? item 'X)
		      board-numbers
		      item
		      )
		  )
		row)
	   )
	 board)
    )
  )

;; reduce rows based on terminals
(define (reduce-rows board)
  (map (lambda (row)
	 (let ((terminals
		(filter (lambda(x) (not (list? x))) row)
		))
	   (map (lambda (item)
		  (if (list? item)
		      (finalize (list-subtract item terminals))
		      item
		      )
		  )
		row
		)
	   )
	 )
       board)
  )

;; reduce cols
(define (reduce-cols board)
  (rotate-matrix
   (reduce-rows
    (rotate-matrix
     board))))

;; reduce blocks (not as easy as it sounds)
(define (reduce-blocks board block-width block-height)
  (letrec (
	   (find-terminals (lambda (block accum)
			     (if (null? block)
				 (filter (lambda (x) (not (list? x))) accum)
				 (find-terminals (cdr block) (append accum (car block)))
				 )
			     )
			   )
	   (rblock (lambda (block)
		     (let ((terms
			    (find-terminals block '())))
		       (map (lambda (row)
			      (map (lambda (item)
				     (if (list? item)
					 (finalize (list-subtract item terms))
					 item
					 )
				     )
				   row)
			      )
			    block)
		       )
		     )
		   )
	   (rcol-helper (lambda (bigrow)
			  (if (null? bigrow)
			      '()
			      (append (rblock
				       (sublist-front bigrow block-width)
				       )
				      (rcol-helper
				       (sublist-back bigrow block-width)
				       )
				      )
			      )
			  )
		 )
	   (rcol (lambda (bigrow)
		   (rotate-matrix (rcol-helper (rotate-matrix bigrow)))))
	   (rrow (lambda (board)
		   (if (null? board)
		       '()
		       (append (rcol (sublist-front board block-height))
			     (rrow (sublist-back board block-height)))
		       )
		   )
		 )
	   )
    (rrow board)
    )
  )

;; Returns the position (row col) of the place with the least amounts of
;; possibilities. -1 represents no lists of possibilites found
(define (least-possibilities board)
  (letrec ((vectorized
	 (list->vector (map (lambda (row) (list->vector row)) board))
	 )
	 (least-in-row (lambda (row num least-so-far)
			 (if (>= num (vector-length row))
			     least-so-far
			     (if (and
				  (list? (vector-ref row num))
				  (or (eqv? least-so-far -1)
				      (< (length (vector-ref row num)) (length (vector-ref row least-so-far)))
				      )
				  )
				 (least-in-row row (+ num 1) num)
				 (least-in-row row (+ num 1) least-so-far)
				 )
			     )
			 )
		       )
	 (least-in-board (lambda (crow least-row least-col)
			   (if (>= crow (vector-length vectorized))
			       (cons least-row (cons least-col '()))
				(let ((least-in-this-row (least-in-row (vector-ref vectorized crow) 0 -1)))
				  (if (or
				       (and
					(eqv? least-row -1)
					(not (eqv? least-in-this-row -1))
					)
				       (and
					(not (eqv? least-row -1))
					(not (eqv? least-in-this-row -1))
					(< (length (vector-ref (vector-ref vectorized crow) least-in-this-row))
					   (length (vector-ref (vector-ref vectorized least-row) least-col)))
					)
				       )
				      (least-in-board (+ crow 1) crow least-in-this-row)
				      (least-in-board (+ crow 1) least-row least-col)
				      )
				  )
				)
			   )
			 )
				      
	  )
    (least-in-board 0 -1 -1)
    )
  )

;; Return a board with a possibility removed from coord (row col)
;; Assumes coord is a list of possiblities
(define (remove-possibility board coord)
  (let* ((vectorized
	 (list->vector (map (lambda (row) (list->vector row)) board))
	 )
	(row-num
	 (car coord)
	 )
	(col-num
	 (cadr coord)
	 )
	(row-ref
	 (vector-ref vectorized row-num)
	 )
	(old-item
	 (vector-ref row-ref col-num)
	 )
	(new-item
	 (finalize (cdr old-item))
	 )
	)
    (vector-set! row-ref col-num new-item)
    (map (lambda (row) (vector->list row)) (vector->list vectorized))
    )
  )

;; Return a board with a list of possibilities replaced by the
;; first item in that list of possilities

(define (choose-possibility board coord)
  (let* ((vectorized
	 (list->vector (map (lambda (row) (list->vector row)) board))
	 )
	(row-num
	 (car coord)
	 )
	(col-num
	 (cadr coord)
	 )
	(row-ref
	 (vector-ref vectorized row-num)
	 )
	(old-item
	 (vector-ref row-ref col-num)
	 )
	(new-item
	 (finalize (car old-item))
	 )
	)
    (vector-set! row-ref col-num new-item)
    (map (lambda (row) (vector->list row)) (vector->list vectorized))
    )
  )

;; Make a guess. Push the board with that guess removed onto
;; continuation stack

(define (guess board)
  (let ((least-pos (least-possibilities board))
	)
    (call/cc
     (lambda (cont)
       (push-continuation
	(lambda ()
	  (cont
	   (remove-possibility board least-pos)
	   )))
       (choose-possibility board least-pos)))))

;; Checks to see if a sudoku board is solved completely
(define (sudoku-solved board)
  (letrec ((items-done (lambda (row)
		      (or (null? row)
			  (and (not (list? (car row)))
			       (items-done (cdr row))
			       )
			  )
		      )
		    )
	(rows-done (lambda (board)
		     (or (null? board)
			 (and (items-done (car board))
			      (rows-done (cdr board))
			      )
			 )
		     )
		   ))
    (rows-done board)
    )
  )

;; Checks to see if a sudoku board has any places with no possibilities

(define (sudoku-nopossibilities board)
  (letrec ((items-failed (lambda (row)
			   (if (null? row)
			       #f
			       (or (null? (car row))
				   (items-failed (cdr row))
				   )
			       )
			   )
			 )
	   (rows-failed (lambda (board)
			  (if (null? board)
			      #f
			      (or (items-failed (car board))
				  (rows-failed (cdr board))
				  )
			      )
			  )
			))
    (rows-failed board)
    )
  )

;; Checks to make sure all the items in the rows of the board are unique

(define (sudoku-duplicates-in-row board)
  (and
   (not (null? board))
   (or (has-duplicate (car board)) (sudoku-duplicates-in-row (cdr board)))
   )
  )

;;Checks to make sure all the itens in the cols of the board are unique

(define (sudoku-duplicates-in-col board)
  (sudoku-duplicates-in-row (rotate-matrix board))
  )

;;Checks to make sure all the items in the blocks of the board are unique

(define (sudoku-duplicates-in-block board block-width block-height)
  (letrec ((dupes-in-block
	 (lambda (block accum)
	   (if (null? block)
	       (has-duplicate accum)
	       (dupes-in-block (cdr block) (append (car block) accum))
	       )
	   )
	 )
	   (dcol-rotated
	    (lambda (bigrow-rotated)
	      (and (not (null? bigrow-rotated))
		   (or (dupes-in-block (sublist-front bigrow-rotated block-width) '())
		       (dcol-rotated (sublist-back bigrow-rotated block-width))
		       )
		   )
	     )
	    )
	   (dcol
	    (lambda (bigrow) (dcol-rotated (rotate-matrix bigrow)))
	    )
	   (drow
	    (lambda (brd)
	     (and (not (null? brd))
		   (or (dcol (sublist-front brd block-height))
		       (drow (sublist-back brd block-height))
		       )
		   )
	      )
	    )
	   )
    (drow board)
    )
  )

;; Checks to see if any failure conditions are met
;; TODO
(define (sudoku-failed board box-width box-height)
  (or (sudoku-nopossibilities board)
      (sudoku-duplicates-in-row board)
      (sudoku-duplicates-in-col board)
      (sudoku-duplicates-in-block board box-width box-height)
      )
  )

;; solve sudoku
;; @param board is a list of rows of sudoku board
;; @param box-width is the number of cells horizontally in a box
;; @param box-width is the number of cells vertically in a box
(define (solve-sudoku board box-width box-height)
  (letrec ((sudoku-helper (lambda (bboard)
			    (if (sudoku-failed bboard box-width box-height)
				(backtrack)
				(let ((simplified
				       (reduce-rows (reduce-cols (reduce-blocks bboard box-width box-height)))))
				  (if (equal? bboard simplified)
				      (if (sudoku-solved bboard)
					  bboard
					  (sudoku-helper (guess bboard))
					  )
				      (sudoku-helper simplified)
				      )
				  )
				)
			    )
			  ))
    (set! continuation-stack '())
    (sudoku-helper (init-bind board))
    )
  )

;; simple console drawing of board. Returns something ugly.
;; if board is #f then it simply returns false without drawing
(define (draw-board board)
  (and board
       (map (lambda (row)
	      (map (lambda (item)
		     (display item)
		     (display " ")
		     )
		   row)
	      (newline)
	      )
	    board)
       )
  )

;; Test cases
;; easy test board (requires no guessing) 3 3
(define board1
  '(
    (X X 5 X 1 2 X 4 7)
    (8 3 X 6 X X X X X)
    (X 2 1 9 X 4 3 6 5)
    (3 1 X X X 6 5 X 2)
    (X 5 8 1 X X X X X)
    (4 X 6 5 2 8 X 9 X)
    (1 X 2 4 9 X 7 5 X)
    (5 8 X X X X 4 X X)
    (X 4 X 8 7 X 2 1 6)
    )
  )

;; supposedly hard test board (still requires no guessing) 3 3
(define board2
  '(
    (8 6 X 3 5 4 2 1 X)
    (X 1 X 2 8 X 5 6 3)
    (X X 2 1 6 X 4 X 9)
    (X X 7 X X X 1 9 X)
    (9 3 X X X 1 X 2 4)
    (X X X 4 X 6 X X 5)
    (5 2 3 X 1 8 9 X 6)
    (X X 8 X 3 X X X 1)
    (X X 6 9 4 5 X 3 X)
    )
  )

;; hard board which requires guessing 3 2
(define board3
  '(
    (X X X X 2 X)
    (1 X X 3 X X)
    (X 2 X 5 X X)
    (X X 1 X X X)
    (X X X X X 5)
    (5 4 X 6 X X)
    )
  )

;; board I made up to have more possibilities 2 2
(define board4
  '(
    (1 X X X)
    (X X X X)
    (X X X X)
    (X X X X)
    )
  )

;; Solve and display board1
(draw-board board1)
(newline)
(draw-board (solve-sudoku board1 3 3))
(newline)
(repeat-backtrack)

;; Solve and display board2
(draw-board board2)
(newline)
(draw-board (solve-sudoku board2 3 3))
(newline)
(repeat-backtrack)

;; Solve and display board3
(draw-board board3)
(newline)
(draw-board (solve-sudoku board3 3 2))
(newline)
(repeat-backtrack)

;; Solve and display board4
(draw-board board4)
(newline)
(draw-board (solve-sudoku board4 2 2))
(newline)
(repeat-backtrack)

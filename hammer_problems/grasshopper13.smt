(set-logic AUFLIA)

; Sorts
(declare-sort t_jumps 0)
(declare-sort t_jump_set 0)
(declare-sort t_mine_field 0)
(declare-sort t_jump 0)

; Functions and constants
(declare-fun jumps_concat (t_jumps t_jumps) t_jumps)
(declare-const empty_jumps t_jumps)
(declare-fun jumpset_merge (t_jump_set t_jump_set) t_jump_set)
(declare-const empty_jumpset t_jump_set)
(declare-fun minefield_concat (t_mine_field t_mine_field) t_mine_field)
(declare-const empty_minefield t_mine_field)
(declare-fun s (t_jumps) t_jump_set)
(declare-fun jumps_singleton (t_jump) t_jumps)
(declare-fun jumpset_singleton (t_jump) t_jump_set)
(declare-fun length (t_jump_set) Int)
(declare-fun number (t_jump_set) Int)
(declare-fun length_c1 (t_jump) Int)
(declare-fun length_c2 (t_mine_field) Int)
(declare-fun count (t_mine_field) Int)
(declare-fun minefield_singleton (Bool) t_mine_field)
(declare-fun landings (t_jumps) t_mine_field)
(declare-fun jump_over (t_jump) t_mine_field)
(declare-fun nodup (t_jump_set) Bool)
(declare-fun contains (t_jump_set t_jump) Bool)
(declare-fun getitem (t_mine_field Int) Bool)
(declare-fun subtract (t_jump_set t_jump_set) t_jump_set)
(declare-fun subtract_c1 (t_jump_set t_jump_set) t_jump_set)
(declare-const jumps t_jump_set)
(declare-const size Int)
(declare-const mines t_mine_field)
(declare-const jumps_max t_jump)
(declare-const jumpsr t_jump_set)
(declare-const mines0 t_mine_field)
(declare-const mines1 t_mine_field)
(declare-const mines00 t_mine_field)
(declare-const mines01 t_mine_field)
(declare-const mines10 t_mine_field)
(declare-const mines11 t_mine_field)
(declare-const jumps_ih t_jumps)

; Constraints
(assert (! (forall ((ja t_jumps)) (= (jumps_concat empty_jumps ja) ja)) :named constraint-0))
(assert (! (forall ((ja t_jumps)) (= (jumps_concat ja empty_jumps) ja)) :named constraint-1))
(assert (! (forall ((ja t_jumps) (jc t_jumps) (jb t_jumps)) (= (jumps_concat (jumps_concat ja jb) jc) (jumps_concat ja (jumps_concat jb jc)))) :named constraint-2))
(assert (! (forall ((jsa t_jump_set)) (= (jumpset_merge empty_jumpset jsa) jsa)) :named constraint-3))
(assert (! (forall ((jsa t_jump_set)) (= (jumpset_merge jsa empty_jumpset) jsa)) :named constraint-4))
(assert (! (forall ((jsa t_jump_set) (jsb t_jump_set)) (= (jumpset_merge jsa jsb) (jumpset_merge jsb jsa))) :named constraint-5))
(assert (! (forall ((jsc t_jump_set) (jsa t_jump_set) (jsb t_jump_set)) (= (jumpset_merge (jumpset_merge jsa jsb) jsc) (jumpset_merge jsa (jumpset_merge jsb jsc)))) :named constraint-6))
(assert (! (forall ((ma t_mine_field)) (= (minefield_concat empty_minefield ma) ma)) :named constraint-7))
(assert (! (forall ((ma t_mine_field)) (= (minefield_concat ma empty_minefield) ma)) :named constraint-8))
(assert (! (forall ((mb t_mine_field) (ma t_mine_field) (mc t_mine_field)) (= (minefield_concat (minefield_concat ma mb) mc) (minefield_concat ma (minefield_concat mb mc)))) :named constraint-9))
(assert (! (= (s empty_jumps) empty_jumpset) :named constraint-10))
(assert (! (forall ((jx t_jump)) (= (s (jumps_singleton jx)) (jumpset_singleton jx))) :named constraint-11))
(assert (! (forall ((ja t_jumps) (jb t_jumps)) (= (s (jumps_concat ja jb)) (jumpset_merge (s ja) (s jb)))) :named constraint-12))
(assert (! (= (length (s empty_jumps)) 0) :named constraint-13))
(assert (! (= (number (s empty_jumps)) 0) :named constraint-14))
(assert (! (forall ((jx t_jump)) (= (length (jumpset_singleton jx)) (length_c1 jx))) :named constraint-15))
(assert (! (forall ((jx t_jump)) (= (number (jumpset_singleton jx)) 1)) :named constraint-16))
(assert (! (forall ((jsa t_jump_set) (jsb t_jump_set)) (= (length (jumpset_merge jsa jsb)) (+ (length jsa) (length jsb)))) :named constraint-17))
(assert (! (forall ((jsa t_jump_set) (jsb t_jump_set)) (= (number (jumpset_merge jsa jsb)) (+ (number jsa) (number jsb)))) :named constraint-18))
(assert (! (= (length_c2 empty_minefield) 0) :named constraint-19))
(assert (! (= (count empty_minefield) 0) :named constraint-20))
(assert (! (forall ((x Bool)) (= (length_c2 (minefield_singleton x)) 1)) :named constraint-21))
(assert (! (= (count (minefield_singleton true)) 1) :named constraint-22))
(assert (! (= (count (minefield_singleton false)) 0) :named constraint-23))
(assert (! (forall ((mb t_mine_field) (ma t_mine_field)) (= (length_c2 (minefield_concat ma mb)) (+ (length_c2 ma) (length_c2 mb)))) :named constraint-24))
(assert (! (forall ((mb t_mine_field) (ma t_mine_field)) (= (count (minefield_concat ma mb)) (+ (count ma) (count mb)))) :named constraint-25))
(assert (! (forall ((ja t_jumps) (jb t_jumps)) (= (landings (jumps_concat ja jb)) (minefield_concat (landings ja) (landings jb)))) :named constraint-26))
(assert (! (forall ((ja t_jumps)) (= (count (landings ja)) (number (s ja)))) :named constraint-27))
(assert (! (= (landings empty_jumps) empty_minefield) :named constraint-28))
(assert (! (forall ((jx t_jump)) (= (landings (jumps_singleton jx)) (minefield_concat (jump_over jx) (minefield_singleton true)))) :named constraint-29))
(assert (! (nodup empty_jumpset) :named constraint-30))
(assert (! (forall ((jx t_jump)) (nodup (jumpset_singleton jx))) :named constraint-31))
(assert (! (forall ((jsa t_jump_set) (jsb t_jump_set)) (or (not (nodup (jumpset_merge jsa jsb))) (nodup jsa))) :named constraint-32))
(assert (! (forall ((jsa t_jump_set) (jsb t_jump_set)) (or (not (nodup (jumpset_merge jsa jsb))) (nodup jsb))) :named constraint-33))
(assert (! (forall ((jsa t_jump_set) (jx t_jump) (jsb t_jump_set)) (or (not (nodup (jumpset_merge jsa jsb))) (not (contains jsa jx)) (not (contains jsb jx)))) :named constraint-34))
(assert (! (forall ((jy t_jump) (jx t_jump)) (= (contains (jumpset_singleton jx) jy) (= jx jy))) :named constraint-35))
(assert (! (forall ((jx t_jump)) (not (contains empty_jumpset jx))) :named constraint-36))
(assert (! (forall ((x Int)) (not (getitem empty_minefield x))) :named constraint-37))
(assert (! (forall ((x Int)) (= (getitem (minefield_singleton true) x) (= x 0))) :named constraint-38))
(assert (! (forall ((x Int)) (not (getitem (minefield_singleton false) x))) :named constraint-39))
(assert (! (forall ((mb t_mine_field) (ma t_mine_field) (x Int)) (= (getitem (minefield_concat ma mb) x) (or (getitem ma x) (getitem mb (+ x (* (- 1) (length_c2 ma))))))) :named constraint-40))
(assert (! (forall ((x Int) (jx t_jump)) (not (getitem (jump_over jx) x))) :named constraint-41))
(assert (! (forall ((jx t_jump)) (= (length_c2 (jump_over jx)) (+ (length_c1 jx) (- 1)))) :named constraint-42))
(assert (! (forall ((jx t_jump)) (= (count (jump_over jx)) 0)) :named constraint-43))
(assert (! (forall ((jsa t_jump_set)) (= (subtract empty_jumpset jsa) empty_jumpset)) :named constraint-44))
(assert (! (forall ((jsa t_jump_set)) (= (subtract jsa empty_jumpset) jsa)) :named constraint-45))
(assert (! (forall ((jsa t_jump_set)) (= (subtract jsa jsa) empty_jumpset)) :named constraint-46))
(assert (! (forall ((jsa t_jump_set) (jsb t_jump_set)) (= (subtract jsa (jumpset_merge jsa jsb)) empty_jumpset)) :named constraint-47))
(assert (! (forall ((jsa t_jump_set) (jsb t_jump_set)) (= (subtract (jumpset_merge jsa jsb) jsa) jsb)) :named constraint-48))
(assert (! (forall ((jsc t_jump_set) (jsa t_jump_set) (jsb t_jump_set)) (= (subtract (jumpset_merge jsa jsb) (jumpset_merge jsa jsc)) (subtract_c1 jsb jsc))) :named constraint-49))
(assert (! (forall ((x t_jump)) (not (<= (length_c1 x) 0))) :named constraint-50))
(assert (! (forall ((x t_jump_set)) (<= 0 (length x))) :named constraint-51))
(assert (! (forall ((x t_jump_set)) (<= 0 (number x))) :named constraint-52))
(assert (! (forall ((x t_jump_set)) (<= (number x) (length x))) :named constraint-53))
(assert (! (forall ((x t_jump_set)) (or (not (= (number x) 0)) (= (length x) 0))) :named constraint-54))
(assert (! (forall ((x t_mine_field)) (<= 0 (length_c2 x))) :named constraint-55))
(assert (! (forall ((x t_mine_field)) (<= 0 (count x))) :named constraint-56))
(assert (! (forall ((x t_mine_field)) (<= (count x) (length_c2 x))) :named constraint-57))
(assert (! (forall ((a t_mine_field) (x Int)) (or (not (getitem a x)) (<= 0 x))) :named constraint-58))
(assert (! (forall ((a t_mine_field) (x Int)) (or (not (getitem a x)) (not (<= (length_c2 a) x)))) :named constraint-59))
(assert (! (forall ((a t_mine_field) (x Int)) (or (not (getitem a x)) (not (<= (count a) 0)))) :named constraint-60))
(assert (! (forall ((a t_mine_field) (x Int)) (or (not (<= (length_c2 a) (count a))) (not (<= 0 x)) (<= (length_c2 a) x) (getitem a x))) :named constraint-61))
(assert (! (nodup jumps) :named constraint-62))
(assert (! (= (length jumps) (+ size 1)) :named constraint-63))
(assert (! (= (length_c2 mines) size) :named constraint-64))
(assert (! (not (<= (number jumps) (count mines))) :named constraint-65))
(assert (! (= jumps (jumpset_merge (jumpset_singleton jumps_max) jumpsr)) :named constraint-66))
(assert (! (forall ((x t_jump)) (or (not (contains jumpsr x)) (<= (length_c1 x) (length_c1 jumps_max)))) :named constraint-67))
(assert (! (not (= (number jumpsr) 0)) :named constraint-68))
(assert (! (= mines (minefield_concat mines0 mines1)) :named constraint-69))
(assert (! (= (length_c2 mines0) (length_c1 jumps_max)) :named constraint-70))
(assert (! (= mines0 (minefield_concat mines00 mines01)) :named constraint-71))
(assert (! (= (length_c2 mines00) (+ (length_c1 jumps_max) (- 1))) :named constraint-72))
(assert (! (not (getitem mines01 0)) :named constraint-73))
(assert (! (<= (number jumpsr) (count mines1)) :named constraint-74))
(assert (! (= mines1 (minefield_concat (minefield_concat mines10 (minefield_singleton true)) mines11)) :named constraint-75))
(assert (! (= (count mines10) 0) :named constraint-76))
(assert (! (= jumpsr (s jumps_ih)) :named constraint-77))
(assert (! (forall ((x Int)) (or (not (getitem (landings jumps_ih) x)) (and (not (getitem mines10 x)) (not (getitem mines11 (+ x (* (- 1) (length_c2 mines10)) (- 1))))))) :named constraint-78))
(assert (! (not (getitem (landings jumps_ih) (length_c2 mines10))) :named constraint-79))
(assert (! (not (= (length (subtract jumps (jumpset_merge (jumpset_singleton jumps_max) (s jumps_ih)))) 0)) :named constraint-80))

(check-sat)

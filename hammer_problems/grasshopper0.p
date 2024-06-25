% Sorts
tff(t_jumps_type, type, t_jumps : $tType).
tff(t_jump_set_type, type, t_jump_set : $tType).
tff(t_mine_field_type, type, t_mine_field : $tType).
tff(t_jump_type, type, t_jump : $tType).

% Functions and constants
tff(jumps_concat_type, type, jumps_concat : (t_jumps * t_jumps) > t_jumps).
tff(empty_jumps_type, type, empty_jumps : t_jumps).
tff(jumpset_merge_type, type, jumpset_merge : (t_jump_set * t_jump_set) > t_jump_set).
tff(empty_jumpset_type, type, empty_jumpset : t_jump_set).
tff(minefield_concat_type, type, minefield_concat : (t_mine_field * t_mine_field) > t_mine_field).
tff(empty_minefield_type, type, empty_minefield : t_mine_field).
tff(s_type, type, s : t_jumps > t_jump_set).
tff(jumps_singleton_type, type, jumps_singleton : t_jump > t_jumps).
tff(jumpset_singleton_type, type, jumpset_singleton : t_jump > t_jump_set).
tff(length_type, type, length : t_jump_set > $int).
tff(number_type, type, number : t_jump_set > $int).
tff(length_c1_type, type, length_c1 : t_jump > $int).
tff(length_c2_type, type, length_c2 : t_mine_field > $int).
tff(count_type, type, count : t_mine_field > $int).
tff(minefield_singleton_type, type, minefield_singleton : $o > t_mine_field).
tff(landings_type, type, landings : t_jumps > t_mine_field).
tff(jump_over_type, type, jump_over : t_jump > t_mine_field).
tff(nodup_type, type, nodup : t_jump_set > $o).
tff(contains_type, type, contains : (t_jump_set * t_jump) > $o).
tff(getitem_type, type, getitem : (t_mine_field * $int) > $o).
tff(jumps_type, type, jumps : t_jump_set).
tff(size_type, type, size : $int).
tff(mines_type, type, mines : t_mine_field).
tff(jumpso_type, type, jumpso : t_jumps).
tff(boom_type, type, boom : $int).

% Constraints
tff('constraint_0', axiom, ![Ja:t_jumps] : jumps_concat(empty_jumps, Ja) = Ja).
tff('constraint_1', axiom, ![Ja:t_jumps] : jumps_concat(Ja, empty_jumps) = Ja).
tff('constraint_2', axiom, ![Jb:t_jumps, Jc:t_jumps, Ja:t_jumps] : jumps_concat(jumps_concat(Ja, Jb), Jc) = jumps_concat(Ja, jumps_concat(Jb, Jc))).
tff('constraint_3', axiom, ![Jsa:t_jump_set] : jumpset_merge(empty_jumpset, Jsa) = Jsa).
tff('constraint_4', axiom, ![Jsa:t_jump_set] : jumpset_merge(Jsa, empty_jumpset) = Jsa).
tff('constraint_5', axiom, ![Jsa:t_jump_set, Jsb:t_jump_set] : jumpset_merge(Jsa, Jsb) = jumpset_merge(Jsb, Jsa)).
tff('constraint_6', axiom, ![Jsa:t_jump_set, Jsc:t_jump_set, Jsb:t_jump_set] : jumpset_merge(jumpset_merge(Jsa, Jsb), Jsc) = jumpset_merge(Jsa, jumpset_merge(Jsb, Jsc))).
tff('constraint_7', axiom, ![Ma:t_mine_field] : minefield_concat(empty_minefield, Ma) = Ma).
tff('constraint_8', axiom, ![Ma:t_mine_field] : minefield_concat(Ma, empty_minefield) = Ma).
tff('constraint_9', axiom, ![Mb:t_mine_field, Mc:t_mine_field, Ma:t_mine_field] : minefield_concat(minefield_concat(Ma, Mb), Mc) = minefield_concat(Ma, minefield_concat(Mb, Mc))).
tff('constraint_10', axiom, s(empty_jumps) = empty_jumpset).
tff('constraint_11', axiom, ![Jx:t_jump] : s(jumps_singleton(Jx)) = jumpset_singleton(Jx)).
tff('constraint_12', axiom, ![Jb:t_jumps, Ja:t_jumps] : s(jumps_concat(Ja, Jb)) = jumpset_merge(s(Ja), s(Jb))).
tff('constraint_13', axiom, length(s(empty_jumps)) = 0).
tff('constraint_14', axiom, number(s(empty_jumps)) = 0).
tff('constraint_15', axiom, ![Jx:t_jump] : length(jumpset_singleton(Jx)) = length_c1(Jx)).
tff('constraint_16', axiom, ![Jx:t_jump] : number(jumpset_singleton(Jx)) = 1).
tff('constraint_17', axiom, ![Jsa:t_jump_set, Jsb:t_jump_set] : length(jumpset_merge(Jsa, Jsb)) = $sum(length(Jsa), length(Jsb))).
tff('constraint_18', axiom, ![Jsa:t_jump_set, Jsb:t_jump_set] : number(jumpset_merge(Jsa, Jsb)) = $sum(number(Jsa), number(Jsb))).
tff('constraint_19', axiom, length_c2(empty_minefield) = 0).
tff('constraint_20', axiom, count(empty_minefield) = 0).
tff('constraint_21', axiom, ![X:$o] : length_c2(minefield_singleton(X)) = 1).
tff('constraint_22', axiom, count(minefield_singleton($true)) = 1).
tff('constraint_23', axiom, count(minefield_singleton($false)) = 0).
tff('constraint_24', axiom, ![Mb:t_mine_field, Ma:t_mine_field] : length_c2(minefield_concat(Ma, Mb)) = $sum(length_c2(Ma), length_c2(Mb))).
tff('constraint_25', axiom, ![Mb:t_mine_field, Ma:t_mine_field] : count(minefield_concat(Ma, Mb)) = $sum(count(Ma), count(Mb))).
tff('constraint_26', axiom, ![Jb:t_jumps, Ja:t_jumps] : landings(jumps_concat(Ja, Jb)) = minefield_concat(landings(Ja), landings(Jb))).
tff('constraint_27', axiom, ![Ja:t_jumps] : count(landings(Ja)) = number(s(Ja))).
tff('constraint_28', axiom, landings(empty_jumps) = empty_minefield).
tff('constraint_29', axiom, ![Jx:t_jump] : landings(jumps_singleton(Jx)) = minefield_concat(jump_over(Jx), minefield_singleton($true))).
tff('constraint_30', axiom, nodup(empty_jumpset)).
tff('constraint_31', axiom, ![Jx:t_jump] : nodup(jumpset_singleton(Jx))).
tff('constraint_32', axiom, ![Jsa:t_jump_set, Jsb:t_jump_set] : (~(nodup(jumpset_merge(Jsa, Jsb))) | nodup(Jsa))).
tff('constraint_33', axiom, ![Jsa:t_jump_set, Jsb:t_jump_set] : (~(nodup(jumpset_merge(Jsa, Jsb))) | nodup(Jsb))).
tff('constraint_34', axiom, ![Jsa:t_jump_set, Jx:t_jump, Jsb:t_jump_set] : (~(nodup(jumpset_merge(Jsa, Jsb))) | ~(contains(Jsa, Jx)) | ~(contains(Jsb, Jx)))).
tff('constraint_35', axiom, ![Jx:t_jump, Jy:t_jump] : (contains(jumpset_singleton(Jx), Jy) <=> Jx = Jy)).
tff('constraint_36', axiom, ![Jx:t_jump] : ~(contains(empty_jumpset, Jx))).
tff('constraint_37', axiom, ![X:$int] : ~(getitem(empty_minefield, X))).
tff('constraint_38', axiom, ![X:$int] : (getitem(minefield_singleton($true), X) <=> X = 0)).
tff('constraint_39', axiom, ![X:$int] : ~(getitem(minefield_singleton($false), X))).
tff('constraint_40', axiom, ![Mb:t_mine_field, X:$int, Ma:t_mine_field] : (getitem(minefield_concat(Ma, Mb), X) <=> (getitem(Ma, X) | getitem(Mb, $sum(X, $product(-1, length_c2(Ma))))))).
tff('constraint_41', axiom, ![Jx:t_jump, X:$int] : ~(getitem(jump_over(Jx), X))).
tff('constraint_42', axiom, ![Jx:t_jump] : length_c2(jump_over(Jx)) = $sum(length_c1(Jx), -1)).
tff('constraint_43', axiom, ![Jx:t_jump] : count(jump_over(Jx)) = 0).
tff('constraint_44', axiom, ![X:t_jump] : ~($lesseq(length_c1(X), 0))).
tff('constraint_45', axiom, ![X:t_jump_set] : $lesseq(0, length(X))).
tff('constraint_46', axiom, ![X:t_jump_set] : $lesseq(0, number(X))).
tff('constraint_47', axiom, ![X:t_jump_set] : $lesseq(number(X), length(X))).
tff('constraint_48', axiom, ![X:t_jump_set] : (~(number(X) = 0) | length(X) = 0)).
tff('constraint_49', axiom, ![X:t_mine_field] : $lesseq(0, length_c2(X))).
tff('constraint_50', axiom, ![X:t_mine_field] : $lesseq(0, count(X))).
tff('constraint_51', axiom, ![X:t_mine_field] : $lesseq(count(X), length_c2(X))).
tff('constraint_52', axiom, ![A:t_mine_field, X:$int] : (~(getitem(A, X)) | $lesseq(0, X))).
tff('constraint_53', axiom, ![A:t_mine_field, X:$int] : (~(getitem(A, X)) | ~($lesseq(length_c2(A), X)))).
tff('constraint_54', axiom, ![A:t_mine_field, X:$int] : (~(getitem(A, X)) | ~($lesseq(count(A), 0)))).
tff('constraint_55', axiom, ![A:t_mine_field, X:$int] : (~($lesseq(length_c2(A), count(A))) | ~($lesseq(0, X)) | $lesseq(length_c2(A), X) | getitem(A, X))).
tff('constraint_56', axiom, nodup(jumps)).
tff('constraint_57', axiom, length(jumps) = $sum(size, 1)).
tff('constraint_58', axiom, length_c2(mines) = size).
tff('constraint_59', axiom, ~($lesseq(number(jumps), count(mines)))).
tff('constraint_60', axiom, count(mines) = 0).
tff('constraint_61', axiom, jumps = s(jumpso)).
tff('constraint_62', axiom, getitem(landings(jumpso), boom)).
tff('constraint_63', axiom, getitem(mines, boom)).

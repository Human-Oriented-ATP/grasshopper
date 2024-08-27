import Grasshopper.Definitions

  theorem order_jumps
  : ∀ jumps : JumpSet,
    ∃ jumpso : Jumps,
    jumps = jumpso.s
  := by sorry

  theorem pop_max_jump
    (jumps : JumpSet)
    (_ : jumps.sizeOf > 0)
  : ∃ (j : Jump) (jumpsr : JumpSet),
    jumps = .cons j jumpsr ∧
    (∀ x ∈ jumps, x.length <= j.length)
  := by sorry

  theorem pop_first_jump
    (jumps : Jumps)
    (_ : jumps.length > 0)
  : ∃ (j : Jump) (jumpsr : Jumps),
    jumps = .cons j jumpsr
  := by sorry

  theorem split_mines
    (mines : MineField) (i : ℤ)
    -- (_ : i >= 0)
    (_ : i <= mines.length)
  : ∃ (mines0 mines1 : MineField),
    mines = mines0 ++ mines1 ∧
    mines0.length = i
  := by sorry

  theorem split_first_mine
    (mines : MineField)
    (_ : mines.countMines > 0)
  : ∃ (mines0 mines1 : MineField),
    mines = mines0 ++ singleton true ++ mines1 ∧
    mines0.countMines = 0
  := by sorry

  theorem split_jump_landings
    (jumps : Jumps) (i : Int)
    (_ : i >= 0)
    (_ : i < jumps.sum)
  : ∃ (jumps0 : Jumps) (j : Jump) (jumps1 : Jumps),
    jumps = jumps0 ++ singleton j ++ jumps1 ∧
    jumps0.sum <= i ∧
    jumps0.sum + j.length > i
  := by sorry

  theorem union_mines
    (mines1 mines2 : MineField)
    (_ : mines1.length = mines2.length)
  : ∃ (mines : MineField),
    mines1.length = mines.length ∧
    mines2.length = mines.length ∧
    mines1.countMines <= mines.countMines ∧
    mines2.countMines <= mines.countMines ∧
    (∀ x : ℤ, mines1.getIndexD x → mines.getIndexD x) ∧
    (∀ x : ℤ, mines2.getIndexD x → mines.getIndexD x) ∧
    mines.countMines <= mines1.countMines + mines2.countMines
  := by sorry

section UniversalTheorems

@[universal]
theorem Jump.pos (j : Jump) : j.length > 0 := by
  simp only [gt_iff_lt, Nat.cast_pos, PNat.pos]

@[universal]
theorem JumpSet.length_nonneg (jumps : JumpSet) : jumps.sizeOf ≥ 0 := by
  simp only [ge_iff_le, zero_le]

@[universal]
theorem MineField.length_nonneg (mineField : MineField) : mineField.length ≥ 0 := by
  simp only [ge_iff_le, zero_le]

@[universal]
theorem MineField.count_nonneg (mines : MineField) : mines.countMines ≥ 0 := by
  simp only [ge_iff_le, zero_le]

@[universal]
theorem MineField.length_ge_count (mines : MineField) : mines.length ≥ mines.countMines :=
  mines.count_le_length true

variable (mines : MineField) (idx : Int)

@[universal]
theorem MineField.getIndexD_nonneg : mines.getIndexD idx → idx ≥ 0 := by
  cases idx <;> simp [List.getIndexD]

@[universal]
theorem MineField.getIndexD_lt_length : mines.getIndexD idx → idx < mines.length := by
  match idx with
  | .ofNat n =>
    simp [List.getIndexD, List.getD, Option.getD_eq_iff, @List.get?_eq_some]
    intros; assumption
  | .negSucc _ => exact fun _ => (compare_gt_iff_gt.mp) rfl

@[universal]
theorem MineField.getIndexD_count_pos : mines.getIndexD idx → 0 < mines.countMines := by
  match idx with
  | .ofNat _ =>
    simp [List.getIndexD, List.getD, Option.getD_eq_iff, @List.get?_eq_some, @List.mem_iff_get?]
    aesop
  | .negSucc _ =>
    simp [List.getIndexD]

@[universal]
theorem MineField.full_count
  (hfull : mines.countMines ≥ mines.length)
  (hidx_nonneg : idx ≥ 0)
  (hidx_lt_length : idx < mines.length) :
    mines.getIndexD idx := by
  have : mines.countMines = mines.length :=
    Nat.le_antisymm (mines.count_le_length true) hfull
  rw [List.count_eq_length] at this
  match idx with
  | .ofNat n =>
    simp [List.getIndexD, List.getD, Option.getD_eq_iff, @List.get?_eq_some]
    simp [List.mem_iff_get] at this
    refine' ⟨_, _⟩
    · simp_all only [ge_iff_le, Int.ofNat_eq_coe, Nat.cast_nonneg, Nat.cast_lt]
    · apply this
  | .negSucc _ =>
    simp_all

end UniversalTheorems

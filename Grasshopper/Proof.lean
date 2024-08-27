import Grasshopper.ProcessingAndAutomation

example
  (main_jumps : JumpSet)
  (main_mines : MineField)
  (grasshopper_ih
  : ∀ (jumps : JumpSet) (mines : MineField),
    jumps.sizeOf < main_jumps.sizeOf →
    jumps.Nodup →
    jumps.sum = mines.length+1 →
    jumps.sizeOf > mines.countMines →
    ∃ (jumps_ih : Jumps),
    jumps = jumps_ih.s ∧
    (∀ (x : ℤ), ¬jumps_ih.landings.getIndexD x ∨ ¬mines.getIndexD x)
  ) :
  main_jumps.Nodup →
  main_jumps.sum = main_mines.length+1 →
  main_jumps.sizeOf > main_mines.countMines →
  ∃ (jumpso : Jumps),
  main_jumps = jumpso.s ∧
  (∀ (x : ℤ), ¬jumpso.landings.getIndexD x ∨ ¬main_mines.getIndexD x)
:= by
  intros
  extract ⟨J, jumps, _, _⟩ := pop_max_jump main_jumps
  extract ⟨mines0, mines1, _, _⟩ := split_mines main_mines J.length
  · by_cases ¬(mines0.getIndexD (J.length - 1 : ℤ))
    · extract ⟨jumpso, _, _⟩ := grasshopper_ih jumps mines1
      · use (singleton J : Jumps) ++ jumpso
        refine' ⟨_, fun _ ↦ _⟩ <;> auto
      · extract ⟨mines10, mines11, _, _⟩ := split_first_mine mines1
        extract ⟨jumpso, _, _⟩ := grasshopper_ih jumps (mines10 ++ singleton false ++ mines11)
        by_cases ¬jumpso.landings.getIndexD mines10.length
        · use (singleton J : Jumps) ++ jumpso
          refine' ⟨_, fun _ ↦ _⟩ <;> auto
        · extract ⟨jumps0, J2, jumps1, _, _⟩ := split_jump_landings jumpso (mines10.length+1) (by auto) (by auto)
          use jumps0 ++ singleton J2 ++ singleton J ++ jumps1
          refine' ⟨_, fun _ ↦ _⟩ <;> auto
    · extract ⟨mines00, mines01, _, _⟩ := split_mines mines0 (J.length - 1)
      extract ⟨mines10, mines11, _, _⟩ := split_mines mines1 mines00.length
      · extract ⟨mines_un, _, _, _, _, _, _, _⟩ := union_mines mines00 mines10
        extract ⟨jumpso, _, _⟩ := grasshopper_ih jumps (mines_un ++ mines11)
        extract ⟨J2, jumpso', _⟩ := pop_first_jump jumpso
        use singleton J2 ++ singleton J ++ jumpso'
        refine' ⟨_, fun _ ↦ _⟩ <;> auto
      · extract ⟨mines00', _, _, _⟩ := split_mines mines00 mines1.length
        extract ⟨mines_un, _, _, _, _, _, _, _⟩ := union_mines mines00' mines1
        extract ⟨jumpso, _, _⟩ := grasshopper_ih jumps mines_un
        extract ⟨J2, jumpso', _⟩ := pop_first_jump jumpso
        use singleton J2 ++ singleton J ++ jumpso'
        refine' ⟨_, fun _ ↦ _⟩ <;> auto
  · extract ⟨jumpso⟩ := order_jumps jumps
    use singleton J ++ jumpso
    refine' ⟨_, fun _ ↦ _⟩ <;> auto

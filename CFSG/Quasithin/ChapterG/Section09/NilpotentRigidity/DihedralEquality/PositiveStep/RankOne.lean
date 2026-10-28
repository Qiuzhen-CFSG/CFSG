module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.Induction
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralDegree.Actions
public import Theory.GroupTheory.OddInvolutionEndpointModels

/-!
# Rank one of the dihedral equality induction

The A.1.44 splitting and the prime-order orbit congruence show that a
faithful cubic action in dimension at most two, or a faithful five-factor
action in dimension at most four, is entirely rotation-moved. The
one-summand internal decomposition therefore uses its actual displacement
space. The cubic group is identified with S₃ and the exceptional group
with D₁₀, whose summand has dimension four.

Source: Aschbacher--Smith G.9.2, printed p.352, the case m = 1.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep

open DihedralDegree

universe v

variable {G : Type*} [Group G] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

/-- The one-factor decomposition with its canonical inclusions. -/
noncomputable def singletonInternal (σ : Representation (ZMod 2) G W)
    (hm : movedSpace σ ⊤ = ⊤) : InternalDecomposition σ ⊤ 1 where
  factor _ := ⊤
  groupEquiv := MulEquiv.piUnique _
  group_inclusion := by
    intro i g
    change ((Pi.mulSingle i g : Fin 1 → (⊤ : Subgroup G)) default : G) = g
    rw [Subsingleton.elim (default : Fin 1) i, Pi.mulSingle_eq_same]
  spaceEquiv := (LinearEquiv.piUnique (ZMod 2) _).trans
    ((LinearEquiv.ofEq _ _ hm).trans Submodule.topEquiv)
  space_inclusion := by intro i w; fin_cases i; simp [LinearEquiv.piUnique]

theorem rotationMoved_factor_le_top {ι : Type} [DecidableEq ι] {p : ι → ℕ}
    (σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W) (i : ι) :
    rotationMoved (factorRep σ i) ≤ movedSpace σ ⊤ := by
  apply Submodule.span_le.mpr
  rintro w ⟨⟨g, v⟩, rfl⟩
  exact Representation.Coinvariants.sub_mem_ker (ρ := σ.comp (⊤ : Subgroup _).subtype)
    ⟨Pi.mulSingle i g.val, Subgroup.mem_top _⟩ v

/-- The sharp one-factor bounds leave no fixed-space summand. -/
theorem one_factor_moved_top [FiniteDimensional (ZMod 2) W]
    {ι : Type} [DecidableEq ι] {p : ι → ℕ}
    (split : DihedralSplittingTheorem.{v})
    (σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W)
    (hf : Function.Injective σ) (i : ι) (hp : (p i).Prime) (ho : Odd (p i))
    (hd : (p i = 3 ∧ Module.finrank (ZMod 2) W ≤ 2) ∨
      (p i = 5 ∧ Module.finrank (ZMod 2) W ≤ 4)) :
    movedSpace σ ⊤ = ⊤ := by
  let τ := factorRep σ i
  have hfτ := factorRep_injective σ hf i
  obtain ⟨hD, hM, hpos⟩ := split_dimensions τ split hp ho hfτ
  have hdim : Module.finrank (ZMod 2) (rotationMoved τ) = Module.finrank (ZMod 2) W := by
    rcases hd with ⟨_, hd⟩ | ⟨hp5, hd⟩
    · omega
    · have hmod := rotationMoved_card_modEq τ hp (split W (p i) hp ho τ hfτ).1.disjoint
      have hn : Module.finrank (ZMod 2) (reflectionHalf τ) ≠ 1 := by
        intro he
        rw [hM, he, hp5] at hmod
        norm_num at hmod
      omega
  have htop := Submodule.eq_top_of_finrank_eq hdim
  apply top_unique
  rw [← htop]
  exact rotationMoved_factor_le_top σ i

/-- Both rank-one classifications, with the genuine exceptional factor. -/
theorem equalityAt_one (split : DihedralSplittingTheorem.{v}) : EqualityAt.{v} 1 := by
  intro ι _ _ hc p hp ho W _ _ _ σ hf
  obtain ⟨uniq⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hc
  let : Unique ι := uniq
  let i : ι := default
  let e : (∀ j, DihedralGroup (p j)) ≃* DihedralGroup (p i) := MulEquiv.piUnique _
  have hb := single_factor_bounds (factorRep σ i) split (hp i) (ho i)
    (factorRep_injective σ hf i)
  constructor
  · intro hall hd
    have hm := one_factor_moved_top split σ hf i (hp i) (ho i) (Or.inl ⟨hall i, hd⟩)
    let d := singletonInternal σ hm
    refine ⟨⟨1, d, False.elim, ?_⟩⟩
    intro j _
    left
    refine ⟨?_, ?_⟩
    · obtain ⟨e3⟩ := Theory.GroupTheory.nonempty_dihedralThreeEquivPerm
      have ep : DihedralGroup (p i) ≃* DihedralGroup 3 :=
        MulEquiv.cast (hall i)
      exact ⟨(Subgroup.topEquiv.trans e).trans (ep.trans e3)⟩
    · change Module.finrank (ZMod 2) (movedSpace σ ⊤) = 2
      rw [hm, finrank_top]
      omega
  · rintro ⟨j, hj⟩ hd
    have hi : p i = 5 := by simpa only [Subsingleton.elim j i] using hj
    have hm := one_factor_moved_top split σ hf i (hp i) (ho i) (Or.inr ⟨hi, hd⟩)
    let d := singletonInternal σ hm
    refine ⟨⟨1, d, ?_, ?_⟩⟩
    · intro _
      refine ⟨by decide, ?_, ?_⟩
      · exact ⟨(Subgroup.topEquiv.trans e).trans (MulEquiv.cast hi)⟩
      · change Module.finrank (ZMod 2) (movedSpace σ ⊤) = 4
        rw [hm, finrank_top]
        have hb4 := hb.2.1 (by omega)
        omega
    · intro j hj
      rcases hj with h | h
      · exact (h trivial).elim
      · exact (by omega : False).elim

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep

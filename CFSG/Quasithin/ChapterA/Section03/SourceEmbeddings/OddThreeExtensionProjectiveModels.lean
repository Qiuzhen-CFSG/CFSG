module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionModels
public import Theory.GroupTheory.CentralizerResidualProducts
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# Actual signed ternary cubic covers

Arbitrary finite-field special and projective models are transported to the
concrete SL₃ or SU₃ carrier. The resulting map is surjective, its kernel is
central of exponent dividing three, and the actual target has two-rank at
most two. These are carrier facts only: no SQTK structure is transported
up a central cover.

Source: Aschbacher--Smith A.3.21, pp.55--56.
-/
public noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels

private theorem cover_comp_equiv {H A G : Type*} [Group H] [Group A] [Group G]
    (f : H →* A) (hf : Function.Surjective f) (hc : f.ker ≤ center H)
    (h3 : ∀ x ∈ f.ker, x^3=1) (e : G ≃* A) :
    ∃ g : H →* G, Function.Surjective g ∧ g.ker ≤ center H ∧
      ∀ x ∈ g.ker, x^3=1 := by
  refine ⟨e.symm.toMonoidHom.comp f,e.symm.surjective.comp hf,?_,?_⟩
  · intro x hx
    apply hc
    apply e.symm.injective
    exact hx.trans (map_one _).symm
  · intro x hx
    apply h3
    apply e.symm.injective
    exact hx.trans (map_one _).symm

theorem odd_three_cubic_carrier {G : Type*} [Group G]
    {q : ℕ} [Fact q.Prime] (ho : Odd q) (unitary : Bool)
    (hm : IsPSLSign G unitary 3 q ∨ IsSLSign G unitary 3 q) :
    ∃ residue, ∃ (H : Type) (_ : Group H) (_ : Finite H),
      RankThreeLocalStructure H q residue ∧
      ∃ f : H →* G, Function.Surjective f ∧ f.ker ≤ center H ∧
        ∀ x ∈ f.ker, x^3=1 := by
  rcases hm with hm | hm
  · cases unitary
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : Fintype F := Fintype.ofFinite F
      let a : F ≃+* ZMod q := FiniteField.ringEquivOfCardEq (by
        rw [←Nat.card_eq_fintype_card,hF,ZMod.card])
      let b : SL(3,F) ≃* SL(3,ZMod q) :=
        { Matrix.SpecialLinearGroup.map a.toRingHom with
          invFun := Matrix.SpecialLinearGroup.map a.symm.toRingHom
          left_inv := by intro g; ext i j; exact a.symm_apply_apply (g i j)
          right_inv := by intro g; ext i j; exact a.apply_symm_apply (g i j) }
      let ep : PSL(3,F) ≃* PSL(3,ZMod q) :=
        QuotientGroup.congr _ _ b (map_center_equiv b)
      refine ⟨1,SL(3,ZMod q),inferInstance,inferInstance,sl3_local_structure q ho,?_⟩
      apply cover_comp_equiv (PSL3.projection (ZMod q))
        (PSL3.projection_surjective (ZMod q)) (by rw [PSL3.projection_ker]) _ (e.trans ep)
      intro x hx
      have hz : x ∈ center SL(3,ZMod q) := by simpa only [PSL3.projection_ker] using hx
      have hh : (⟨x,hz⟩ : center SL(3,ZMod q))^3=1 :=
        orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard _).trans
          (Matrix.SL3.card_center_dvd_three (ZMod q)))
      exact congrArg Subtype.val hh
    · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
      let K := ABG.unitaryForm 3 q 1 (by decide)
      let ep := (Matrix.SU3.InnerThreeRank.exists_projective_equiv_standard q F J hF hc).some
      refine ⟨2,RankThreeSU q,inferInstance,inferInstance,su3_local_structure q ho,?_⟩
      apply cover_comp_equiv K.specialToProjective K.specialToProjective_surjective
        K.specialToProjective_ker_le_center _ (e.trans ep)
      intro x hx
      exact congrArg Subtype.val (K.specialToProjective_ker_cube ⟨x,hx⟩)
  · rcases special_odd_three_standard unitary hm with ⟨_,⟨e⟩⟩ | ⟨_,⟨e⟩⟩
    · refine ⟨1,SL(3,ZMod q),inferInstance,inferInstance,sl3_local_structure q ho,
        e.symm.toMonoidHom,e.symm.surjective,?_,?_⟩
      · rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]; exact bot_le
      · intro x hx
        have hx1 : x=1 := e.symm.injective (hx.trans (map_one _).symm)
        simp only [hx1,one_pow]
    · refine ⟨2,RankThreeSU q,inferInstance,inferInstance,su3_local_structure q ho,
        e.symm.toMonoidHom,e.symm.surjective,?_,?_⟩
      · rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]; exact bot_le
      · intro x hx
        have hx1 : x=1 := e.symm.injective (hx.trans (map_one _).symm)
        simp only [hx1,one_pow]

theorem odd_three_two_rank {G : Type*} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime] (ho : Odd q) (unitary : Bool)
    (hm : IsPSLSign G unitary 3 q ∨ IsSLSign G unitary 3 q) : primeRank 2 G ≤ 2 := by
  rcases hm with hm | hm
  · cases unitary
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      exact (primeRank_equiv 2 e).le.trans
        (Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le Fact.out ho hF)
    · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
      let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective e e.surjective
      exact (primeRank_equiv 2 e).le.trans
        (Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J Fact.out ho hF hc)
  · cases unitary
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      exact Theory.SpecificGroups.OddThreeRank.special_primeRank_two_le e
        (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho (k:=1) (by simpa using hF))
    · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
      exact (primeRank_equiv 2 e).le.trans
        (Theory.SpecificGroups.OddThreeRank.hermitian_special_primeRank_two_le J
          (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hF))
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

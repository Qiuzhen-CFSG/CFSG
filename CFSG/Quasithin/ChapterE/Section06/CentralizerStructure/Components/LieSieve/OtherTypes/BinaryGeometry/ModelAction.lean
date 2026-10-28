module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.Normalization
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.Alternating.Aut

/-!
# Actual binary component actions and the symmetric-eight quotient

The conjugation action of LQ on L/O₂(L) is transported through an actual
binary matrix equivalence. The linear model has trivial two-core and center,
so the action kernel is exactly O₂(LQ). Its restriction to L consists of
all inner automorphisms. In dimension four, PSL₄(2) ≃ A₈ and the faithful
conjugation isomorphism S₈ ≃ Aut(A₈) turn an outer actor into an odd
permutation. The even permutations and this actor generate S₈, yielding
an isomorphism of the literal core quotient with S₈.

The other branch records that the actual action is inner. It still needs
invariant parabolics and their block exclusions; it is not the whole E.6.8
alternative. No action kernel or symmetric-group identification is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259). The exceptional equivalence uses the
attributed ATLAS port; the alternating automorphism theorem is GLS3 5.2.1.
-/

@[expose] public section

open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry

private theorem center_eq_bot_of_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hX : center X = ⊥) : center Y = ⊥ := by
  apply eq_bot_iff.mpr
  intro y hy
  have hx : e.symm y ∈ center X := ((centerCongr e).symm ⟨y, hy⟩).property
  have hx1 : e.symm y = 1 := by simpa only [hX, mem_bot] using hx
  apply mem_bot.mpr
  apply e.symm.injective
  simpa using hx1

/-- The two-core is trivial in the actual binary projective model. -/
theorem binary_twoCore_eq_bot {X : Type*} [Group X] {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL X n 2) : pCore 2 X = ⊥ := by
  let e := binaryEquiv hn hm
  apply ((pCore 2 X).map_eq_bot_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso]
  exact BinaryLinear.SmallParabolicLevi.linearGroup_twoCore_eq_bot

/-- The actual intrinsic core quotient, identified with the linear model. -/
noncomputable def binaryCoreEquiv {X : Type*} [Group X] {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL X n 2) : (X ⧸ pCore 2 X) ≃* LinearGroup n :=
  ((QuotientGroup.quotientMulEquivOfEq (binary_twoCore_eq_bot hn hm)).trans
    (QuotientGroup.quotientBot)).trans (binaryEquiv hn hm)

@[simp] theorem binaryCoreEquiv_mk {X : Type*} [Group X] {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL X n 2) (x : X) :
    binaryCoreEquiv hn hm (QuotientGroup.mk' (pCore 2 X) x) = binaryEquiv hn hm x := rfl

/-- Centerlessness needed by the core-quotient action theorem. -/
theorem binary_coreQuotient_center {X : Type*} [Group X] {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL X n 2) : center (X ⧸ pCore 2 X) = ⊥ :=
  center_eq_bot_of_equiv ((slEquivLinear n).trans (binaryCoreEquiv hn hm).symm)
    (binary_center_eq_bot hn)

variable {G : Type*} [Group G] {Q L : Subgroup G} {n : ℕ}

/-- Conjugation on the literal component core quotient in binary coordinates. -/
noncomputable def binaryAction (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (hN : Q ≤ normalizer (L : Set G)) : (L ⊔ Q : Subgroup G) →* MulAut (LinearGroup n) :=
  (MulAut.congr (binaryCoreEquiv hn hm)).toMonoidHom.comp (pCoreJoinAction 2 hN)

/-- The model action intertwines the actual ambient conjugation. -/
theorem binaryAction_apply (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (hN : Q ≤ normalizer (L : Set G)) (g : (L ⊔ Q : Subgroup G)) (l : L) :
    binaryAction hn hm hN g (binaryEquiv hn hm l) =
      binaryEquiv hn hm (L.normalizerMonoidHom (inclusion (sup_le L.le_normalizer hN) g) l) := by
  change binaryCoreEquiv hn hm (pCoreJoinAction 2 hN g
    ((binaryCoreEquiv hn hm).symm (binaryEquiv hn hm l))) = _
  rw [← binaryCoreEquiv_mk hn hm l, (binaryCoreEquiv hn hm).symm_apply_apply,
    pCoreJoinAction_mk, binaryCoreEquiv_mk]

/-- Component elements give the prescribed inner automorphisms. -/
theorem binaryAction_on_component (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (hN : Q ≤ normalizer (L : Set G)) (l : L) :
    binaryAction hn hm hN (inclusion le_sup_left l) = MulAut.conj (binaryEquiv hn hm l) := by
  rw [binaryAction, MonoidHom.comp_apply, pCoreJoinAction_on_component]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_conj, binaryCoreEquiv_mk]

/-- Every inner automorphism occurs in the action image. -/
theorem binaryAction_inner_le_range (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (hN : Q ≤ normalizer (L : Set G)) :
    MulAut.innerSubgroup (LinearGroup n) ≤ (binaryAction hn hm hN).range := by
  rintro a ⟨x, rfl⟩
  obtain ⟨l, rfl⟩ := (binaryEquiv hn hm).surjective x
  exact ⟨inclusion le_sup_left l, binaryAction_on_component hn hm hN l⟩

/-- The exact action kernel follows from the two-group supplement. -/
theorem binaryAction_kernel (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (hN : Q ≤ normalizer (L : Set G)) (hQ : IsPGroup 2 Q) :
    (binaryAction hn hm hN).ker = pCore 2 (L ⊔ Q : Subgroup G) := by
  rw [binaryAction, MonoidHom.ker_comp_of_injective _ _ (MulAut.congr _).injective]
  exact pCoreJoinAction_kernel 2 hN hQ (binary_coreQuotient_center hn hm)

/-- The literal quotient is isomorphic to its faithful model action image. -/
noncomputable def binaryQuotientEquivRange (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L n 2) (hN : Q ≤ normalizer (L : Set G))
    (hQ : IsPGroup 2 Q) :
    ((L ⊔ Q : Subgroup G) ⧸ pCore 2 (L ⊔ Q : Subgroup G)) ≃*
      (binaryAction hn hm hN).range :=
  (QuotientGroup.quotientMulEquivOfEq (binaryAction_kernel hn hm hN hQ).symm).trans
    (QuotientGroup.quotientKerEquivRange (binaryAction hn hm hN))

/-- The linear-to-alternating comparison from the actual projective model. -/
noncomputable def linearFourEquivAltEight : LinearGroup 4 ≃* alternatingGroup (Fin 8) :=
  (projectiveEquivLinear (by decide : 0 < 4)).symm.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8

/-- Conjugation on A₈ gives the full automorphism group of the linear model. -/
noncomputable def symmetricEightAutEquiv :
    Equiv.Perm (Fin 8) ≃* MulAut (LinearGroup 4) :=
  (MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
      (by decide) (by decide))).trans (MulAut.congr linearFourEquivAltEight.symm)

/-- Compatibility with the inner action, retaining the embedded A₈. -/
theorem symmetricEightAutEquiv_on_alt (x : alternatingGroup (Fin 8)) :
    symmetricEightAutEquiv x = MulAut.conj (linearFourEquivAltEight.symm x) := by
  change MulAut.congr linearFourEquivAltEight.symm (MulAut.conjNormal (x : Equiv.Perm (Fin 8))) = _
  rw [show (MulAut.conjNormal (x : Equiv.Perm (Fin 8)) : MulAut (alternatingGroup (Fin 8))) =
    MulAut.conj x from rfl, MulAut.congr_conj]

/-- The actual eight-point permutation action of the component extension. -/
noncomputable def fourPermutationAction (hm : ClassicalGroup.IsPSL L 4 2)
    (hN : Q ≤ normalizer (L : Set G)) : (L ⊔ Q : Subgroup G) →* Equiv.Perm (Fin 8) :=
  symmetricEightAutEquiv.symm.toMonoidHom.comp (binaryAction (by decide) hm hN)

/-- Its restriction is the specified exceptional equivalence on L. -/
theorem fourPermutationAction_on_component (hm : ClassicalGroup.IsPSL L 4 2)
    (hN : Q ≤ normalizer (L : Set G)) (l : L) :
    fourPermutationAction hm hN (inclusion le_sup_left l) =
      linearFourEquivAltEight (binaryEquiv (by decide) hm l) := by
  apply symmetricEightAutEquiv.injective
  rw [fourPermutationAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    symmetricEightAutEquiv.apply_symm_apply, symmetricEightAutEquiv_on_alt,
    linearFourEquivAltEight.symm_apply_apply, binaryAction_on_component]

/-- An outer action gives the actual S₈ quotient; otherwise all actions are inner. -/
theorem four_quotient_alternative (hm : ClassicalGroup.IsPSL L 4 2)
    (hN : Q ≤ normalizer (L : Set G)) (hQ : IsPGroup 2 Q) :
    (binaryAction (by decide) hm hN).range ≤ MulAut.innerSubgroup (LinearGroup 4) ∨
      Nonempty (((L ⊔ Q : Subgroup G) ⧸ pCore 2 (L ⊔ Q : Subgroup G)) ≃*
        Equiv.Perm (Fin 8)) := by
  classical
  by_cases hi : (binaryAction (by decide) hm hN).range ≤ MulAut.innerSubgroup (LinearGroup 4)
  · exact Or.inl hi
  apply Or.inr
  obtain ⟨a, ⟨g, rfl⟩, hg⟩ := SetLike.not_le_iff_exists.mp hi
  let f := fourPermutationAction hm hN
  have hodd : f g ∉ alternatingGroup (Fin 8) := by
    intro he
    apply hg
    refine ⟨linearFourEquivAltEight.symm ⟨f g, he⟩, ?_⟩
    rw [← symmetricEightAutEquiv_on_alt]
    exact symmetricEightAutEquiv.apply_symm_apply _
  have heven (a : Equiv.Perm (Fin 8)) (ha : a ∈ alternatingGroup (Fin 8)) :
      ∃ x : (L ⊔ Q : Subgroup G), f x = a := by
    obtain ⟨l, hl⟩ := ((binaryEquiv (by decide) hm).trans linearFourEquivAltEight).surjective ⟨a, ha⟩
    exact ⟨inclusion le_sup_left l, (fourPermutationAction_on_component hm hN l).trans
      (congrArg Subtype.val hl)⟩
  have hf : Function.Surjective f := by
    intro a
    by_cases ha : a ∈ alternatingGroup (Fin 8)
    · exact heven a ha
    · have hp : a * (f g)⁻¹ ∈ alternatingGroup (Fin 8) := by
        rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two, inv_mem_iff]
        exact iff_of_false ha hodd
      obtain ⟨x, hx⟩ := heven _ hp
      exact ⟨x * g, by rw [map_mul, hx, inv_mul_cancel_right]⟩
  have hk : f.ker = pCore 2 (L ⊔ Q : Subgroup G) := by
    rw [show f = symmetricEightAutEquiv.symm.toMonoidHom.comp
      (binaryAction (by decide) hm hN) from rfl,
      MonoidHom.ker_comp_of_injective _ _ symmetricEightAutEquiv.symm.injective]
    exact binaryAction_kernel (by decide) hm hN hQ
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry

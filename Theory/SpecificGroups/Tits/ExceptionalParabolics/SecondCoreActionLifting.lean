module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreAction
public import Theory.GroupTheory.ConjugationFiberProduct.Quotient
public import Theory.GroupTheory.QuotientKernelComplement
public import Theory.GroupTheory.SelfCentralizingNormalFourComplement

/-!
# Lifting the second-parabolic action while retaining its central kernel

The actual conjugation fiber product has a normal diagonal core. A complement
to the common image of its two projection kernels in the diagonal quotient
recovers an isomorphism of the endpoints. Conjugacy then places the original
marked Sylow in any specified Sylow of the other endpoint, and transporting
the checked generators gives precisely the right-generator three-coset table.

The quotient has order twenty-four and its retained central kernel is a
self-centralizing four-group. Recognition as S₄ supplies the required
complement. Source context: Aschbacher--Smith F.1.11--12, pp.262--264, and
14.2.20--21, pp.988--989; Parrott (1972), §5, p.683.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.SecondCoreActionLifting
open Subgroup SecondCoreAction
open AmalgamRigidity.SecondExtension RelativeSecondBlockLayers

variable {X : Type*} [Group X]

abbrev Fiber (d : Core ≃* pCore 2 X) :=
  ConjugationFiberProduct.fiber Core (pCore 2 X) d

abbrev Diagonal (d : Core ≃* pCore 2 X) :=
  ConjugationFiberProduct.diagonal Core (pCore 2 X) d

abbrev ActionQuotient (d : Core ≃* pCore 2 X) := Fiber d ⧸ Diagonal d

abbrev KernelImage (d : Core ≃* pCore 2 X) : Subgroup (ActionQuotient d) :=
  ConjugationFiberProduct.kernelImage Core (pCore 2 X) d

theorem model_selfCentralizing
    (hZcentralizer : centralizer ((center Core).map Core.subtype : Set second) = Core) :
    centralizer (Core : Set second) ≤ Core := by
  apply le_trans _ hZcentralizer.le
  apply centralizer_le
  rintro _ ⟨z,_,rfl⟩
  exact z.property

/-- The actual diagonal quotient and its retained central kernel have orders
twenty-four and four, respectively. -/
theorem quotient_cards [Finite X]
    (hZcard : Nat.card (center Core) = 4)
    (hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (d : Core ≃* pCore 2 X)
    (himage : (through (pCore 2 X) d).range = model.range) :
    Nat.card (ActionQuotient d) = 24 ∧ Nat.card (KernelImage d) = 4 := by
  have he : (center (pCore 2 X)).map (pCore 2 X).subtype =
      centralizer (pCore 2 X : Set X) := by
    rw [map_center_subtype_eq_inf_centralizer,inf_eq_right.mpr hc]
  have hC : Nat.card (centralizer (pCore 2 X : Set X)) = 4 := by
    rw [← he,← Nat.card_congr ((center (pCore 2 X)).equivMapOfInjective
      (pCore 2 X).subtype (pCore 2 X).subtype_injective).toEquiv,
      ← Nat.card_congr (centerCongr d).toEquiv]
    exact hZcard
  have hF : Nat.card (Fiber d) = 24576 := by
    rw [ConjugationFiberProduct.card_fiber _ _ _ himage,hC,second_card]
  have hD : Nat.card (Diagonal d) = 1024 :=
    (ConjugationFiberProduct.card_diagonal _ _ _).trans second_core_card
  constructor
  · have h := (Diagonal d).card_mul_index
    change Nat.card (Diagonal d) * Nat.card (ActionQuotient d) = Nat.card (Fiber d) at h
    rw [hD,hF] at h
    omega
  · exact (Nat.card_congr (ConjugationFiberProduct.kernelImageEquiv Core
      (pCore 2 X) d).toEquiv).symm.trans
      ((Nat.card_congr (ConjugationFiberProduct.fstKerEquiv Core
        (pCore 2 X) d).toEquiv).trans hC)

/-- The complement is constructed from the actual order-24 quotient. -/
theorem quotient_complement [Finite X]
    (hZcard : Nat.card (center Core) = 4)
    (hZcentralizer : centralizer ((center Core).map Core.subtype : Set second) = Core)
    (hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (d : Core ≃* pCore 2 X)
    (himage : (through (pCore 2 X) d).range = model.range) :
    ∃ U : Subgroup (ActionQuotient d), (KernelImage d).IsComplement' U := by
  obtain ⟨hQ,hK⟩ := quotient_cards hZcard hc d himage
  exact exists_complement_of_selfCentralizing_normal_four (KernelImage d)
    (IsPGroup.of_card (p := 2) (n := 2) (by simpa using hK)) hK
    (ConjugationFiberProduct.kernelImage_selfCentralizing _ _ _ hZcentralizer.le) hQ

/-- The common quotient complement reconstructs the actual endpoint. -/
theorem equiv_of_quotient_complement
    (hZcentralizer : centralizer ((center Core).map Core.subtype : Set second) = Core)
    (hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (d : Core ≃* pCore 2 X)
    (himage : (through (pCore 2 X) d).range = model.range)
    (hcomp : ∃ U : Subgroup (ActionQuotient d), (KernelImage d).IsComplement' U) :
    Nonempty (second ≃* X) := by
  apply QuotientKernelComplement.nonempty_equiv
    (ConjugationFiberProduct.fst Core (pCore 2 X) d)
    (ConjugationFiberProduct.snd Core (pCore 2 X) d)
    (ConjugationFiberProduct.quotientMap Core (pCore 2 X) d)
  · exact ConjugationFiberProduct.fst_surjective _ _ _ himage
  · exact ConjugationFiberProduct.snd_surjective _ _ _ himage
  · simpa only [ConjugationFiberProduct.quotientMap,QuotientGroup.ker_mk'] using
      (ConjugationFiberProduct.disjoint_diagonal_fst_ker Core (pCore 2 X) d).symm
  · simpa only [ConjugationFiberProduct.quotientMap,QuotientGroup.ker_mk'] using
      (ConjugationFiberProduct.disjoint_diagonal_snd_ker Core (pCore 2 X) d).symm
  · exact ConjugationFiberProduct.kernel_images_eq _ _ _
      (model_selfCentralizing hZcentralizer) hc
  · exact hcomp

private theorem reflection_not_mem : gen 0 ∉ S.subgroupOf second := by
  intro hr
  have ht : S.subgroupOf second = ⊤ := by
    apply top_unique
    rw [← gen_generates]
    apply (closure_le _).mpr
    rintro _ ⟨a,rfl⟩
    by_cases ha : a = 0
    · subst a
      exact hr
    · rw [← SecondRecognition.inclusion_positive a ha]
      exact (SecondRecognition.positive a).property
  have hi := second_sylow_index
  rw [ht,index_top] at hi
  contradiction

/-- An endpoint isomorphism supplies the literal collection table on any
specified Sylow, after changing the marking on that same Sylow. -/
theorem reflection_of_equiv [Finite X] (e : second ≃* X) (R : Sylow 2 X) :
    ∃ (j : S →* X), Function.Injective j ∧ j.range = (R : Subgroup X) ∧
      ∃ r : X, r ∉ (R : Subgroup X) ∧
        CosetRelations (SecondRecognition.generators j r) := by
  let P := secondSylowTwo.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨x,hx⟩ := MulAction.exists_smul_eq X P R
  let e' := e.trans (MulAut.conj x)
  let j : S →* X := e'.toMonoidHom.comp (inclusion sylow_le_second)
  have hi : (inclusion sylow_le_second).range = S.subgroupOf second := by
    ext y
    constructor
    · rintro ⟨s,rfl⟩
      exact s.property
    · intro hy
      exact ⟨⟨y.val,hy⟩,rfl⟩
  have hj : j.range = (R : Subgroup X) := by
    have hjmap : j.range = (S.subgroupOf second).map e'.toMonoidHom := by
      change (e'.toMonoidHom.comp (inclusion sylow_le_second)).range = _
      rw [MonoidHom.range_comp,hi]
    rw [hjmap]
    have h := congrArg (fun Q : Sylow 2 X => (Q : Subgroup X)) hx
    change ((secondSylowTwo : Subgroup second).map e.toMonoidHom).map
      (MulAut.conj x).toMonoidHom = (R : Subgroup X) at h
    rw [secondSylowTwo_coe,map_map] at h
    exact h
  refine ⟨j,e'.injective.comp (inclusion_injective sylow_le_second),hj,
    e' (gen 0),?_,?_⟩
  · intro hr
    rw [← hj] at hr
    obtain ⟨s,hs⟩ := hr
    exact reflection_not_mem (show gen 0 ∈ S.subgroupOf second from
      (e'.injective hs) ▸ s.property)
  · have he : SecondRecognition.generators j (e' (gen 0)) = e'.toMonoidHom ∘ gen := by
      funext a
      by_cases ha : a = 0
      · simp only [SecondRecognition.generators,ha,ite_true,Function.comp_apply]
        rfl
      · simp only [SecondRecognition.generators,ha,ite_false,Function.comp_apply]
        change e' (inclusion sylow_le_second (SecondRecognition.positive a)) = e' (gen a)
        rw [SecondRecognition.inclusion_positive a ha]
    rw [he]
    intro a i
    simpa only [map_mul,map_word,map_rep,Function.comp_apply] using
      congrArg e'.toMonoidHom (gen_cosetRelations a i)

/-- Actual reconstruction and marked reflection, conditional only on the
explicit complement step in addition to the identified action. -/
theorem reflection_of_quotient_complement [Finite X]
    (hZcentralizer : centralizer ((center Core).map Core.subtype : Set second) = Core)
    (hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (d : Core ≃* pCore 2 X)
    (himage : (through (pCore 2 X) d).range = model.range)
    (hcomp : ∃ U : Subgroup (ActionQuotient d), (KernelImage d).IsComplement' U)
    (R : Sylow 2 X) :
    ∃ (j : S →* X), Function.Injective j ∧ j.range = (R : Subgroup X) ∧
      ∃ r : X, r ∉ (R : Subgroup X) ∧
        CosetRelations (SecondRecognition.generators j r) := by
  obtain ⟨e⟩ := equiv_of_quotient_complement hZcentralizer hc d himage hcomp
  exact reflection_of_equiv e R

/-- Reconstruction from the original core and its actual conjugation image.
No endpoint equivalence or splitting is assumed. -/
theorem exists_reflection [Finite X]
    (hZcard : Nat.card (center Core) = 4)
    (hZcentralizer : centralizer ((center Core).map Core.subtype : Set second) = Core)
    (hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (d : Core ≃* pCore 2 X)
    (himage : (through (pCore 2 X) d).range = model.range)
    (R : Sylow 2 X) :
    ∃ (j : S →* X), Function.Injective j ∧ j.range = (R : Subgroup X) ∧
      ∃ r : X, r ∉ (R : Subgroup X) ∧
        CosetRelations (SecondRecognition.generators j r) :=
  reflection_of_quotient_complement hZcentralizer hc d himage
    (quotient_complement hZcard hZcentralizer hc d himage) R

end Tits.ExceptionalParabolics.SecondCoreActionLifting

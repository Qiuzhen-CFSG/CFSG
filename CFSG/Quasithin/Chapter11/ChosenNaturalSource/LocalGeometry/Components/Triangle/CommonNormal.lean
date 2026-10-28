module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.OtherResidual
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreInRestriction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Normalization
public import Theory.GroupTheory.SolvableResidual.TwoSupplement

/-!
# Placing the two triangle residuals in their literal join

A nontrivial two-subgroup normalized by T, K₀ and L₂ puts their Sylow join
in H(T). Unique component containment and relative normality then apply.
A subgroup of K₀ acting nontrivially on L₂/O₂(L₂) forces the containing
components to coincide: distinct components commute modulo their own
cores, and restriction to L₂ retains its smaller intrinsic two-core.

The containing component is exactly I = ⟨K₀,L₂⟩. Both generators are
perfect and T-invariant, so I is perfect and normal in IT, with two-group
quotient. This proves I = (IT)^∞ = O²(IT) without an extra generation or
model-classification premise. The source consumer derives the required
noncentrality from the original Cartan cubic and its nontrivial action on
the first flag line. It does not assume that the cubic moves the retained
fixed layer of the full flag.

This is the common-normal branch of the triangle argument, conditional on
its nontrivial common normal subgroup and Cartan intersection witness.
Their construction, the F.1.12 zero-core contradiction, recognition of I,
SL₃(4) exclusion and both final orientations remain obligations of
qt-d-1222-natural-relative-components. The preceding flag and Cartan inputs
retain qt-d-1222-natural-flag-cartan and qt-d-1222-natural-local-geometry as
producer and final discharge owner. No source 11.1.2 completion is asserted.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.762--763, using A.3.7 and 1.2.1(2--3).
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem local_perfect {B P : Subgroup G} (hB : B ∈ Chapter1.L G P) :
    Group.IsPerfect B := by
  let := hB.1.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ P from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

omit [Finite G] in
private theorem perfect_join (B C : Subgroup G)
    [Group.IsPerfect B] [Group.IsPerfect C] : Group.IsPerfect (B ⊔ C : Subgroup G) := by
  apply isPerfect_iff.mpr
  apply le_antisymm (by simpa only [sup_idem] using (Subgroup.commutator_le_sup (B ⊔ C) (B ⊔ C)))
  apply sup_le
  · exact (commutator_eq_self (H := B)).ge.trans
      (commutator_mono le_sup_left le_sup_left)
  · exact (commutator_eq_self (H := C)).ge.trans
      (commutator_mono le_sup_right le_sup_right)

omit [Finite G] in
/-- The common normal two-subgroup places the literal Sylow join in H(T). -/
theorem pair_mem_HOver_of_common_normal (T : Sylow 2 G) {B C Q : Subgroup G}
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hBQ : B ≤ normalizer (Q : Set G)) (hCQ : C ≤ normalizer (Q : Set G)) :
    ((B ⊔ C) ⊔ (T : Subgroup G)) ∈ Chapter1.HOver G (T : Set G) := by
  refine ⟨?_,fun _ hx => (show (T : Subgroup G) ≤ (B ⊔ C) ⊔ (T : Subgroup G) from le_sup_right) hx⟩
  intro he
  apply hQ
  apply bot_unique
  have hc := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hQT)
    (hQT.trans (show (T : Subgroup G) ≤ (B ⊔ C) ⊔ (T : Subgroup G) from le_sup_right))
    (sup_le (sup_le hBQ hCQ) hTQ)
  exact he ▸ hc

/-- Distinct containing components cannot support the specified nontrivial
quotient action of U on B. Normality remains relative to H. -/
theorem same_component_of_noncentral_quotient
    {H B C I J U : Subgroup G}
    (hH : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H))
    (hI : Source.ComponentIn H I) (hJ : Source.ComponentIn H J)
    (hBI : B ≤ I) (hCJ : C ≤ J) (hUC : U ≤ C)
    (hUB : U ≤ normalizer (B : Set G))
    (hnon : ¬ ⁅B,U⁆ ≤ B.pCoreIn 2) : I = J := by
  by_contra hne
  have hne' : I.subgroupOf H ≠ J.subgroupOf H := by
    intro he
    apply hne
    simpa only [map_subgroupOf_eq_of_le hI.1,map_subgroupOf_eq_of_le hJ.1]
      using congrArg (map H.subtype) he
  have hh := (ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two
    hH hI.2 hJ.2 hne').1
  have hcomm : ⁅I,J⁆ ≤ I.pCoreIn 2 := by
    have hm := map_mono (f := H.subtype) (hh.trans inf_le_left)
    simpa only [map_commutator,map_subgroupOf_eq_of_le hI.1,
      map_subgroupOf_eq_of_le hJ.1,pCoreIn_subgroupOf 2 I H hI.1,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 I).trans hI.1)] using hm
  apply hnon
  apply le_trans _ (inf_pCoreIn_le_of_le 2 hBI)
  exact le_inf (le_normalizer_iff_commutator_le_left.mp hUB)
    ((commutator_mono hBI (hUC.trans hCJ)).trans hcomm)

/-- Once the two local residuals share a component, that component is
exactly their join. The original Sylow supplies only a solvable quotient. -/
theorem containing_component_eq_join (T : Sylow 2 G) {B C I : Subgroup G}
    (hB : B ∈ Chapter1.L G T) (hC : C ∈ Chapter1.L G T)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hI : Source.ComponentIn ((B ⊔ C) ⊔ (T : Subgroup G)) I)
    (hBI : B ≤ I) (hCI : C ≤ I) : I = B ⊔ C := by
  let := local_perfect hB
  let := local_perfect hC
  let := perfect_join B C
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  let := hI.2.perfect
  let : Group.IsPerfect I := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hI.1).toMonoidHom) (subgroupOfEquivOfLe hI.1).surjective
  have hn : (T : Subgroup G) ≤ normalizer ((B ⊔ C : Subgroup G) : Set G) :=
    (le_inf hTB hTC).trans (normalizer_inf_normalizer_le_normalizer_sup B C)
  apply le_antisymm _ (sup_le hBI hCI)
  have hr := le_map_solvableResidual_of_isPerfect I ((B ⊔ C) ⊔ (T : Subgroup G)) hI.1
  rwa [map_residual_sup_eq_of_perfect_of_solvable (B ⊔ C) (T : Subgroup G) hn] at hr

/-- The common-normal-subgroup branch constructs the component as the
literal join, together with local membership and both residual identities. -/
theorem pair_component_of_common_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {B C U Q : Subgroup G}
    (hB : B ∈ Chapter1.L G T) (hC : C ∈ Chapter1.L G T)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hUC : U ≤ C) (hUB : U ≤ normalizer (B : Set G))
    (hnon : ¬ ⁅B,U⁆ ≤ B.pCoreIn 2)
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hBQ : B ≤ normalizer (Q : Set G)) (hCQ : C ≤ normalizer (Q : Set G)) :
    Source.NormalComponentIn ((B ⊔ C) ⊔ (T : Subgroup G)) (B ⊔ C) ∧
      (B ⊔ C) ∈ Chapter1.L G T ∧ (B ⊔ C) ∈ Chapter1.He G ∧
      (solvableResidual ((B ⊔ C) ⊔ (T : Subgroup G) : Subgroup G)).map
        ((B ⊔ C) ⊔ (T : Subgroup G)).subtype = B ⊔ C ∧
      (pResidual 2 ((B ⊔ C) ⊔ (T : Subgroup G) : Subgroup G)).map
        ((B ⊔ C) ⊔ (T : Subgroup G)).subtype = B ⊔ C := by
  let H := (B ⊔ C) ⊔ (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hBH : B ≤ H := le_sup_left.trans le_sup_left
  have hCH : C ≤ H := le_sup_right.trans le_sup_left
  have hHN : H ≤ normalizer (Q : Set G) := sup_le (sup_le hBQ hCQ) hTQ
  have hN : IsSQTK KnownSimple.IsKnownSimple (normalizer (Q : Set G)) :=
    hG.twoLocal_sqtk ⟨Q,hQ,T.isPGroup'.to_le hQT,rfl⟩
  have hH : IsSQTK KnownSimple.IsKnownSimple H := by
    let e := (subgroupOfEquivOfLe hHN).symm
    have hh := hN.subgroup (H.subgroupOf (normalizer (Q : Set G)))
    exact ⟨hh.stronglyQuasithin.of_injective e.toMonoidHom e.injective,
      hh.isKGroup.of_injective e.toMonoidHom e.injective⟩
  have hP : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  obtain ⟨I,hI,hBI,_⟩ := exists_unique_normal_component hH hP hBH hB hTB
  obtain ⟨J,hJ,hCJ,_⟩ := exists_unique_normal_component hH hP hCH hC hTC
  have he : I = J := same_component_of_noncentral_quotient
    (ChapterE.Structure.sqtk_two_quotient hH (pCore 2 H) pCore_isPGroup)
    hI.1 hJ.1 hBI hCJ hUC hUB hnon
  have hCI : C ≤ I := he.symm ▸ hCJ
  have heI : I = B ⊔ C := containing_component_eq_join T hB hC hTB hTC hI.1 hBI hCI
  have hj : Source.NormalComponentIn H (B ⊔ C) := heI ▸ hI
  have hh : H ∈ Chapter1.HOver G (T : Set G) :=
    pair_mem_HOver_of_common_normal T hQ hQT hTQ hBQ hCQ
  have hHe : H ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hh
  have hJHe : (B ⊔ C) ∈ Chapter1.He G := Chapter1.lemma_1_1_3_1 hHe
    (fun he => hj.1.2.ne_bot (by rw [he]; exact bot_subgroupOf H)) hj.1.1 hj.1.2.subnormal
  let := local_perfect hB
  let := local_perfect hC
  let := perfect_join B C
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  have hn : (T : Subgroup G) ≤ normalizer ((B ⊔ C : Subgroup G) : Set G) :=
    (le_inf hTB hTC).trans (normalizer_inf_normalizer_le_normalizer_sup B C)
  have hr := map_residual_sup_eq_of_perfect_of_solvable (B ⊔ C) (T : Subgroup G) hn
  refine ⟨hj,⟨hj.1.2,hP,hh.1⟩,hJHe,hr,?_⟩
  rw [pResidual_eq_solvableResidual_of_perfect_sup_twoGroup (B ⊔ C)
    (T : Subgroup G) T.isPGroup' hn]
  exact hr

open scoped commutatorElement
open Closure

omit [Finite G] in
private theorem coreCentralizer_of_commutators {K : Subgroup G} {x : G}
    (hn : x ∈ normalizer (K : Set G))
    (hc : ∀ k ∈ K, ⁅x,k⁆ ∈ K.pCoreIn 2) :
    x ∈ coreQuotientCentralizer K := by
  refine ⟨⟨x,hn⟩,?_,rfl⟩
  apply MulEquiv.ext
  intro q
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) q
  rw [coreQuotientAction_apply_mk]
  obtain ⟨a,ha,he⟩ := hc k k.property
  have he' : a = K.normalizerMonoidHom ⟨x,hn⟩ k * k⁻¹ := Subtype.ext he
  have hh := (QuotientGroup.eq_one_iff (N := pCore 2 K)
    (K.normalizerMonoidHom ⟨x,hn⟩ k * k⁻¹)).mpr (he' ▸ ha)
  change QuotientGroup.mk' (pCore 2 K)
    (K.normalizerMonoidHom ⟨x,hn⟩ k * k⁻¹) = 1 at hh
  rw [map_mul,map_inv] at hh
  exact mul_inv_eq_one.mp hh

/-- A nontrivial Cartan subgroup fixing the first flag line cannot act
trivially on the second residual quotient: its cubic kernel moves that line.
Only nontrivial movement is needed, not movement of the full fixed layer. -/
theorem noncentral_quotient_of_fixed_line
    {B X U W : Subgroup G} (hU : U ≠ ⊥) (hUX : U ≤ X)
    (hUB : U ≤ normalizer (B : Set G)) (hUW : U ≤ centralizer (W : Set G))
    (hcard : Nat.card (X ⊓ coreQuotientCentralizer B : Subgroup G) = 3)
    (hmove : ¬ X ⊓ coreQuotientCentralizer B ≤ centralizer (W : Set G)) :
    ¬ ⁅B,U⁆ ≤ B.pCoreIn 2 := by
  intro hc
  have hUC : U ≤ X ⊓ coreQuotientCentralizer B := by
    refine le_inf hUX ?_
    intro u hu
    apply coreCentralizer_of_commutators (hUB hu)
    intro b hb
    apply hc
    rw [commutator_comm B U]
    exact commutator_mem_commutator hu hb
  have hd : Nat.card U ∣ 3 := hcard ▸ card_dvd_of_le hUC
  have he : U = X ⊓ coreQuotientCentralizer B := by
    apply eq_of_le_of_card_ge hUC
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact (hU (Subgroup.card_eq_one.mp h1)).elim
    · rw [hcard,h3]
  exact hmove (he ▸ hUW)

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
public noncomputable section
open Closure
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The actual p.762 component construction after the common-normal step.
The Cartan intersection and common normal subgroup remain explicit source
obligations; the component, He membership and residual identities are proved.
The conclusion uses the original full flag and the literal join K₀ ∨ L₂. -/
theorem triangle_join_component_of_common_normal
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K₀ X U Q : Subgroup G} (hX : IsCartan T L X)
    (hK₀ : K₀ ∈ Chapter1.L G T)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hU : U ≠ ⊥) (hUX : U ≤ X) (hUL₁ : U ≤ f.Li 0) (hUK₀ : U ≤ K₀)
    (hcard : Nat.card (X ⊓ coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    Source.NormalComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1) ∧
      (K₀ ⊔ f.Li 1) ∈ Chapter1.L G T ∧ (K₀ ⊔ f.Li 1) ∈ Chapter1.He G ∧
      (solvableResidual ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
        ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 ∧
      (pResidual 2 ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
        ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 := by
  have hXN : X ≤ normalizer (f.Li 1 : Set G) := by
    have hx : X ≤ L ⊓ normalizer (f.Vi 1 : Set G) :=
      le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX 1)
    exact (hx.trans (L ⊓ normalizer (f.Vi 1 : Set G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hn := Triangle.noncentral_quotient_of_fixed_line hU hUX
    (hUX.trans hXN) (hUL₁.trans hfix) hcard hmove
  have hh := Triangle.pair_component_of_common_normal S.source.simpleQTKE T
    (flag_mem_local_of_model D S f 1 hm) hK₀ (f.sylow_normalizes_Li 1) hTK₀
    hUK₀ (hUX.trans hXN) hn hQ hQT hTQ hLQ hKQ
  rw [sup_comm (f.Li 1) K₀] at hh
  exact hh

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

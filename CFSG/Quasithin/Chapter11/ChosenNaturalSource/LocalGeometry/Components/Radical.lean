module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Uniqueness
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Membership
public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.SylowSubnormalIntersection
public import FeitThompson.FinalTheorem

/-!
# Sylow control of the other components on the full flag plane

Distinct relative C-components commute modulo their two-cores. The actual
conjugation action on L₂/O₂(L₂) identifies its kernel in L₂T with R₂.
Thus every other component K has T ∩ K contained in R₂. Subnormality makes
this the full Sylow intersection in K. If R₂ centralizes the original V₂,
the action image of K has odd order. The odd-order theorem and perfectness
then make that image trivial.

This proves centralization of the entire plane at every field degree,
including its original C_V(L); it uses neither whole-plane Irr⁺ nor a
bound on the central quotient. The natural-action consumer discharges
noncentrality and quotient centerlessness from the preceding literal maps.
The final consumer applies to the exact second-normalizer refinement.

Full R₂-centralization and the preceding natural maps remain with the
flag/radical producer qt-d-1222-natural-flag-cartan. The relative-components
owner must still prove the local refinement, and the parent
qt-d-1222-natural-local-geometry discharges the preceding flag inputs.
This conditional deduction is not a completed proof of the source family.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.3, printed p.765; the plane-radical action is used in 11.2.4,
printed pp.769--770. This supplies an ambient replacement for the
whole-plane Irr⁺ assertion in the printed proof of 11.1.3.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter12.Section02
open scoped commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

private theorem perfect_hom_eq_one_of_sylow_le_kernel
    {A B : Type*} [Group A] [Finite A] [Group.IsPerfect A] [Group B]
    (P : Sylow 2 A) (φ : A →* B) (hP : (P : Subgroup A) ≤ φ.ker) (a : A) :
    φ a = 1 := by
  let ψ := φ.rangeRestrict
  let : Finite φ.range := Finite.of_surjective ψ φ.rangeRestrict_surjective
  let Q := P.mapSurjective (f := ψ) φ.rangeRestrict_surjective
  have hQ : (Q : Subgroup φ.range) = ⊥ := by
    change (P : Subgroup A).map ψ = ⊥
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    apply Subtype.ext
    exact hP hx
  have hodd : Odd (Nat.card φ.range) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    apply Q.not_dvd_index
    rw [hQ, index_bot]
    exact even_iff_two_dvd.mp he
  let : Group.IsSolvable φ.range := odd_order_theorem φ.range hodd
  have h := map_solvableResidual_le ψ
  rw [solvableResidual_eq_top, solvableResidual_eq_bot, ← MonoidHom.range_eq_map] at h
  have ha : ψ a = 1 := mem_bot.mp (h (MonoidHom.mem_range.mpr ⟨a,rfl⟩))
  exact congrArg Subtype.val ha

private theorem sylow_intersection_le_radical_of_commutator
    {G : Type*} [Group G] {T : Sylow 2 G} {A B : Subgroup G}
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hc : center (A ⧸ pCore 2 A) = ⊥)
    (hcomm : ⁅B,A⁆ ≤ A.pCoreIn 2) :
    (T : Subgroup G) ⊓ B ≤ (A ⊔ (T : Subgroup G)).pCoreIn 2 := by
  intro t ht
  let t' : (A ⊔ (T : Subgroup G) : Subgroup G) := ⟨t,(le_sup_right : (T : Subgroup G) ≤ A ⊔ (T : Subgroup G)) ht.1⟩
  have hk : t' ∈ (pCoreJoinAction 2 hTA).ker := by
    apply MulEquiv.ext
    intro x
    induction x using Quotient.inductionOn with
    | h a =>
      rw [show (⟦a⟧ : A ⧸ pCore 2 A) = QuotientGroup.mk' (pCore 2 A) a from rfl,
        pCoreJoinAction_mk]
      let b := A.normalizerMonoidHom (inclusion (sup_le A.le_normalizer hTA) t') a
      have hb : b * a⁻¹ ∈ pCore 2 A := by
        have hx := hcomm (commutator_mem_commutator ht.2 a.property)
        change b * a⁻¹ ∈ ((pCore 2 A).map A.subtype).comap A.subtype at hx
        rwa [comap_map_eq_self_of_injective A.subtype_injective] at hx
      have he := (QuotientGroup.eq_one_iff (N := pCore 2 A) (b*a⁻¹)).mpr hb
      change QuotientGroup.mk' (pCore 2 A) (b*a⁻¹) = 1 at he
      rw [map_mul,map_inv] at he
      exact mul_inv_eq_one.mp he
  rw [pCoreJoinAction_kernel 2 hTA T.isPGroup' hc] at hk
  exact mem_map_of_mem _ hk

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Other components' actual Sylow intersections lie in the plane radical. -/
theorem other_component_sylow_le_second_radical
    (hL : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) (f.Li 1))
    (hc : center (f.Li 1 ⧸ pCore 2 (f.Li 1)) = ⊥)
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hne : K ≠ f.Li 1) : (T : Subgroup G) ⊓ K ≤ f.Ri 1 := by
  let H := normalizer (f.Vi 1 : Set G)
  let A := (f.Li 1).subgroupOf H
  have hQ := ChapterE.Structure.sqtk_two_quotient
    (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 1)) (pCore 2 H) pCore_isPGroup
  have hne' : K.subgroupOf H ≠ A := by
    intro he
    apply hne
    calc
      K = (K.subgroupOf H).map H.subtype := (map_subgroupOf_eq_of_le hK.1).symm
      _ = A.map H.subtype := congrArg (map H.subtype) he
      _ = f.Li 1 := map_subgroupOf_eq_of_le hL.1
  have hcomm := (ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two
    hQ hK.2 hL.2 hne').1
  have hamb : ⁅K, f.Li 1⁆ ≤ (f.Li 1).pCoreIn 2 := by
    have hh := map_mono (f := H.subtype) (hcomm.trans inf_le_right)
    rw [map_commutator, map_subgroupOf_eq_of_le hK.1,
      map_subgroupOf_eq_of_le hL.1, pCoreIn_subgroupOf 2 _ _ hL.1,
      map_subgroupOf_eq_of_le (((f.Li 1).pCoreIn_le 2).trans hL.1)] at hh
    exact hh
  exact sylow_intersection_le_radical_of_commutator (f.sylow_normalizes_Li 1) hc hamb

/-- Full-radical centralization controls the entire plane, including its center. -/
theorem other_component_centralizes_of_second_radical
    (hL : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) (f.Li 1))
    (hc : center (f.Li 1 ⧸ pCore 2 (f.Li 1)) = ⊥)
    (hR : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hne : K ≠ f.Li 1) : K ≤ centralizer (f.Vi 1 : Set G) := by
  let H := normalizer (f.Vi 1 : Set G)
  let B := K.subgroupOf H
  let P : Sylow 2 H := T.subtype (f.invariant 1)
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal B hK.2.subnormal
  let φ := ((f.Vi 1).normalizerMonoidHom).comp (B.subtype)
  have hP : (Q : Subgroup B) ≤ φ.ker := by
    intro b hb
    have hbT : (b.val.val : G) ∈ (T : Subgroup G) := by
      rw [hQ] at hb
      exact hb
    have hbC := hR (other_component_sylow_le_second_radical S f hL hc hK hne
      ⟨hbT,b.property⟩)
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hbC v v.property).symm
  let := hK.2.perfect
  intro k hk v hv
  have he := perfect_hom_eq_one_of_sylow_le_kernel Q φ hP
    (⟨⟨k,hK.1 hk⟩,hk⟩ : B)
  have hv' := congrArg Subtype.val (DFunLike.congr_fun he ⟨v,hv⟩)
  change k*v*k⁻¹ = v at hv'
  exact (mul_inv_eq_iff_eq_mul.mp hv').symm

/-- Source uniqueness from the full radical action, without a dimension bound. -/
theorem uniqueNoncentral_second_of_radical
    (hL : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) (f.Li 1))
    (hc : center (f.Li 1 ⧸ pCore 2 (f.Li 1)) = ⊥)
    (hR : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    (hmove : ¬ f.Li 1 ≤ centralizer (f.Vi 1 : Set G)) :
    Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  refine ⟨⟨hL,hmove⟩,?_⟩
  intro K hK
  by_contra hne
  exact hK.2 (other_component_centralizes_of_second_radical S f hL hc hR hK.1 hne)

private theorem second_quotient_center_of_model
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree)) :
    center (f.Li 1 ⧸ pCore 2 (f.Li 1)) = ⊥ := by
  let : Group.IsPerfect (f.Li 1) := localResidual_perfect _
  obtain ⟨E, _, _, hE, ⟨e⟩⟩ := hm
  have hfour : 4 ≤ Nat.card E := by
    rw [hE]
    exact (show (4 : ℕ) = 2 ^ 2 from rfl).le.trans
      (Nat.pow_le_pow_right (by decide) S.nonbinary)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : IsSimpleGroup (f.Li 1 ⧸ pCore 2 (f.Li 1)) := e.isSimpleGroup
  rcases (inferInstance : (center (f.Li 1 ⧸ pCore 2 (f.Li 1))).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative (f.Li 1 ⧸ pCore 2 (f.Li 1))
      (center_eq_top_iff.mp ht)).elim

/-- The original natural quotient action supplies noncentrality. The entire
central cover is controlled by R₂, with no restriction on the field degree. -/
theorem uniqueNoncentral_second_of_radical_and_natural_action
    (hL : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) (f.Li 1))
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    (hR : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v)) :
    Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  apply uniqueNoncentral_second_of_radical S f hL
    (second_quotient_center_of_model S f hm) hR
  intro hfix
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq S.field.Carrier
    (![1,0]) (![0,1]) (by simp) (by simp)
  obtain ⟨a,rfl⟩ := hπ g
  obtain ⟨v,hv⟩ := hp (![1,0])
  have he : flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v = v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hfix a.property v.toMul v.toMul.property).symm
  have ha := hact a v
  rw [he,hv] at ha
  have hg' : specialLinearNatural 2 (π a) (![1,0]) = (![0,1]) := hg
  rw [hg'] at ha
  have hz := congrFun ha 0
  simp at hz

/-- The actual second-normalizer sieve feeds the unrestricted-degree consumer.
The first-normalizer triangle is independent of this deduction. -/
theorem uniqueNoncentral_second_of_radical_and_reduction
    (K X : Subgroup G)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (href : RefinementReduction L (f.Li 0) (f.Li 1) K X 1 S.field.degree)
    (hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2 ^ S.field.degree))
    (hR : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    (π : f.Li 1 →* SL(2,S.field.Carrier)) (hπ : Function.Surjective π)
    (p : Additive (f.Vi 1) →ₗ[ZMod 2] (Fin 2 → S.field.Carrier))
    (hp : Function.Surjective p)
    (hact : ∀ a : f.Li 1, ∀ v,
      p (flagAction f 1 ⟨a,(localResidual_le _ a.property).2⟩ v) =
        specialLinearNatural 2 (π a) (p v)) :
    Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  apply uniqueNoncentral_second_of_radical_and_natural_action S f _ hm hR π hπ p hp hact
  rw [href.second_eq]
  exact hK.1

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

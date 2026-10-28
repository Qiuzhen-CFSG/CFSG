module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPushingUp
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.Constrained
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ComponentEscape
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement

/-!
# The remaining original Mathieu point-centralizer alternatives

The original M23 weak-closure bounds force an escaping distinguished vector.
Its literal point residual and original Q satisfy all of C.2.8. The residual
has M22 as its two-core quotient and is normal in the local intersection, so
the proved Mathieu normal-seed theorem excludes every constrained escaping
component. The same exclusion applies to each M24 cocode point configuration.

The surviving alternatives retain either the full generalized-Fitting
preimage inside the local intersection or an escaping normal ordinary
component containing the point residual. In the latter case the original
vector is in the center of that same component. The contained-Fitting and
ordinary exclusions, point-centralizer containment, and final J4 assembly
remain with qt-d-1222-nonff-mathieu. No source 8.1.1 containment is assumed.
Source: Aschbacher--Smith C.2.11--13, C.3.2--4, C.4.8 and 8.1.1,
printed pp.148--154 and712--713, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuPairs
open Sporadic.Mathieu MathieuCode ChapterE
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

private theorem m22_no_constrained_seed
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hn : (B.subgroupOf M).Normal) (e : (B ⧸ pCore 2 B) ≃* M22)
    (K : Subgroup H) (hK : K.IsCComponent) (hqu : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) : False := by
  let := m22_isSimpleGroup
  let : IsQuasisimple M22 :=
    { toIsPerfect := pairResidual_m22_perfect
      simple := ((QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  let c : (M22 ⧸ center M22) ≃* M22 :=
    (QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans QuotientGroup.quotientBot
  let q : B →* (M22 ⧸ center M22) :=
    c.symm.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B)))
  have hq : Function.Surjective q := c.symm.surjective.comp
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  let : Group.IsSolvable q.ker := by
    have hk : q.ker = pCore 2 B := by
      rw [MonoidHom.ker_comp_of_injective _ _ c.symm.injective,
        MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    rw [hk]
    let : Group.IsNilpotent (pCore 2 B) := pCore_isPGroup.isNilpotent
    infer_instance
  exact h.no_constrained_mathieu_normal_seed hn (Or.inr (Or.inl ⟨c⟩)) q hq K hK hqu hout hfK

private theorem m22_point_remainder
    (x : D.sourceOrbit)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple
      (centralizer ({(x : G)} : Set G))
      (centralizer ({(x : G)} : Set G) ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({(x : G)} : Set G)).subtype)
      ((L ⊔ (T : Subgroup G)).pCoreIn 2) D.sourceOrbit)
    (e : (((solvableResidual (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({(x : G)} : Set G)).subtype) ⧸ pCore 2
      ((solvableResidual (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({(x : G)} : Set G)).subtype)) ≃* M22) :
    let H := centralizer ({(x : G)} : Set G)
    let M := normalizer (L : Set G)
    let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    (generalizedFitting (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H)) ≤
        (H ⊓ M).subgroupOf H ∨
      ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
        ¬ K ≤ (H ⊓ M).subgroupOf H ∧ B.subgroupOf H ≤ K ∧
          (x : G) ∈ ((center K).map K.subtype).map H.subtype := by
  let H := centralizer ({(x : G)} : Set G)
  let M := normalizer (L : Set G)
  let C := L ⊓ H
  let B := (solvableResidual C).map C.subtype
  have hNB : H ⊓ M ≤ normalizer (B : Set G) :=
    ((le_inf inf_le_right (inf_le_left.trans H.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image C (solvableResidual C))
  have hn : (B.subgroupOf (H ⊓ M)).Normal := normal_subgroupOf_of_le_normalizer hNB
  rcases hc.component_source_alternative with hf | ⟨K,hK,hqu,hKout,_,ho | hfK⟩
  · exact Or.inl hf
  · have hxH : (x : G) ∈ H := mem_centralizer_singleton_iff.mpr rfl
    have hxK : (⟨x,hxH⟩ : H) ∈ K := ((hc.ordinary_module_placement K ho).1
      (show (⟨x,hxH⟩ : H) ∈ D.sourceOrbit.subgroupOf H from x.property)).2
    let z : K := ⟨⟨x,hxH⟩,hxK⟩
    have hz : z ∈ center K := by
      apply mem_center_iff.mpr
      intro k
      apply Subtype.ext
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp k.val.property
    exact Or.inr ⟨K,ho,hc.ordinary_component_normal K ho,hKout,
      hc.ordinary_component_contains_original K ho,
      ⟨⟨x,hxH⟩,⟨z,hz,rfl⟩,rfl⟩⟩
  · exact (m22_no_constrained_seed hc hn e K hK hqu hKout hfK).elim

/-- The actual M23 branch supplies a strict original pushing-up configuration.
Every constrained escaping component is already excluded by the proved
Mathieu normal-seed theorem; the contained-Fitting and ordinary cases remain. -/
theorem sourceOrbit_m23_strict_pushingUp_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ∃ x : D.sourceOrbit, x ≠ 1 ∧
      let H := centralizer ({(x : G)} : Set G)
      let M := normalizer (L : Set G)
      let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      H ⊓ M < H ∧
        ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ M) B
          ((L ⊔ (T : Subgroup G)).pCoreIn 2) D.sourceOrbit ∧
        Nonempty ((B ⧸ pCore 2 B) ≃* M22) ∧
        ((generalizedFitting (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H)) ≤
            (H ⊓ M).subgroupOf H ∨
          ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
            ¬ K ≤ (H ⊓ M).subgroupOf H ∧ B.subgroupOf H ≤ K ∧
          (x : G) ∈ ((center K).map K.subtype).map H.subtype) := by
  classical
  obtain ⟨a,E,hE,hc28⟩ := D.sourceOrbit_m23_hypothesisC28_of_many h hmany hV hq hnon
  have hex : ∃ x : D.sourceOrbit, E (Additive.ofMul x) ∈ m23WeightTwoOrbit ∧
      ¬ centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G) := by
    by_contra! hn
    exact D.sourceOrbit_m23_false_of_pair_control h hmany hV hq hnon a E hE hn
  obtain ⟨x,hx,hout⟩ := hex
  obtain ⟨hc,⟨e⟩⟩ := hc28 x hx
  have hx1 : x ≠ 1 := by
    intro he
    apply m23WeightTwoOrbit_nonzero hx
    rw [he]
    exact E.map_zero
  exact ⟨x,hx1,lt_of_le_of_ne inf_le_left (fun he => hout (he.symm.le.trans inf_le_right)),
    hc,⟨e⟩,D.m22_point_remainder x hc e⟩

/-- On the actual M24 cocode, constrained escaping components are excluded;
the full original C.2.8 configuration retains the other source alternatives. -/
theorem sourceOrbit_m24_pushingUp_remainder_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (x : D.sourceOrbit) (hx : E (Additive.ofMul x) ∈ weightTwoOrbit) :
    let H := centralizer ({(x : G)} : Set G)
    let M := normalizer (L : Set G)
    let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ M) B
      ((L ⊔ (T : Subgroup G)).pCoreIn 2) D.sourceOrbit ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* M22) ∧
      ((generalizedFitting (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H)) ≤
          (H ⊓ M).subgroupOf H ∨
        ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
          ¬ K ≤ (H ⊓ M).subgroupOf H ∧ B.subgroupOf H ≤ K ∧
          (x : G) ∈ ((center K).map K.subtype).map H.subtype) := by
  obtain ⟨hc,⟨e⟩⟩ := D.sourceOrbit_m24_hypothesisC28_of_many h hmany hV hq hnon a E hE x hx
  exact ⟨hc,⟨e⟩,D.m22_point_remainder x hc e⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

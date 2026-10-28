module

public import Theory.GroupTheory.CComponent.TwoComponent.ResidualLayer
public import Theory.AtlasPort.LinearGroups.G2.Simplicity
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.RootElements
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage
public import Theory.GroupTheory.PPrimeCoreReduction

/-!
# G₂ fixed groups and their two-components

Over every finite field the actual commutator of the split-octonion G₂
model is quasisimple. For q > 2 this follows from existing simplicity and
perfectness; for q = 2 it is the proper simple derived subgroup of order
6048. Thus the solvable residual lies in the ordinary layer in both cases.

Any actual fixed-group equivalence with this full G₂ model consequently
makes every two-component quasisimple. The field-action application uses
the actual coefficient action and a coboundary. Its two descent premises
remain explicit; this module does not claim to solve the cocycle or to
identify the coefficient fixed group.

The characteristic-two assembly uses the proved inner-field automorphism
coverage. Its remaining inputs are exhaustive element conjugacy to the two
root representatives, the two actual root-centralizer odd cores, and the
cocycle and coefficient-descent statements. These explicit inputs account
for all automorphisms, without any Sylow-fixer restriction.

Sources: GLS II Definition 2.4; GLS III Proposition 4.9.1; the G₂(4)
fixed-group discussion in Aschbacher–Smith, printed p.1191. The imported
split-octonion calculations have attribution in LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup Theory.GroupTheory
namespace Atlas.G2.InvolutoryTwoComponents

private theorem quasisimple_of_simple_perfect (G : Type*) [Group G]
    [IsSimpleGroup G] [Group.IsPerfect G] : IsQuasisimple G := by
  have hz : center G = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative G (center_eq_top_iff.mp h))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩

private theorem binary_commutator_quasisimple :
    IsQuasisimple (commutator (Model (ZMod 2))) := by
  let := isSimple_commutator_binary
  let : Group.IsPerfect (commutator (Model (ZMod 2))) := by
    rw [BinaryParabolicPair.commutator_eq_longRootClosure]
    exact BinaryException.H_isPerfect
  exact quasisimple_of_simple_perfect _

variable (F : Type*) [Field F] [Finite F]

/-- Includes the proper derived subgroup at field order two. -/
theorem commutator_quasisimple : IsQuasisimple (commutator (Model F)) := by
  by_cases hq : 2 < Nat.card F
  · let := isSimple hq
    let := isPerfect hq
    let := quasisimple_of_simple_perfect (Model F)
    exact IsQuasisimple.of_mulEquiv
      ((MulEquiv.subgroupCongr (Group.IsPerfect.commutator_eq_top (G := Model F))).trans
        topEquiv).symm
  · have hcard : Nat.card F = 2 := by
      have := Finite.one_lt_card (α := F)
      omega
    let e := fieldEquiv (binaryFieldEquiv hcard)
    have hm : (commutator (Model F)).map e.toMonoidHom =
        commutator (Model (ZMod 2)) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
      rfl
    let d := (e.subgroupMap (commutator (Model F))).trans (MulEquiv.subgroupCongr hm)
    let := binary_commutator_quasisimple
    exact IsQuasisimple.of_mulEquiv d.symm

/-- Every perfect subgroup lies in the ordinary layer of the full G₂ model. -/
theorem solvableResidual_le_componentLayer :
    solvableResidual (Model F) ≤ componentLayer (Model F) := by
  have hcomp : IsComponent (Model F) (commutator (Model F)) :=
    ⟨(inferInstance : (commutator (Model F)).Normal).isSubnormal,
      commutator_quasisimple F⟩
  exact (solvableResidual_le_derivedSeries 1).trans (le_sSup hcomp)

variable {F}

/-- Use an equivalence of the actual fixed group, retaining the binary endpoint. -/
theorem fixed_twoComponent_isQuasisimple_of_equiv
    {G : Type*} [Group G] (a : MulAut G)
    (e : a.fixedSubgroup ≃* Model F)
    (L : Subgroup a.fixedSubgroup) (hL : L.IsTwoComponent) : IsQuasisimple L := by
  have hq := ((hL.1.map_equiv e).isComponent_of_solvableResidual_le_componentLayer
    (solvableResidual_le_componentLayer F)).2
  exact IsQuasisimple.of_mulEquiv (e.subgroupMap L).symm (hG := hq)

/-- The concrete coefficient-action application; both descent inputs remain explicit. -/
theorem field_twoComponent_isQuasisimple_of_coboundary_of_descent
    (a : MulAut (Model F)) (g : Model F) (σ : F ≃+* F)
    (he : a = MulAut.conj g * LieAutomorphismExtensions.fieldAction σ)
    (hboundary : ∃ c : Model F, g = c * LieAutomorphismExtensions.fieldAction σ c⁻¹)
    (descent : (LieAutomorphismExtensions.fieldAction σ).fixedSubgroup ≃*
      Model (EvenFieldFixedResidual.fixedField σ))
    (L : Subgroup a.fixedSubgroup) (hL : L.IsTwoComponent) : IsQuasisimple L := by
  obtain ⟨c, hc⟩ := hboundary
  exact fixed_twoComponent_isQuasisimple_of_equiv a
    ((EvenFieldFixedResidual.fixedEquivOfCoboundary a g c σ he hc).trans descent) L hL

end Atlas.G2.InvolutoryTwoComponents

namespace Atlas.G2.InvolutoryTwoComponents
variable {F : Type*} [Field F]

private theorem conjugate_fixed_oddCore (r g : Model F)
    (hr : pPrimeCore 2 (MulAut.conj r).fixedSubgroup = ⊥) :
    pPrimeCore 2 (MulAut.conj (MulAut.conj g r)).fixedSubgroup = ⊥ := by
  let e : (MulAut.conj (MulAut.conj g r)).fixedSubgroup ≃*
      (MulAut.conj r).fixedSubgroup :=
    MulAut.fixedSubgroupEquivOfCompatible (MulAut.conj g⁻¹) _ _ (by
      intro x
      change g⁻¹ * ((g * r * g⁻¹) * x * (g * r * g⁻¹)⁻¹) * (g⁻¹)⁻¹ =
        r * (g⁻¹ * x * (g⁻¹)⁻¹) * r⁻¹
      group)
  exact pPrimeCore_eq_bot_of_equiv e hr

/-- Actual root conjugacy transports the intrinsic odd core of the fixed group. -/
theorem inner_fixed_oddCore_of_root
    (hA : ∀ t : F, t ≠ 0 → pPrimeCore 2 (MulAut.conj (rootA t)).fixedSubgroup = ⊥)
    (hC : ∀ t : F, t ≠ 0 → pPrimeCore 2 (MulAut.conj (rootC t)).fixedSubgroup = ⊥)
    (x : Model F) (hx : EvenInvolutionGeometry.IsRootElement x) :
    pPrimeCore 2 (MulAut.conj x).fixedSubgroup = ⊥ := by
  rcases hx with ⟨g, t, ht, rfl⟩ | ⟨g, t, ht, rfl⟩
  · exact conjugate_fixed_oddCore _ _ (hA t ht)
  · exact conjugate_fixed_oddCore _ _ (hC t ht)

open LieAutomorphismExtensions EvenFieldFixedResidual

/-- All even-field automorphisms are handled by root cores and genuine field descent.
The five displayed geometric premises remain to be supplied by their model proofs. -/
theorem even_hasInvolutoryB2_of_root_cores_of_descent [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F)
    (hroot : ∀ x : Model F, x ^ 2 = 1 → x ≠ 1 → EvenInvolutionGeometry.IsRootElement x)
    (hA : ∀ t : F, t ≠ 0 → pPrimeCore 2 (MulAut.conj (rootA t)).fixedSubgroup = ⊥)
    (hC : ∀ t : F, t ≠ 0 → pPrimeCore 2 (MulAut.conj (rootC t)).fixedSubgroup = ⊥)
    (hboundary : ∀ (σ : F ≃+* F), orderOf σ = 2 → ∀ g : Model F,
      g * fieldAction σ g = 1 → ∃ c : Model F, g = c * fieldAction σ c⁻¹)
    (hdescent : ∀ (σ : F ≃+* F), orderOf σ = 2 →
      Nonempty ((fieldAction σ).fixedSubgroup ≃* Model (fixedField σ))) :
    HasInvolutoryB2 (Model F) := by
  intro a ha L hL
  by_cases hi : ∃ x : Model F, a = MulAut.conj x
  · obtain ⟨x, rfl⟩ := hi
    have hinj := conj_injective_of_center_eq_bot (model_center_eq_bot hq)
    have hx : orderOf x = 2 := (orderOf_injective MulAut.conj hinj x).symm.trans ha
    have hs : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
    have hn : x ≠ 1 := by
      intro he
      simp [he] at hx
    exact (hL.isComponent_of_oddCore_eq_bot
      (inner_fixed_oddCore_of_root hA hC x (hroot x hs hn))).2
  · obtain ⟨g, σ, he⟩ := exists_inner_field hq a
    have hs : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
    obtain ⟨hσ, hg⟩ := coefficient_involution_and_cocycle hq a hs g σ he
      (fun x hx => hi ⟨x, hx⟩)
    obtain ⟨e⟩ := hdescent σ hσ
    exact field_twoComponent_isQuasisimple_of_coboundary_of_descent a g σ he
      (hboundary σ hσ g hg) e L hL

end Atlas.G2.InvolutoryTwoComponents

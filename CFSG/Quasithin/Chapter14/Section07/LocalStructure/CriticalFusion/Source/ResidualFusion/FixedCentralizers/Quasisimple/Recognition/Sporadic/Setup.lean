module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.PerfectCentralCover

/-!
# The marked sporadic cover and its actual fixed residual

The original nonidentity u is central in L_u and belongs to its two-core.
Consequently the literal map J → J/O₂(J) → S is a perfect central cover
with even kernel, where J is L_u as a subgroup of G_u. For the given
conjugation by z, the image of the fixed subgroup is L_u ∩ C_G(z).
Its two-residual is therefore the original K, with its ambient inclusion.

These are preparations for the sporadic sieve, not a Ru recognition
assertion. The generation identity is retained as an earlier-source input.

Source: Aschbacher–Smith, 14.7.68(2), printed p.1071 (PDF p.1088), and
1.1.5(3)(f), printed p.502, combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter15.Section03.Candidates.ComponentStructure
open ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace SporadicSieve

/-- The original hypotheses of the sporadic branch, before selecting its name.
The actual quotient equivalence is supplied separately, so it remains marked. -/
structure Case (d : Data T L V F W) (u : F.U) (Lu : Subgroup G)
    (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))) (name : SporadicName) : Prop where
  member : (u : G) ∈ d.U₀
  nontrivial : (u : G) ≠ 1
  fixed : d.FixedModuloPoint u
  normalizer_eq : normalizer (K F : Set G) = F.H
  maximal : IsMaximalTwoLocal F.H
  sylow : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u)
  le_centralizer : Lu ≤ d.fixedCentralizer u
  component : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent
  normal : (Lu.subgroupOf (d.fixedCentralizer u)).Normal
  contains : K F < Lu
  escapes : ¬ Lu ≤ F.H
  quasisimple : IsQuasisimple Lu
  generation : F.U = ⁅F.U, K F⁆
  conjugation : ∀ x : Lu.subgroupOf (d.fixedCentralizer u),
    ((α x : d.fixedCentralizer u) : G) = d.z * (x : G) * d.z⁻¹
  not_j3 : name ≠ .j3
  twoCentral : TwoCentralInner α

private theorem central_involution_mem_twoCore {A : Type*} [Group A] [Finite A]
    (x : A) (hc : x ∈ center A) (ho : orderOf x = 2) : x ∈ pCore 2 A := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ho, pow_one])
  have hn : (zpowers x).Normal := by
    constructor
    intro y hy a
    have hcy := (zpowers_le.mpr hc) hy
    rw [mem_center_iff.mp hcy a]
    simpa using hy
  exact (le_sSup ⟨hn, hp⟩ : zpowers x ≤ pCore 2 A) (mem_zpowers x)

end SporadicSieve

namespace Data
variable (d : Data T L V F W)

/-- The unchanged inclusion J → G_u → G. -/
def fixedComponentInclusion (u : F.U) (Lu : Subgroup G) :
    Lu.subgroupOf (d.fixedCentralizer u) →* G :=
  (d.fixedCentralizer u).subtype.comp (Lu.subgroupOf (d.fixedCentralizer u)).subtype

theorem fixedComponentInclusion_injective (u : F.U) (Lu : Subgroup G) :
    Function.Injective (d.fixedComponentInclusion u Lu) :=
  (d.fixedCentralizer u).subtype_injective.comp
    (Lu.subgroupOf (d.fixedCentralizer u)).subtype_injective

/-- The source involution makes the intrinsic two-core even. -/
theorem fixedComponent_twoCore_even (hgen : F.U = ⁅F.U, K F⁆)
    (u : F.U) (hne : (u : G) ≠ 1) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u) (hKLu : K F ≤ Lu) :
    2 ∣ Nat.card (pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) := by
  have huLu := d.fixed_mem_component_of_commutator hgen u hKLu
  let x : Lu.subgroupOf (d.fixedCentralizer u) := ⟨⟨u, hLu huLu⟩, huLu⟩
  have hx : x ∈ center (Lu.subgroupOf (d.fixedCentralizer u)) := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp y.val.property
  have ho : orderOf x = 2 := by
    rw [← orderOf_injective (d.fixedComponentInclusion u Lu)
      (d.fixedComponentInclusion_injective u Lu)]
    exact d.fixedElement_order u hne
  have hm := SporadicSieve.central_involution_mem_twoCore x hx ho
  let v : pCore 2 (Lu.subgroupOf (d.fixedCentralizer u)) := ⟨x, hm⟩
  have hv : orderOf v = 2 := by
    rw [← orderOf_injective (pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))).subtype
      (pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))).subtype_injective]
    exact ho
  have hd := _root_.orderOf_dvd_natCard v
  rwa [hv] at hd

/-- The literal perfect central covering obtained from the supplied quotient map. -/
def fixedSporadicCover (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u) (hq : IsQuasisimple Lu)
    {name : SporadicName}
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier) :
    PerfectCentralCovering.Cover (Lu.subgroupOf (d.fixedCentralizer u)) name.Carrier := by
  let := hq
  let : IsQuasisimple (Lu.subgroupOf (d.fixedCentralizer u)) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLu).symm
  exact
    { toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 _))
      surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
      isPerfect := inferInstance
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
        exact IsQuasisimple.pCore_le_center 2 }

@[simp] theorem fixedSporadicCover_apply (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u) (hq : IsQuasisimple Lu)
    {name : SporadicName}
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier)
    (x : Lu.subgroupOf (d.fixedCentralizer u)) :
    (d.fixedSporadicCover u hLu hq e).toMonoidHom x =
      e (QuotientGroup.mk' (pCore 2 _) x) := rfl

@[simp] theorem fixedSporadicCover_kernel (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u) (hq : IsQuasisimple Lu)
    {name : SporadicName}
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier) :
    (d.fixedSporadicCover u hLu hq e).toMonoidHom.ker =
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u)) := by
  exact (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)

/-- The fixed subgroup is exactly the original ambient centralizer intersection. -/
theorem fixedComponent_fixedSubgroup_image (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u)
    (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u)))
    (ha : ∀ x : Lu.subgroupOf (d.fixedCentralizer u),
      ((α x : d.fixedCentralizer u) : G) = d.z * (x : G) * d.z⁻¹) :
    α.fixedSubgroup.map (d.fixedComponentInclusion u Lu) =
      Lu ⊓ centralizer ({d.z} : Set G) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have he := ha x
    have hx := (MulAut.mem_fixedSubgroup α x).mp hx
    rw [hx] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · intro hg
    let x : Lu.subgroupOf (d.fixedCentralizer u) := ⟨⟨g, hLu hg.1⟩, hg.1⟩
    refine ⟨x, ?_, rfl⟩
    apply (MulAut.mem_fixedSubgroup α x).mpr
    apply (d.fixedComponentInclusion_injective u Lu)
    change ((α x : d.fixedCentralizer u) : G) = g
    rw [ha]
    change d.z * g * d.z⁻¹ = g
    rw [← mem_centralizer_singleton_iff.mp hg.2, mul_inv_cancel_right]

/-- The literal fixed residual maps onto K, so its model structure must be
compared with K's original quotient and chief factors. -/
theorem fixedComponent_fixedResidual_image (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u) (hKLu : K F ≤ Lu)
    (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u)))
    (ha : ∀ x : Lu.subgroupOf (d.fixedCentralizer u),
      ((α x : d.fixedCentralizer u) : G) = d.z * (x : G) * d.z⁻¹) :
    (MulAut.embeddedFixedResidual 2 α).map (d.fixedComponentInclusion u Lu) = K F := by
  rw [MulAut.embeddedFixedResidual, map_embedded_pResidual,
    d.fixedComponent_fixedSubgroup_image u hLu α ha]
  exact d.fixedComponent_centralizerResidual hKLu

/-- The residual comparison is an actual equivalence induced by the original
ambient inclusion, rather than a group-family label. -/
def fixedComponentResidualEquiv (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u) (hKLu : K F ≤ Lu)
    (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u)))
    (ha : ∀ x : Lu.subgroupOf (d.fixedCentralizer u),
      ((α x : d.fixedCentralizer u) : G) = d.z * (x : G) * d.z⁻¹) :
    MulAut.embeddedFixedResidual 2 α ≃* K F :=
  ((MulAut.embeddedFixedResidual 2 α).equivMapOfInjective
    (d.fixedComponentInclusion u Lu) (d.fixedComponentInclusion_injective u Lu)).trans
      (MulEquiv.subgroupCongr (d.fixedComponent_fixedResidual_image u hLu hKLu α ha))

@[simp] theorem fixedComponentResidualEquiv_apply (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u) (hKLu : K F ≤ Lu)
    (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u)))
    (ha : ∀ x : Lu.subgroupOf (d.fixedCentralizer u),
      ((α x : d.fixedCentralizer u) : G) = d.z * (x : G) * d.z⁻¹)
    (x : MulAut.embeddedFixedResidual 2 α) :
    (d.fixedComponentResidualEquiv u hLu hKLu α ha x : G) =
      d.fixedComponentInclusion u Lu x := rfl

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

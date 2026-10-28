module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Contracts
public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import Theory.GroupTheory.NormalizerQuotientOuterPair
public import Theory.FieldTheory.BinaryNormOne

/-!
# The literal central Hall action and exponent transport

Restrict normalizer conjugation to the actual Hall subgroup of H intersect M.
Its kernel maps into C_G(L₀/O₂(L₀)), with the two-core taken intrinsically in
L₀. The permitted section-faithfulness premise therefore makes this action
injective. A three-group image or an embedding of that image in two norm-one
tori transfers back to the original Hall carrier.

The actual image calculations are separate source obligations, consumed in
`CentralHall.Source`. No model classification or Hall placement is asserted
by this module. Source: Aschbacher--Smith, 10.2.3(2), printed p.745.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10.CentralHall
open Chapter3.Section02 Chapter4
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Conjugation on the literal orbit two-core quotient. -/
def action {H : Subgroup G} (B : Subgroup H)
    (hBM : B ≤ D.maximalLocal.subgroupOf H) :
    B →* MulAut (localOrbit T L ⧸ pCore 2 (localOrbit T L)) :=
  (normalizerPCoreQuotientAction (localOrbit T L)).comp
    ((H.subtype.comp B.subtype).codRestrict D.maximalLocal (fun b => hBM b.property))

/-- A trivial quotient action has commutators in the intrinsic two-core. -/
theorem action_kernel_image_le {H : Subgroup G} (B : Subgroup H)
    (hBM : B ≤ D.maximalLocal.subgroupOf H) :
    (action D B hBM).ker.map (H.subtype.comp B.subtype) ≤
      sectionCentralizer (localOrbit T L) := by
  let R := localOrbit T L
  let f := action D B hBM
  apply (le_sectionCentralizer_iff _ _).mpr
  refine ⟨?_,commutator_le.mpr ?_⟩
  · rintro _ ⟨b,_,rfl⟩
    exact hBM b.property
  · rintro _ ⟨b,hb,rfl⟩ r hr
    have hbr := DFunLike.congr_fun (show f b = 1 from hb)
      (QuotientGroup.mk' (pCore 2 R) ⟨r,hr⟩)
    change quotientAut (pCore 2 R) _ _ = _ at hbr
    rw [quotientAut_apply_mk] at hbr
    let r' : R := ⟨r,hr⟩
    let bM : D.maximalLocal := ⟨b.val.val,hBM b.property⟩
    let br := R.normalizerMonoidHom bM r'
    have hh : br * r'⁻¹ ∈ pCore 2 R := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 R) (br * r'⁻¹) = 1
      rw [map_mul,map_inv]
      change QuotientGroup.mk' (pCore 2 R) br = QuotientGroup.mk' (pCore 2 R) r' at hbr
      rw [hbr,mul_inv_cancel]
    exact ⟨br * r'⁻¹,hh,rfl⟩

/-- The contract's section kernel is exactly the faithfulness needed here. -/
theorem action_injective {H : Subgroup G} (B : Subgroup H)
    (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hfaith : B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥) :
    Function.Injective (action D B hBM) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro b hb
  apply mem_bot.mpr
  apply Subtype.ext
  apply Subtype.ext
  have hh : (b.val : G) ∈ B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) :=
    ⟨mem_map_of_mem H.subtype b.property,
      action_kernel_image_le D B hBM (mem_map_of_mem (H.subtype.comp B.subtype) hb)⟩
  exact mem_bot.mp (hfaith ▸ hh)

/-- The image calculation returns a three-group on the original Hall carrier. -/
theorem isThreeGroup_of_image {H : Subgroup G} (B : Subgroup H)
    (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hfaith : B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥)
    (hthree : IsPGroup 3 (action D B hBM).range) : IsPGroup 3 B := by
  exact hthree.of_injective (action D B hBM).rangeRestrict
    (fun _ _ h => action_injective D B hBM hfaith (congrArg Subtype.val h))

/-- A faithful norm-one-pair placement bounds the exponent of the whole Hall group. -/
theorem exponent_dvd_of_image_embedding {H : Subgroup G} (B : Subgroup H)
    (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hfaith : B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥)
    (n : ℕ) (f : (action D B hBM).range →* FiniteField.BinaryNormOne.torus n × FiniteField.BinaryNormOne.torus n)
    (hf : Function.Injective f) : Monoid.exponent B ∣ 2 ^ n + 1 := by
  apply (Monoid.exponent_dvd_of_monoidHom (f.comp (action D B hBM).rangeRestrict)
    (hf.comp (fun _ _ h => action_injective D B hBM hfaith
      (congrArg Subtype.val h)))).trans
  exact FiniteField.BinaryNormOne.pair_exponent_dvd n

end CFSG.Quasithin.Chapter10.CentralHall

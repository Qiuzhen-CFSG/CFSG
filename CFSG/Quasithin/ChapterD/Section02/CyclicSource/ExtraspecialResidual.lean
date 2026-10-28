module
public import Theory.Representation.ExtraspecialBinarySix.Residual
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Equivariant
public import Theory.GroupTheory.SubgroupCenterImageBound
public import Theory.ElementaryAbelian.ExtraspecialEquiv
import Mathlib.Tactic

/-!
# The extraspecial cyclic endpoint inside its original ambient actor

The odd kernel in a cyclic-source witness is its two-residual, hence is
characteristic. Inside a normal actor its image is therefore normal in the
original ambient group. The faithful binary residual theorem applies with
the unchanged involution, displacement and mapped center. This identifies
the literal embedded kernel with the ambient two-residual, without assuming
that the ambient quotient is a two-group.

Source: Aschbacher--Smith D.2.17(4), consumed in 15.1.2, printed p.1086.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {G V : Type u} [Group G] [Finite G]
 [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem odd_isTwoPerfect {H : Type*} [Group H] [Finite H]
    (hodd : Odd (Nat.card H)) : IsPPerfect 2 H := by
  intro N hn htwo
  let := hn
  apply index_eq_one.mp
  change Nat.card (H ⧸ N) = 1
  apply htwo.card_eq_or_dvd.resolve_right
  intro hd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (hd.trans N.card_quotient_dvd_card))

/-- The marked extraspecial kernel is the original ambient two-residual. -/
theorem LocalGeneration.extraspecial_ambient_residual
    {X : Type*} [Group X] [Finite X] (f : X →* G) (hf : Function.Surjective f)
    (hrank : primeRank 3 X ≤ 2)
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (K : Subgroup G) [K.Normal] (l : LocalGeneration (ρ.comp K.subtype)) :
    letI := BinaryGroupAction.action (ρ.comp K.subtype)
    letI : Finite V := Module.finite_of_finite (ZMod 2)
    letI : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
    letI := l.normal
    Section02.ExtraspecialEndpoint (V := Multiplicative V) l.kernel l.involution →
    l.kernel.map K.subtype = pResidual 2 G := by
  let := BinaryGroupAction.action (ρ.comp K.subtype)
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let := l.normal
  intro h
  let : l.kernel.Characteristic := characteristic_of_isPPerfect_quotient l.kernel
    (odd_isTwoPerfect (by rw [h.card_kernel]; decide))
    (isPGroup_quotient_of_sup_eq_top l.kernel (zpowers l.involution)
      (IsPGroup.of_card (n := 1) (by simp only [Nat.card_zpowers,l.order_two,pow_one]))
      l.generated)
  let P := l.kernel.map K.subtype
  let e := l.kernel.equivMapOfInjective K.subtype K.subtype_injective
  let : P.Normal := inferInstance
  let := h.kernel_extraspecial
  let : IsExtraspecial 3 P := IsExtraspecial.of_mulEquiv e h.kernel_extraspecial
  have hp : Nat.card P = 27 := (Nat.card_congr e.symm.toEquiv).trans h.card_kernel
  have hd : Module.finrank (ZMod 2) V = 6 := by
    have hc : Nat.card V = 64 := (Nat.card_congr Multiplicative.toAdd).symm.trans h.card_module
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [hc,Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) hh.symm
  have hz : ⁅(center P).map P.subtype,zpowers (l.involution : G)⁆ = ⊥ := by
    have hh := congrArg (fun A : Subgroup K => A.map K.subtype) h.fixes_center
    rw [map_commutator,map_subgroup_center_eq K.subtype K.subtype_injective,
      MonoidHom.map_zpowers,Subgroup.map_bot] at hh
    exact hh
  have hr : fixedCodim ρ (zpowers (l.involution : G)) ≤ 2 := by
    have hh := fixedCodim_map_equivariant (ρ.comp K.subtype) ρ K.subtype
      (LinearEquiv.refl (ZMod 2) V) (fun _ _ => rfl) (zpowers l.involution)
    rw [MonoidHom.map_zpowers] at hh
    exact hh ▸ l.codimension
  exact Representation.ExtraspecialBinarySix.normal_extraspecial_eq_twoResidual f hf hrank
    ρ hρ P hp hd l.involution ((orderOf_injective K.subtype K.subtype_injective _).trans l.order_two) hr hz
end CFSG.Quasithin.ChapterD.CyclicSource

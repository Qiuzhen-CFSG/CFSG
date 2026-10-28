module

public import Theory.Representation.AlternatingFiveInvolutionDisplacement
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# The chief-factor displacement step of 14.7.71

Consider an actual binary H-section A/B on C_H(U)/U, with the action
factored through the original star map H → H/O₂(H) ≃ S₅. The order-two
star image of Uα and the index-four intersection with U give index two
inside O₂(H). Its image in A/B therefore has dimension at most one.
The normalizer inclusions place every Uα-displacement in that image.
The A₅ displacement theorem forces K to centralize this same section.

The input index four and star order two are the earlier 14.7.69–70
conclusions for one chosen Uα. The normalizer bound comes from the original
conjugate centralizer Hα=N_G(Uα); C_H(U)≤O₂(H) follows from 14.5.15(4).
These earlier inputs are retained by qt-14-07 and its source owners.
No ambient G→S₅ map is used. The theorem does not construct the chief
sections or assert the remaining factor placement and counting in 14.7.71.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.71(1), printed p.1075 (PDF p.1092).
-/

public section

open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame

variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
private theorem imageSpace_card {H A B : Subgroup G}
    {ρ : Representation (ZMod 2) H W}
    (d : BinaryConjugationSection H A B ρ) (D : Subgroup G) (hDA : D ≤ A) :
    Nat.card (d.imageSpace D) = B.relIndex D := by
  change Nat.card ((D.subgroupOf A).map d.coordinates) = _
  rw [← relIndex_ker, d.kernel_eq]
  exact relIndex_subgroupOf hDA

/-- The original K centralizes any binary section on C_H(U)/U with the source star action. -/
theorem centralizer_section_centralized
    (H U Uα QH K A B : Subgroup G)
    (qH : H →* Equiv.Perm (Fin 5))
    (hqker : qH.ker = QH.subgroupOf H)
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 5)) W)
    (d : BinaryConjugationSection H A B (σ.comp qH))
    (hUQ : U ≤ QH) (hUαH : Uα ≤ H) (hKH : K ≤ H)
    (hAC : A ≤ H ⊓ centralizer (U : Set G)) (hUB : U ≤ B)
    (hCN : H ⊓ centralizer (U : Set G) ≤ normalizer Uα)
    (hCQ : H ⊓ centralizer (U : Set G) ≤ QH)
    (h70 : U.relIndex Uα = 4)
    (h69 : Nat.card ((Uα.subgroupOf H).map qH) = 2)
    (t : H) (ht : (t : G) ∈ Uα) (htord : orderOf (qH t) = 2)
    (hteven : qH t ∈ alternatingGroup (Fin 5))
    (hKeven : ∀ k : K, qH ⟨k, hKH k.property⟩ ∈ alternatingGroup (Fin 5)) :
    ⁅K, A⁆ ≤ B := by
  have hstar : QH.relIndex Uα = 2 := by
    rw [← relIndex_ker, hqker, relIndex_subgroupOf hUαH] at h69
    exact h69
  have hquot : U.relIndex (QH ⊓ Uα) = 2 := by
    have h := relIndex_inf_mul_relIndex U QH Uα
    rw [inf_eq_left.mpr hUQ, h70, hstar] at h
    omega
  let D := Uα ⊓ A
  have hD : D ≤ QH ⊓ Uα := le_inf (inf_le_right.trans (hAC.trans hCQ)) inf_le_left
  have hcard : Nat.card (d.imageSpace D) ≤ 2 := by
    rw [imageSpace_card d D inf_le_right]
    have hUD : U.relIndex D ≠ 0 := by
      intro hz
      have hdiv := relIndex_dvd_card U D
      rw [hz, zero_dvd_iff] at hdiv
      exact Nat.card_pos.ne' hdiv
    exact (relIndex_le_of_le_left hUB hUD).trans
      ((relIndex_le_of_le_right hD (by rw [hquot]; decide)).trans_eq hquot)
  have hdim : Module.finrank (ZMod 2) (d.imageSpace D) ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard
    by_contra hn
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ Module.finrank (ZMod 2)
      (d.imageSpace D) by omega)
    omega
  have hcomm : ⁅Uα, A⁆ ≤ D := le_inf
    (le_normalizer_iff_commutator_le_left.mp (hAC.trans hCN))
    (le_normalizer_iff_commutator_le_right.mp (hUαH.trans d.normalized))
  have hr := Submodule.finrank_mono
    (d.displacement_range_le_imageSpace_of_commutator_le Uα D hcomm t ht)
  let a : alternatingGroup (Fin 5) := ⟨qH t, hteven⟩
  have ha : orderOf a = 2 := (Subgroup.orderOf_coe a).symm.trans htord
  have htriv := AlternatingFiveInvolutionDisplacement.trivial_of_displacement_le_one
    (σ.comp (alternatingGroup (Fin 5)).subtype) a ha (hr.trans hdim)
  apply commutator_le.mpr
  intro k hk v hv
  let kH : H := ⟨k, hKH hk⟩
  let vA : A := ⟨v, hv⟩
  let c : A := (⟨k * v * k⁻¹,
    (mem_normalizer_iff.mp (d.normalized kH.property) v).mp hv⟩ : A) * vA⁻¹
  have hfix : σ (qH kH) = 1 := htriv ⟨qH kH, hKeven ⟨k, hk⟩⟩
  have he : d.coordinates c = 1 := by
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv]
    change (d.coordinates ⟨k * v * k⁻¹, _⟩).toAdd + -(d.coordinates vA).toAdd = 0
    rw [← sub_eq_add_neg, d.equivariant kH vA]
    change σ (qH kH) _ - _ = 0
    rw [hfix, Module.End.one_apply, sub_self]
  exact (d.coordinates_eq_one_iff c).mp he

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame

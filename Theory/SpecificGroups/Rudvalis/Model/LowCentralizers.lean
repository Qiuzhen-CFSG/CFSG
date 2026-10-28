module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Centralizer
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max6Action
public import Theory.SpecificGroups.Rudvalis.Model.SylowCenter
public import Theory.SpecificGroups.Rudvalis.Model.FivePointBase
public import Theory.GroupTheory.CentralizerEquivBounds

/-!
# The marked Rudvalis 2A centralizer and its small center

A short word conjugates the certified max6 involution to the square of the
second standard ATLAS generator. The equality is checked on the already
certified five-point base for the original permutation words.
Thus the identification concerns the literal marked element.

The five-block quotient of max6 is S5, with a two-group kernel. Since S5
has trivial center, the center of max6 is a two-group. It embeds in the
center of an ambient Sylow two-subgroup, whose center has at most two
elements. Finally the ambient centralizer of max6 lies in max6, because
max6 is itself the centralizer of its marked involution.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
Ru paragraph, manuscript p.17; GLS3 Table 5.3r. The original ATLAS words,
permutation conventions and attribution remain in the imported certificate
modules. Maximality is proved separately in LowCentralizers.Maximality.
-/

public section

open Subgroup
namespace Rudvalis.LowCentralizers
open SylowOvergroups CoreQuotients
open SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate

theorem max6_eq_centralizer : max6 = centralizer ({centralInvolution} : Set Model) :=
  le_antisymm CentralizerCertificate.max6_le_centralizer centralizer_le_max6

def squareConjugator : Model :=
  let g := a*b*a
  g⁻¹ * (centralInvolution * (g * b^2 * g⁻¹))^3

theorem squareConjugator_alignment :
    MulAut.conj squareConjugator centralInvolution = b^2 := by
  apply eq_of_smul_first_five
  decide +kernel

theorem max6_center_isPGroup : IsPGroup 2 (center max6) := by
  have hle : center max6 ≤ max6FiveAction.ker := by
    intro z hz
    apply MonoidHom.mem_ker.mpr
    have hc : max6FiveAction z ∈ center (Equiv.Perm (Fin 5)) := by
      apply mem_center_iff.mpr
      intro σ
      obtain ⟨x, rfl⟩ := max6FiveAction_surjective σ
      simpa only [map_mul] using congrArg max6FiveAction (mem_center_iff.mp hz x)
    rwa [Theory.SpecificGroups.SymmetricFive.center_eq_bot, mem_bot] at hc
  exact (IsPGroup.of_card (p := 2) (n := 11) max6FiveAction_kernel_card).of_injective
    (inclusion hle) (inclusion_injective hle)

theorem max6_center_card_le_two : Nat.card (center max6) ≤ 2 := by
  let P : Sylow 2 max6 := Classical.choice inferInstance
  have hc : Nat.card P = 16384 := by
    rw [P.card_eq_multiplicity, max6_card]
    decide +kernel
  let Q : Subgroup Model := (P : Subgroup max6).map max6.subtype
  have hQ : Nat.card Q = 16384 := by
    rw [card_map_of_injective max6.subtype_injective]
    exact hc
  have hodd : ¬ 2 ∣ Q.index := by
    intro h
    apply RadicalCoverage.SylowCertificate.not_two_pow_fifteen_dvd_card_model
    rw [← Q.card_mul_index, hQ]
    exact Nat.mul_dvd_mul_left 16384 h
  let S : Sylow 2 Model := (P.isPGroup'.map max6.subtype).toSylow hodd
  have hZP : center max6 ≤ P := max6_center_isPGroup.le_sylow_of_normal P
  let f : center max6 → center S := fun z =>
    ⟨⟨z.val.val, mem_map.mpr ⟨z.val, hZP z.property, rfl⟩⟩,
      mem_center_iff.mpr (by
        intro x
        obtain ⟨y, hy, he⟩ := mem_map.mp x.property
        apply Subtype.ext
        change x.val * z.val.val = z.val.val * x.val
        rw [← he]
        exact congrArg Subtype.val (mem_center_iff.mp z.property y))⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : center S => z.val.val) h
  exact (Nat.card_le_card_of_injective f hf).trans (SylowCenter.sylow_center_card_le_two S)

theorem max6_doubleCentralizer_card_le_two :
    Nat.card (centralizer (max6 : Set Model)) ≤ 2 := by
  have hz : centralInvolution ∈ max6 := centralInvolution_mem_max6
  have hle : centralizer (max6 : Set Model) ≤ max6 := by
    intro z hz'
    rw [max6_eq_centralizer]
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hz' _ hz).symm)
  let f : centralizer (max6 : Set Model) → center max6 := fun z =>
    ⟨⟨z.val, hle z.property⟩, mem_center_iff.mpr (by
      intro x
      apply Subtype.ext
      exact mem_centralizer_iff.mp z.property x.val x.property)⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : center max6 => z.val.val) h
  exact (Nat.card_le_card_of_injective f hf).trans max6_center_card_le_two
end Rudvalis.LowCentralizers

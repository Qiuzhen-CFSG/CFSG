module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.Inputs
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.LocalFacts

/-!
# A noncentral involution in the marked residual

Lift the marked three-cycle to c in Lᵥ. The commutator of z with c is the
nonzero module displacement z + zᶜ, so it has order two. Conjugation by c
moves it. This supplies an actual noncentral involution of Lᵥ; in particular
the cubic quotient alone cannot be mistaken for a cyclic residual.

Source: Aschbacher–Smith, the marked module on printed p.926 and the
A₄ deduction in 13.6.6, p.927, combined manuscript (1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
open A5Module BinaryPermutation.FiveCentralizerGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}

private def displacement : Space := z + act cubic z

private theorem displacement_moved : act cubic displacement ≠ displacement := by
  intro he
  have hh := congrArg (fun w : Space => w.val 3) he
  exact (by decide : (act cubic displacement).val 3 ≠ displacement.val 3) hh

/-- The actual residual contains an involution moved by another residual element. -/
theorem exists_residual_moved_involution (d : Setup κ T s) :
    ∃ x : Lv L (markedV s), orderOf x = 2 ∧ x ∉ center (Lv L (markedV s)) := by
  obtain ⟨c, hc, he⟩ := exists_residual_cubic s
  let D := L ⊓ Gv (markedV s)
  let zz : D := ⟨markedZ s, d.V_le_L (s.range_eq.le ⟨_, rfl⟩), markedZ_mem_Gv s⟩
  let r : D := zz * c * zz⁻¹ * c⁻¹
  have hr : r ∈ pResidual 2 D :=
    mul_mem ((inferInstance : (pResidual 2 D).Normal).conj_mem c hc zz) (inv_mem hc)
  have hz2 : (markedZ s) ^ 2 = 1 :=
    (orderOf_eq_prime_iff.mp (marked_orders s).1).1
  have hu : (r : G) = s.map (Multiplicative.ofAdd displacement) := by
    change markedZ s * (c : G) * (markedZ s)⁻¹ * (c : G)⁻¹ = _
    rw [inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hz2)]
    have hconj := s.equivariant (inclusion inf_le_left c) z
    rw [he] at hconj
    change (c : G) * markedZ s * (c : G)⁻¹ = _ at hconj
    calc
      _ = markedZ s * ((c : G) * markedZ s * (c : G)⁻¹) := by group
      _ = _ := by rw [hconj]; exact (s.map.map_mul _ _).symm
  let x : Lv L (markedV s) := ⟨r, ⟨r, hr, rfl⟩⟩
  have hxc : x ∉ center (Lv L (markedV s)) := by
    intro hx
    let cc : Lv L (markedV s) := ⟨c, ⟨c, hc, rfl⟩⟩
    have hcomm := congrArg Subtype.val (mem_center_iff.mp hx cc)
    change (c : G) * (r : G) = (r : G) * (c : G) at hcomm
    have hfix : MulAut.conj (c : G) (r : G) = r := by
      change (c : G) * (r : G) * (c : G)⁻¹ = r
      rw [hcomm, mul_inv_cancel_right]
    rw [hu] at hfix
    have hm := s.equivariant (inclusion inf_le_left c) displacement
    rw [he] at hm
    change MulAut.conj (c : G) (s.map (Multiplicative.ofAdd displacement)) = _ at hm
    rw [hm] at hfix
    exact displacement_moved (congrArg Multiplicative.toAdd (s.injective hfix))
  refine ⟨x, (orderOf_eq_prime_iff (p := 2)).mpr ⟨?_, ?_⟩, hxc⟩
  · apply Subtype.ext
    change (r : G) ^ 2 = 1
    rw [hu, ← map_pow, show (Multiplicative.ofAdd displacement) ^ 2 = 1 by decide +kernel,
      map_one]
  · intro hx
    apply hxc
    rw [hx]
    exact one_mem _

omit [Finite G] in
theorem three_dvd_card_residual (m : ModuleData s) : 3 ∣ Nat.card (Lv L (markedV s)) := by
  rw [← m.residual_quotient_card]
  exact (pCore 2 (Lv L (markedV s))).index_dvd_card

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix

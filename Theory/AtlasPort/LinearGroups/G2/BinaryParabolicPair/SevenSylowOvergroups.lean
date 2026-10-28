module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups.RecoveryShort
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups.RecoveryMiddle
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups.RecoveryLong


/-!
# Seven-divisible Sylow overgroups in the actual group G₂(2)′

Let K contain the positive-root Sylow subgroup restricted to the actual
commutator of the split-octonion automorphism group over F₂. If seven divides
its order, Cauchy's theorem supplies an element of order seven. Its derived
Bruhat factorization cannot use one of the first three Weyl cells, since
those lie in the two restricted parabolics of order 96. Every remaining even
representative recovers both cubic actors by the checked word certificates.
The Sylow subgroup and these actors generate both parabolics, and hence K
is the whole derived group.

No solvability, parabolic containment, unitary-model identification, or new
order or simplicity certification is assumed. This supplies the precise
seven-overgroup premise used by `ExceptionalGeneration.DerivedG2` in the
source reduction on Aschbacher–Smith, printed pp.1144–1145 (proof of 15.3.49).
The root conventions retain the ATLAS attribution through the imports;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups
open Subgroup BinaryCore SolvableSylowPlacement

private theorem small_cell (i : Fin 12) (hi : i.val < 3) (a b : Fin 2) :
    representative i a b ∈ firstParabolic ∨ representative i a b ∈ secondParabolic := by
  have hf := unipotent_le_firstParabolic shortRoot_mem_unipotent
  have hs := unipotent_le_parabolic shortRoot_mem_unipotent
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi' with rfl | rfl | rfl
  · left
    exact firstParabolic.mul_mem
      (firstParabolic.mul_mem (firstParabolic.pow_mem hf _) firstParabolic.one_mem)
      (firstParabolic.pow_mem hf _)
  · right
    exact secondParabolic.mul_mem
      (secondParabolic.mul_mem (secondParabolic.pow_mem hs _) weylR_mem_parabolic)
      (secondParabolic.pow_mem hs _)
  · left
    exact firstParabolic.mul_mem
      (firstParabolic.mul_mem (firstParabolic.pow_mem hf _) weylS_mem_firstParabolic)
      (firstParabolic.pow_mem hf _)

private theorem large_cell (K : Subgroup G) (hP : derivedSylowAmbient ≤ K)
    (i : Fin 12) (hi : 3 ≤ i.val) (a b : Fin 2) (hab : allowed i a b)
    (hg : representative i a b ∈ K) : cubicActor ∈ K ∧ movingActor ∈ K := by
  fin_cases i
  · exact False.elim ((by decide : ¬ 3 ≤ (0 : ℕ)) hi)
  · exact False.elim ((by decide : ¬ 3 ≤ (1 : ℕ)) hi)
  · exact False.elim ((by decide : ¬ 3 ≤ (2 : ℕ)) hi)
  · exact recover_cell_3 K hP a b hab hg
  · exact recover_cell_4 K hP a b hab hg
  · exact recover_cell_5 K hP a b hab hg
  · exact recover_cell_6 K hP a b hab hg
  · exact recover_cell_7 K hP a b hab hg
  · exact recover_cell_8 K hP a b hab hg
  · exact recover_cell_9 K hP a b hab hg
  · exact recover_cell_10 K hP a b hab hg
  · exact recover_cell_11 K hP a b hab hg


private theorem no_seven_in_parabolic (H : Subgroup DerivedModel) (hH : Nat.card H = 96)
    (x : DerivedModel) (hx : orderOf x = 7) : x ∉ H := by
  intro hm
  have hd := orderOf_dvd_natCard (⟨x,hm⟩ : H)
  rw [← Subgroup.orderOf_coe, hx, hH] at hd
  norm_num at hd

/-- A seven-divisible overgroup of the marked derived Sylow subgroup is the
whole actual commutator subgroup of the binary octonion automorphism group. -/
theorem eq_top_of_seven_dvd (K : Subgroup DerivedModel)
    (hP : (derivedSylow : Subgroup DerivedModel) ≤ K) (h7 : 7 ∣ Nat.card K) : K = ⊤ := by
  let E := K.map DerivedModel.subtype
  have hPE : derivedSylowAmbient ≤ E := by
    rw [← derivedSylow_map_subtype]
    exact map_mono hP
  have memK (x : DerivedModel) (hx : x.val ∈ E) : x ∈ K := by
    obtain ⟨y,hy,he⟩ := hx
    exact (Subtype.ext he : y = x) ▸ hy
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 7 h7
  have hx7 : orderOf x.val = 7 := (Subgroup.orderOf_coe x).trans hx
  obtain ⟨i,a,b,u,v,hu,hv,hab,he⟩ := derived_cover x.val
  have hrep : representative i a b ∈ E := by
    have hm := E.mul_mem (E.mul_mem (E.inv_mem (hPE hu))
      (mem_map_of_mem DerivedModel.subtype x.prop)) (E.inv_mem (hPE hv))
    change u⁻¹ * x.val.val * v⁻¹ ∈ E at hm
    simpa only [he, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hm
  have hi : 3 ≤ i.val := by
    by_contra h
    rcases small_cell i (by omega) a b with hf | hs
    · apply no_seven_in_parabolic derivedFirst card_derivedFirst x.val hx7
      change x.val.val ∈ firstParabolic
      rw [he]
      exact firstParabolic.mul_mem
        (firstParabolic.mul_mem (unipotent_le_firstParabolic hu.1) hf)
        (unipotent_le_firstParabolic hv.1)
    · apply no_seven_in_parabolic derivedSecond card_derivedSecond x.val hx7
      change x.val.val ∈ secondParabolic
      rw [he]
      exact secondParabolic.mul_mem
        (secondParabolic.mul_mem (unipotent_le_parabolic hu.1) hs)
        (unipotent_le_parabolic hv.1)
  obtain ⟨hc,hm⟩ := large_cell E hPE i hi a b hab hrep
  exact eq_top_of_actors K hP (memK _ hc) (memK _ hm)

end Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups

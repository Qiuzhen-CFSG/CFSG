module

public import Theory.GroupTheory.CentralCoprimeCardLift
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Involutions lifted modulo a two-core

A homomorphism with kernel central modulo O₂ descends to a central-kernel
map on G/O₂(G). That quotient has trivial two-core, so the central kernel
has odd order. Coprime correction lifts any involution to an element whose
square is in the original O₂(G). The image and quotient maps are unchanged.

Source application: Aschbacher–Smith, choice before13.7.10, printedp.941.
-/

@[expose] public section
open Subgroup
namespace MonoidHom
variable {G A : Type*} [Group G] [Finite G] [Group A]

/-- An involution modulo a kernel central above O₂ has a lift squaring into O₂. -/
theorem exists_square_mem_twoCore_lift (f : G →* A) (hf : Function.Surjective f)
    (hcore : pCore 2 G ≤ f.ker)
    (hcentral : f.ker.map (QuotientGroup.mk' (pCore 2 G)) ≤ center (G ⧸ pCore 2 G))
    (a : A) (ha : a ^ 2 = 1) :
    ∃ g : G, f g = a ∧ g ^ 2 ∈ pCore 2 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let fbar := QuotientGroup.lift (pCore 2 G) f hcore
  have hsurj : Function.Surjective fbar := by
    intro a
    obtain ⟨g, rfl⟩ := hf a
    exact ⟨q g, rfl⟩
  have hker : fbar.ker ≤ center (G ⧸ pCore 2 G) := by
    intro z hz
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) z
    exact hcentral (mem_map_of_mem q (show g ∈ f.ker from hz))
  have hodd : ¬ 2 ∣ Nat.card fbar.ker :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) fbar.ker hker
  have hcop : (Nat.card fbar.ker).Coprime 2 :=
    (Nat.prime_two.coprime_iff_not_dvd).mpr hodd |>.symm
  obtain ⟨x, hx, hs⟩ := fbar.exists_pow_eq_one_lift_of_central_coprime_ker
    hsurj hker hcop a ha
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) x
  exact ⟨g, hx, (QuotientGroup.eq_one_iff (g ^ 2)).mp (by
    change q (g ^ 2) = 1
    rw [map_pow]
    exact hs)⟩

end MonoidHom

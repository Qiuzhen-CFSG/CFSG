module

public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Automorphisms.Quotient

/-!
# Intrinsic power counts in the Frattini cosets

Counting elements whose square or fourth power is the identity gives five
colors on the binary quotient. These are intrinsic, so every automorphism
preserves the coloring certified in `Quotient`.

Source context: Aschbacher–Smith, printed p.511; GLS3, Table 5.3e.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.AutomorphismData
open Theory.GroupTheory

noncomputable def powerTag (g : candidate) : Fin 3 := by
  classical
  exact if g ^ 2 = 1 then 0 else if g ^ 4 = 1 then 1 else 2

theorem powerTag_map (f : MulAut candidate) (g : candidate) : powerTag (f g) = powerTag g := by
  classical
  have h2 : (f g) ^ 2 = 1 ↔ g ^ 2 = 1 := by rw [← map_pow, f.map_eq_one_iff]
  have h4 : (f g) ^ 4 = 1 ↔ g ^ 4 = 1 := by rw [← map_pow, f.map_eq_one_iff]
  simp only [powerTag, h2, h4]

theorem phi_square (j : Fin 64) : phi j ^ 2 = phi (squareIndex 0 j) := by
  simpa only [full, outer_zero, one_mul] using full_square 0 j

theorem full_fourth (i : Fin 16) (j : Fin 64) :
    full (i,j) ^ 4 = phi (squareIndex 0 (squareIndex i j)) := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, full_square, phi_square]

theorem powerTag_full (i : Fin 16) (j : Fin 64) :
    powerTag (full (i,j)) = powerLabel i j := by
  classical
  simp only [powerTag, full_square, full_fourth, phi_eq_one, powerLabel]

def counts : Fin 16 → Fin 3 → ℕ :=
  ![![48,16,0], ![0,64,0], ![32,32,0], ![0,0,64],
    ![32,32,0], ![16,48,0], ![0,64,0], ![0,64,0],
    ![16,48,0], ![0,64,0], ![16,48,0], ![16,48,0],
    ![0,64,0], ![0,64,0], ![0,64,0], ![16,48,0]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem counts_check : ∀ i a,
    (Finset.univ.filter (fun j : Fin 64 => powerLabel i j = a)).card = counts i a := by
  decide +kernel

theorem counts_distinguish : ∀ i j,
    counts i 0 = counts j 0 → counts i 2 = counts j 2 → color i = color j := by
  decide +kernel

theorem fiberProfile_counts (hcard : Nat.card candidate = 1024) (i : Binary) (a : Fin 3) :
    Subgroup.fiberProfile (fun g => quotientEquiv hcard (QuotientGroup.mk' _ g)) powerTag i a =
      counts i.val a := by
  classical
  let : Fintype candidate := Fintype.ofFinite candidate
  let E : (Fin 16 × Fin 64) ≃ candidate := Equiv.ofBijective full (full_bijective hcard)
  let P := fun p : Fin 16 × Fin 64 => p.1 = i.val ∧ powerLabel p.1 p.2 = a
  let R := fun g : candidate =>
    quotientEquiv hcard (QuotientGroup.mk' _ g) = i ∧ powerTag g = a
  have he : ∀ p, P p ↔ R (E p) := by
    intro ⟨u,v⟩
    change _ ↔ quotientEquiv hcard (QuotientGroup.mk' _ (full (u,v))) = i ∧
      powerTag (full (u,v)) = a
    rw [quotientEquiv_full, powerTag_full]
    cases i
    simp only [Binary.mk.injEq, P]
  let F : {p // P p} ≃ {j : Fin 64 // powerLabel i.val j = a} :=
    { toFun p := ⟨p.val.2, by simpa only [← p.property.1] using p.property.2⟩
      invFun j := ⟨(i.val,j.val), rfl, j.property⟩
      left_inv p := by apply Subtype.ext; exact Prod.ext p.property.1.symm rfl
      right_inv j := rfl }
  calc
    _ = Nat.card {g : candidate // R g} := by
      rw [Subgroup.fiberProfile_eq_card_filter, Nat.card_eq_fintype_card,
        Fintype.card_subtype]
    _ = Nat.card {p // P p} := (Nat.card_congr (E.subtypeEquiv he)).symm
    _ = Nat.card {j : Fin 64 // powerLabel i.val j = a} := Nat.card_congr F
    _ = (Finset.univ.filter (fun j : Fin 64 => powerLabel i.val j = a)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = counts i.val a := counts_check i.val a

theorem profile_color (hcard : Nat.card candidate = 1024) (i j : Binary)
    (h : Subgroup.fiberProfile (fun g => quotientEquiv hcard (QuotientGroup.mk' _ g)) powerTag i =
      Subgroup.fiberProfile (fun g => quotientEquiv hcard (QuotientGroup.mk' _ g)) powerTag j) :
    binaryColor i = binaryColor j := by
  apply counts_distinguish
  · simpa only [fiberProfile_counts] using congrFun h 0
  · simpa only [fiberProfile_counts] using congrFun h 2

end Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.AutomorphismData

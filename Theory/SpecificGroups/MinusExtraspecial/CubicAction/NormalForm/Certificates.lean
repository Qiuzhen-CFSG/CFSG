module

public import Theory.SpecificGroups.MinusExtraspecial.CubicAction.NormalForm.Data

/-!
# Checked cubic automorphism coverage and conjugating maps

Presentation relations prune the search through four generator images.
Every nonidentity cubic tuple satisfying these necessary relations occurs
in the table. Independently, each table row satisfies multiplication by
all four generators, both inverse identities, and the conjugacy equation
on all 32 elements. Both checks use kernel reduction.

Source: Aschbacher, *Sporadic Groups* (1994), 47.5, p.263, and p.265.
-/

@[expose] public section
namespace MinusExtraspecial.CubicAction.NormalForm

def covered (a : Images) : Bool := rows.any fun t => decide (t.a = a)

/-- The nested implications prune impossible partial generator tuples early. -/
def Coverage (u : B) : Prop :=
  mul u u ≠ 0 → ∀ v : B,
  mul v v = mul u u → mul v u = mul (inv u) v → ∀ r : B,
  mul r r = 0 → mul r u = mul u r → mul r v = mul v r → ∀ s : B,
  mul s s = 0 → mul s u = mul u s → mul s v = mul v s →
  mul s r = mul (mul (mul u u) r) s →
  cubic ⟨u, v, r, s⟩ → nontrivial ⟨u, v, r, s⟩ → covered ⟨u, v, r, s⟩

def coverageCheck (u : B) : Bool :=
  if mul u u ≠ 0 then all.all fun v =>
    if mul v v = mul u u ∧ mul v u = mul (inv u) v then all.all fun r =>
      if mul r r = 0 ∧ mul r u = mul u r ∧ mul r v = mul v r then all.all fun s =>
        if mul s s = 0 ∧ mul s u = mul u s ∧ mul s v = mul v s ∧
            mul s r = mul (mul (mul u u) r) s then
          if cubic ⟨u, v, r, s⟩ ∧ nontrivial ⟨u, v, r, s⟩ then covered ⟨u, v, r, s⟩
          else true
        else true
      else true
    else true
  else true

theorem coverage_of_check (u : B) (h : coverageCheck u) : Coverage u := by
  intro hu v hv hvu r hr hru hrv s hs hsu hsv hsr hc hn
  simp only [coverageCheck, if_pos hu] at h
  have h := List.all_eq_true.mp h v (mem_all v)
  simp only [hv, hvu, and_self, ↓reduceIte] at h
  have h := List.all_eq_true.mp h r (mem_all r)
  simp only [hr, hru, hrv, and_self, ↓reduceIte] at h
  have h := List.all_eq_true.mp h s (mem_all s)
  simpa only [hs, hsu, hsv, hsr, hc, hn, and_self, ↓reduceIte] using h

-- These reductions are deliberately sequential. The original simultaneous
-- full-table reductions exceeded the compiler's 8 GiB memory guard.
set_option Elab.async false in
private theorem coverage_checked : all.all coverageCheck := by decide +kernel

/-- Exhaustiveness of the eighty rows, without enumerating arbitrary functions. -/
theorem coverage_all (u : B) : Coverage u :=
  coverage_of_check u (List.all_eq_true.mp coverage_checked u (mem_all u))

set_option Elab.async false in
private theorem rows_first : (rows.take 20).all rowCheck := by decide +kernel
set_option Elab.async false in
private theorem rows_second : ((rows.drop 20).take 20).all rowCheck := by decide +kernel
set_option Elab.async false in
private theorem rows_third : ((rows.drop 40).take 20).all rowCheck := by decide +kernel
set_option Elab.async false in
private theorem rows_fourth : (rows.drop 60).all rowCheck := by decide +kernel

/-- Every proposed conjugator is checked on the full model coordinates. -/
theorem rows_valid : rows.all rowCheck := by
  have h := Bool.and_eq_true_iff.mpr ⟨rows_first,
    Bool.and_eq_true_iff.mpr ⟨rows_second, Bool.and_eq_true_iff.mpr ⟨rows_third, rows_fourth⟩⟩⟩
  change ((rows.take 20 ++ (rows.drop 20).take 20 ++
    (rows.drop 40).take 20 ++ rows.drop 60).all rowCheck) = true
  simpa only [List.all_append, Bool.and_assoc] using h

end MinusExtraspecial.CubicAction.NormalForm

module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The action on a normal closure of a Sylow-central subgroup

If a Sylow p-subgroup centralizes Z, its conjugation action on the normal
closure E of Z has trivial p-core. Pull the p-core back from the action
image. Its elements act like Sylow elements on E, so they centralize Z.
The pullback is normal, hence its centralizer contains the normal closure E.
Faithfulness of the action image then kills the p-core.

This is the automizer reduction in Janko–Thompson, Math. Z. 113 (1970),
Lemma 3.1, printed pp.387–388; the result needs neither solvability nor
an elementary abelian hypothesis.
-/

open Subgroup

/-- The action on the normal closure of a Sylow-central subgroup has
trivial p-core. -/
public theorem pCore_conjNormal_range_eq_bot_of_normalClosure {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (P : Sylow p G) (Z E : Subgroup G) [E.Normal]
    (hE : E = normalClosure (Z : Set G))
    (hZP : Z ≤ centralizer (P : Set G)) :
    pCore p (MulAut.conjNormal (H := E) : G →* MulAut E).range = ⊥ := by
  let f : G →* MulAut E := MulAut.conjNormal
  let Q := P.mapSurjective f.rangeRestrict_surjective
  let K := (pCore p f.range).comap f.rangeRestrict
  have hQ : pCore p f.range ≤ (Q : Subgroup f.range) :=
    pCore_isPGroup.le_sylow_of_normal Q
  have hZE : Z ≤ E := hE ▸ le_normalClosure
  have hZK : Z ≤ centralizer (K : Set G) := by
    intro z hz k hk
    obtain ⟨t, ht, he⟩ := hQ hk
    have htfix : t * z * t⁻¹ = z := by
      have hc := hZP hz t ht
      calc
        t * z * t⁻¹ = z * t * t⁻¹ := by rw [hc]
        _ = z := mul_inv_cancel_right _ _
    have heval := congrArg (fun a : f.range => (a : MulAut E) ⟨z, hZE hz⟩) he
    have heval' := congrArg Subtype.val heval
    change t * z * t⁻¹ = k * z * k⁻¹ at heval'
    have hkfix : k * z * k⁻¹ = z := heval'.symm.trans htfix
    exact mul_inv_eq_iff_eq_mul.mp hkfix
  have hEK : E ≤ centralizer (K : Set G) := by
    rw [hE]
    exact normalClosure_le_normal hZK
  apply bot_unique
  intro a ha
  apply mem_bot.mpr
  apply Subtype.ext
  obtain ⟨k, hk⟩ := a.property
  have hkK : k ∈ K := by
    change f.rangeRestrict k ∈ pCore p f.range
    have he : f.rangeRestrict k = a := Subtype.ext hk
    rwa [he]
  rw [← hk]
  ext e
  change k * (e : G) * k⁻¹ = e
  have hc := hEK e.property k hkK
  rw [hc, mul_inv_cancel_right]

module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Normal closures through a normal supplement

If `G = ES` with `E` normal and `B ≤ E` normalized by `S`, then
the normal closure of `B` in `G` equals its normal closure inside `E`,
mapped back to `G`.

Every ambient conjugator factors as `e*s`; the `s` factor preserves
`B`, so each ambient conjugate already lies in the closure inside `E`.
The reverse inclusion follows from the normal-closure universal property.

This elementary transfer is used in Stellmacher (4.6) to apply (2.3) to
`E = O²(Pstar)O₂(C)` while retaining the normal closures defined in
`Pstar`; see `refs/latex/stellmacher-n-group.tex`.
-/

/-- A normal supplement that normalizes the generators does not enlarge
their normal closure. -/
public theorem Subgroup.normalClosure_eq_map_of_normal_supplement
    {G : Type*} [Group G] (E S B : Subgroup G) [E.Normal]
    (hgen : E ⊔ S = ⊤) (hBE : B ≤ E)
    (hSB : S ≤ Subgroup.normalizer (B : Set G)) :
    Subgroup.normalClosure (B : Set G) =
      (Subgroup.normalClosure (B.subgroupOf E : Set E)).map E.subtype := by
  apply le_antisymm
  · apply (Subgroup.closure_le (K :=
      (Subgroup.normalClosure (B.subgroupOf E : Set E)).map E.subtype)).mpr
    intro x hx
    obtain ⟨b, hb, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    have hg : g ∈ E ⊔ S := by rw [hgen]; trivial
    obtain ⟨e, he, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    have hsbs : s * b * s⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hSB hs) b).mp hb
    let bE : E := ⟨s * b * s⁻¹, hBE hsbs⟩
    let eE : E := ⟨e, he⟩
    have hbN : bE ∈ Subgroup.normalClosure (B.subgroupOf E : Set E) :=
      Subgroup.le_normalClosure hsbs
    have hconjN := (Subgroup.normalClosure_normal (s := (B.subgroupOf E : Set E))).conj_mem
      bE hbN eE
    refine ⟨eE * bE * eE⁻¹, hconjN, ?_⟩
    simp [eE, bE, mul_assoc]
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply Subgroup.normalClosure_le_normal
    intro b hb
    exact Subgroup.le_normalClosure hb

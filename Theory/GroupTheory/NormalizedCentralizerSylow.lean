module
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# Centralizers normalized by an embedded Sylow subgroup

Suppose S is the image in G of a Sylow p-subgroup of N, and S normalizes Z.
Then S ∩ C_G(Z) is the image of a Sylow p-subgroup of N ∩ C_G(Z).
The Sylow subgroup of N normalizes its relative centralizer of Z, so the
normalized-subgroup intersection theorem applies inside N. Transport through
the literal subgroup inclusions gives the ambient intersection formula.

This is the standard Sylow-intersection argument used in Aschbacher–Smith,
proof of Lemma 2.4.21, printed p.536, after their Lemma 2.4.17(1).
-/

public section
open Subgroup

/-- An embedded Sylow subgroup restricts to the centralizer of any subgroup
that it normalizes, with the result expressed through the ambient inclusion. -/
theorem Subgroup.exists_sylow_centralizer_of_normalizes
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N S Z : Subgroup G) (P : Sylow p N)
    (hP : (P : Subgroup N).map N.subtype = S)
    (hSZ : S ≤ normalizer (Z : Set G)) :
    ∃ Q : Sylow p (N ⊓ centralizer (Z : Set G) : Subgroup G),
      (Q : Subgroup (N ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (N ⊓ centralizer (Z : Set G)).subtype = S ⊓ centralizer (Z : Set G) := by
  let K := N ⊓ centralizer (Z : Set G)
  have hSN : S ≤ N := hP ▸ map_subtype_le (P : Subgroup N)
  have hCZ : normalizer (Z : Set G) ≤ normalizer (centralizer (Z : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (Z : Set G))).mp
      inferInstance
  have hSK : S ≤ normalizer (K : Set G) :=
    (le_inf (hSN.trans N.le_normalizer)
      (hSZ.trans hCZ)).trans
      inf_normalizer_le_normalizer_inf
  have hPK : (P : Subgroup N) ≤ normalizer (K.subgroupOf N : Set N) := by
    intro x hx
    rw [← subgroupOf_normalizer_eq (show K ≤ N from inf_le_left)]
    exact hSK (hP ▸ mem_map_of_mem N.subtype hx)
  obtain ⟨Q,hQ⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow
    P (K.subgroupOf N) hPK
  let e := subgroupOfEquivOfLe (show K ≤ N from inf_le_left)
  let Q' : Sylow p K := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Q', ?_⟩
  change ((Q : Subgroup (K.subgroupOf N)).map e.toMonoidHom).map K.subtype = _
  rw [hQ]
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨hP ▸ mem_map_of_mem N.subtype hz, z.property.2⟩
  · intro hx
    obtain ⟨y,hy,he⟩ := hP.symm ▸ hx.1
    refine ⟨⟨x,hSN hx.1,hx.2⟩,?_,rfl⟩
    refine ⟨⟨⟨x,hSN hx.1⟩,hSN hx.1,hx.2⟩,?_,rfl⟩
    exact (Subtype.ext he : y = ⟨x,hSN hx.1⟩) ▸ hy


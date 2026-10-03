module

public import Mathlib.Combinatorics.Configuration

/-!
# The full incidence collineation group

A collineation is a pair of permutations preserving incidence in both directions.
Keeping the two permutations separate also allows points and line covectors to
have the same underlying type, as in the orthogonality model of a projective plane.
The group law is composition on both components.
-/

namespace Configuration

variable (P L : Type*) [Membership P L]

/-- All pairs of permutations preserving the incidence relation. -/
@[expose] public def collineationSubgroup : Subgroup (Equiv.Perm P × Equiv.Perm L) where
  carrier := {g | ∀ p l, g.1 p ∈ g.2 l ↔ p ∈ l}
  one_mem' := by intro p l; rfl
  mul_mem' := by
    intro a b ha hb p l
    exact (ha (b.1 p) (b.2 l)).trans (hb p l)
  inv_mem' := by
    intro a ha p l
    simpa using (ha (a.1.symm p) (a.2.symm l)).symm

/-- The full group of incidence collineations. -/
public abbrev Collineation := collineationSubgroup P L

namespace Collineation

/-- The permutation of points underlying a collineation. -/
@[expose] public def pointHom : Collineation P L →* Equiv.Perm P :=
  (MonoidHom.fst _ _).comp (collineationSubgroup P L).subtype

/-- The permutation of lines underlying a collineation. -/
@[expose] public def lineHom : Collineation P L →* Equiv.Perm L :=
  (MonoidHom.snd _ _).comp (collineationSubgroup P L).subtype

variable {P L}

public theorem mem_iff (g : Collineation P L) (p : P) (l : L) :
    pointHom P L g p ∈ lineHom P L g l ↔ p ∈ l := g.property p l

@[ext] public theorem ext {g h : Collineation P L}
    (hp : ∀ p, pointHom P L g p = pointHom P L h p)
    (hl : ∀ l, lineHom P L g l = lineHom P L h l) : g = h :=
  Subtype.ext (Prod.ext (Equiv.ext hp) (Equiv.ext hl))

/-- In a finite projective plane, the point permutation determines the line permutation. -/
public theorem ext_points [Finite P] [Finite L] [ProjectivePlane P L]
    {g h : Collineation P L}
    (hp : ∀ p, pointHom P L g p = pointHom P L h p) : g = h := by
  apply ext hp
  intro l
  let := Fintype.ofFinite {p : P // p ∈ l}
  have hcard : 1 < Fintype.card {p : P // p ∈ l} := by
    rw [← Nat.card_eq_fintype_card]
    exact lt_trans (by omega) (ProjectivePlane.two_lt_pointCount P l)
  obtain ⟨p, q, hpq⟩ := Fintype.one_lt_card_iff.mp hcard
  have hpg := (mem_iff g p.val l).mpr p.property
  have hqg := (mem_iff g q.val l).mpr q.property
  have hph := (mem_iff h p.val l).mpr p.property
  have hqh := (mem_iff h q.val l).mpr q.property
  rw [← hp p.val] at hph
  rw [← hp q.val] at hqh
  exact (Nondegenerate.eq_or_eq hpg hqg hph hqh).resolve_left
    (fun heq => hpq (Subtype.ext ((pointHom P L g).injective heq)))

end Collineation
end Configuration

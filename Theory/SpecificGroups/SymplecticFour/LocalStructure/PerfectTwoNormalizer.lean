module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectSubgroups
public import Theory.GroupTheory.PerfectAutomorphismStabilizer
/-!
# Perfect groups inside symplectic two-local normalizers

The common-fixed-space geometry puts the normalizer of every nontrivial
two-subgroup in a point or plane parabolic. Each perfect subgroup of such a
parabolic has odd-prime rank at most one. Thus a faithful perfect group of
odd-prime rank two cannot normalize a nontrivial two-subgroup.

This is the symplectic normalizer obstruction needed in Aschbacher--Smith
C.4.5--7, printed pp.152--153. No radical or full Sylow hypothesis is needed.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem no_perfect_odd_rank_two_in_two_normalizer
    (P : Subgroup (Sp F)) (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : 2 ≤ primeRank p A)
    (f : A →* Sp F) (hf : Function.Injective f)
    (hn : f.range ≤ normalizer (P : Set (Sp F))) : False := by
  obtain ⟨g,hg⟩ := twoLocal_parabolic_cover_of_charTwo
    (normalizer (P : Set (Sp F))) ⟨P,hne,hp,rfl⟩
  let j := (MulAut.conj g).toMonoidHom.comp f
  apply no_perfect_odd_rank_two_in_parabolic ho hr j ((MulAut.conj g).injective.comp hf)
  have hj : j.range ≤ (normalizer (P : Set (Sp F))).map (MulAut.conj g).toMonoidHom := by
    rintro _ ⟨a,rfl⟩
    exact mem_map_of_mem _ (hn ⟨a,rfl⟩)
  exact hg.elim (fun h => Or.inl (hj.trans h)) (fun h => Or.inr (hj.trans h))


/-- The same bound for the actual automorphism stabilizer. Soluble outers
make every perfect actor inner; centerlessness makes that realization faithful. -/
theorem perfect_automorphism_stabilizer_odd_rank_le_one
    (P : Subgroup (Sp F)) (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (A : Subgroup (MulAut (Sp F))) [Group.IsPerfect A]
    [Group.IsSolvable (MulAut.Outer (Sp F))]
    (hA : A ≤ MulAction.stabilizer (MulAut (Sp F)) P)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) : primeRank p A ≤ 1 := by
  obtain ⟨f,hf,hconj⟩ := MulAut.perfect_subgroup_exists_inner_lift A
    (EvenProjective.center_eq_bot (F := F))
  by_contra! hb
  apply no_perfect_odd_rank_two_in_two_normalizer P hp hne ho (by omega) f hf
  rintro _ ⟨a,rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [hconj a]
  exact hA a.property
end Theory.SpecificGroups.SymplecticFour

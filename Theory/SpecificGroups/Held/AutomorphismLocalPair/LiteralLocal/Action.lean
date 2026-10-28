module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.Representative
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankSixCertificate.Data

/-!
# The literal Held seed and its twelve generators

We concatenate the six generators of catalogue row 20 and the six of row 21.
Their closure is the unchanged literal seed. The associated permutations use
previously certified tables for the four Sylow generators. Commuting with these
twelve permutations is therefore exactly the ambient centralizer condition.

Source: the ATLAS degree-2058 Held action; GLS3 Table 5.3p and the local pair
used in Aschbacher--Smith, printed p.526.
-/

@[expose] public section
namespace Held.AutomorphismLocalPair.LiteralLocal
open Subgroup TwoLocalCandidates.MaximalNormalizerCatalogue

abbrev Vertex := Fin 2058

def seedGen (i : Fin 12) : He :=
  RankSixCertificate.gen ⟨i.val / 6, by omega⟩ ⟨i.val % 6, Nat.mod_lt _ (by decide)⟩

def seedPerm (i : Fin 12) : Equiv.Perm Vertex :=
  RankSixCertificate.perm ⟨i.val / 6, by omega⟩ ⟨i.val % 6, Nat.mod_lt _ (by decide)⟩

theorem seedPerm_eq (i : Fin 12) : seedPerm i = representation (seedGen i) :=
  RankSixCertificate.perm_eq _ _

theorem seedGen_mem (i : Fin 12) : seedGen i ∈ representativeLargeSeed := by
  have h := RankSixCertificate.gen_mem
    (⟨i.val / 6, by omega⟩ : Fin 2) ⟨i.val % 6, Nat.mod_lt _ (by decide)⟩
  change seedGen i ∈ ambient (RankSixCertificate.row _) at h
  unfold RankSixCertificate.row at h
  split_ifs at h with hi
  · exact (show ambient 20 ≤ representativeLargeSeed from le_sup_left) h
  · exact (show ambient 21 ≤ representativeLargeSeed from le_sup_right) h

theorem seed_le_of_generators (K : Subgroup He) (h : ∀ i, seedGen i ∈ K) :
    representativeLargeSeed ≤ K := by
  apply sup_le
  · rw [show (20 : Fin 22) = RankSixCertificate.row 0 from rfl,
      RankSixCertificate.ambient_eq_closure]
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    have he : seedGen ⟨i.val, by omega⟩ = RankSixCertificate.gen 0 i := by
      unfold seedGen
      congr 1 <;> apply Fin.ext <;> simp
    rw [← he]
    exact h _
  · rw [show (21 : Fin 22) = RankSixCertificate.row 1 from rfl,
      RankSixCertificate.ambient_eq_closure]
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    have he : seedGen ⟨i.val + 6, by omega⟩ = RankSixCertificate.gen 1 i := by
      unfold seedGen
      congr 1 <;> apply Fin.ext <;> simp
    rw [← he]
    exact h _

def seedWord (w : List (Fin 12)) : He := (w.map seedGen).prod

def seedPermWord (w : List (Fin 12)) : Equiv.Perm Vertex := (w.map seedPerm).prod

theorem seedWord_mem (w : List (Fin 12)) : seedWord w ∈ representativeLargeSeed := by
  apply list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact seedGen_mem i

theorem seedPermWord_eq (w : List (Fin 12)) :
    seedPermWord w = representation (seedWord w) := by
  simp only [seedPermWord, seedWord, map_list_prod, List.map_map, Function.comp_def,
    show seedPerm = fun i => representation (seedGen i) from funext seedPerm_eq]

theorem mem_centralizer_iff_generators (x : He) :
    x ∈ centralizer (representativeLargeSeed : Set He) ↔
      ∀ i, seedGen i * x = x * seedGen i := by
  constructor
  · intro hx i
    exact hx _ (seedGen_mem i)
  · intro hx y hy
    have hle : representativeLargeSeed ≤ centralizer ({x} : Set He) := by
      apply seed_le_of_generators
      intro i
      exact mem_centralizer_singleton_iff.mpr (hx i)
    exact mem_centralizer_singleton_iff.mp (hle hy)

def CommutesGenerators (σ : Equiv.Perm Vertex) : Prop :=
  ∀ i x, σ (seedPerm i x) = seedPerm i (σ x)

theorem centralizer_commutes {x : He}
    (hx : x ∈ centralizer (representativeLargeSeed : Set He)) :
    CommutesGenerators (representation x) := by
  intro i v
  rw [seedPerm_eq]
  exact (congrArg (fun g : He => representation g v)
    ((mem_centralizer_iff_generators x).mp hx i)).symm

def walk : List (Fin 12) → Vertex → Vertex
  | [], x => x
  | i :: w, x => walk w (seedPerm i x)

theorem walk_commute (σ : Equiv.Perm Vertex) (hσ : CommutesGenerators σ)
    (w : List (Fin 12)) (x : Vertex) : σ (walk w x) = walk w (σ x) := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih => simp only [walk, ih, hσ i]

end Held.AutomorphismLocalPair.LiteralLocal

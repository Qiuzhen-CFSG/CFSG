module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Theory.GroupAction.SubgroupConjugation

/-!
# Transitivity of the natural alternating-six module

The fifteen nonzero vectors of the binary natural module are its duad
classes. Double transitivity of A₆ carries any such class to any other.
Transport through a marked conjugation representation produces conjugators
in the original acting subgroup, retaining its literal normalizer map.

Source application: Aschbacher–Smith 14.3.19(6)–(7), printed p.997.
-/

@[expose] public noncomputable section
namespace BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

/-- The literal natural A₆ module has one orbit on nonzero vectors. -/
theorem alternatingSix_natural_nonzero_transitive
    (v w : natural (Fin 6)) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : alternatingGroup (Fin 6), naturalRepresentation (Fin 6) g.val v = w := by
  obtain ⟨d,rfl⟩ := (vector_cases v).resolve_left hv
  obtain ⟨f,rfl⟩ := (vector_cases w).resolve_left hw
  have := alternatingGroup.isMultiplyPretransitive (Fin 6)
  have ht : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin 6) - 2)
      (by simp) (Nat.sub_le _ _)
  obtain ⟨g,hi,hj⟩ := MulAction.is_two_pretransitive_iff.mp ht
    (ne_of_lt d.property) (ne_of_lt f.property)
  refine ⟨g,?_⟩
  change naturalRepresentation (Fin 6) g.val (pairVector d.val.1 d.val.2) =
    pairVector f.val.1 f.val.2
  rw [pairVector_map,show g.val d.val.1 = f.val.1 from hi,
    show g.val d.val.2 = f.val.2 from hj]

open Subgroup in
/-- A marked natural action supplies conjugators in the actual acting subgroup. -/
theorem exists_conjugator_of_alternatingSix_natural_action
    {G : Type*} [Group G] (A K : Subgroup G) (hn : K ≤ normalizer (A:Set G))
    (e : (A.normalizerMonoidHom.comp (inclusion hn)).range ≃* alternatingGroup (Fin 6))
    (q : A ≃* Multiplicative (natural (Fin 6)))
    (he : ∀ (a : (A.normalizerMonoidHom.comp (inclusion hn)).range) (v : A),
      (q (a.val v)).toAdd = naturalRepresentation (Fin 6) (e a).val (q v).toAdd)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ k ∈ K, k * (a:G) * k⁻¹ = b := by
  have hqa : (q a).toAdd ≠ 0 := fun h => ha (q.injective (h.trans q.map_one.symm))
  have hqb : (q b).toAdd ≠ 0 := fun h => hb (q.injective (h.trans q.map_one.symm))
  obtain ⟨s,hs⟩ := alternatingSix_natural_nonzero_transitive _ _ hqa hqb
  obtain ⟨k,hk⟩ := (e.symm s).property
  refine ⟨k,k.property,?_⟩
  have hh := he (e.symm s) a
  rw [e.apply_symm_apply,hs] at hh
  have hh' : (e.symm s).val a = b := q.injective (Multiplicative.toAdd.injective hh)
  rw [←hk] at hh'
  exact congrArg Subtype.val hh'
end BinaryPermutation

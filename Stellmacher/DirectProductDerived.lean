module

public import Stellmacher.SectionsOneToFourDefs
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.Commutator.Finite

/-!
# Derived subgroups of an internal product family

The derived subgroup of a finite internal product family is the internal
product of the factors' derived subgroups, with the same index type. The
ambient group itself need not be finite. The result uses the project's
generation, pairwise disjointness, and pairwise commutation predicate
without asserting stronger independence data.

The external product's coordinate homomorphism maps its derived subgroup
onto the ambient derived subgroup. Coordinate projections put each entry
in the corresponding factor's derived subgroup, giving one generation
containment; commutator monotonicity gives the other. Disjointness and
commutation descend from the original family.

This is the product algebra used for the order-three factors in
Stellmacher (9.10)(3), printed p.57 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher

public theorem IsInternalDirectProductFamily.derived
    {G ι : Type*} [Group G] [Finite ι]
    {E : Subgroup G} {D : ι → Subgroup G}
    (hprod : IsInternalDirectProductFamily E D) :
    IsInternalDirectProductFamily ((commutator E).map E.subtype)
      (fun i => (commutator (D i)).map (D i).subtype) := by
  classical
  let _ := Fintype.ofFinite ι
  let P := ∀ i, D i
  let F (i : ι) : Subgroup G := (commutator (D i)).map (D i).subtype
  have hcomm : Pairwise (fun i j : ι => ∀ x y : G,
      x ∈ D i → y ∈ D j → Commute x y) := by
    intro i j hij x y hx hy
    exact hprod.2.2 i j hij x hx y hy
  let f : P →* G := Subgroup.noncommPiCoprod hcomm
  have hf : f.range = E :=
    (Subgroup.noncommPiCoprod_range).trans hprod.1.symm
  have hmap : (commutator P).map f = (commutator E).map E.subtype := by
    rw [map_commutator_eq, hf, Subgroup.map_subtype_commutator]
  refine ⟨le_antisymm ?_ ?_, ?_, ?_⟩
  · rw [← hmap]
    rintro x ⟨p, hp, rfl⟩
    rw [Subgroup.noncommPiCoprod_apply]
    apply Subgroup.noncommProd_mem
    intro i _hi
    apply (le_iSup F i)
    have hpi : p i ∈ commutator (D i) := by
      have hm := Subgroup.mem_map_of_mem
        (Pi.evalMonoidHom (fun i : ι => D i) i) hp
      rw [map_commutator_eq] at hm
      exact Subgroup.commutator_mono le_top le_top hm
    exact Subgroup.mem_map_of_mem (D i).subtype hpi
  · apply iSup_le
    intro i
    dsimp only
    rw [Subgroup.map_subtype_commutator, Subgroup.map_subtype_commutator]
    have hDiE : D i ≤ E := by
      rw [hprod.1]
      exact le_iSup D i
    exact Subgroup.commutator_mono hDiE hDiE
  · intro i j hij
    exact (hprod.2.1 i j hij).mono (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _)
  · intro i j hij x hx y hy
    exact hprod.2.2 i j hij x (Subgroup.map_subtype_le _ hx)
      y (Subgroup.map_subtype_le _ hy)

end Stellmacher

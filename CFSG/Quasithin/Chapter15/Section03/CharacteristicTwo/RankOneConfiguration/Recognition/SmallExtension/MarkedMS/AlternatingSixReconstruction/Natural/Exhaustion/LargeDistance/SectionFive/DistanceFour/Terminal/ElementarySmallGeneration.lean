module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementarySmallOpposite
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.DLattice.Cube

/-!
# Generation from a non-line subgroup of an elementary cube

The quotient image of a pair of distinct small kernels is a subgroup of the
three-pair cube.  Once its order is greater than two, the explicit subgroup
lattice of that cube gives the generation required in MS93 (5.6)(a): it
generates the whole symmetric-six image together with one fixed compatible
conjugate cube.  The proof is a finite certificate over the sixteen entries of
`dLattice`; conjugation then transports it to every marked cube.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.6)(a), printed p.917.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal

local notation "S" => Equiv.Perm (Fin 6)
/-- The fixed compatible conjugator used by the finite cube certificate. -/
def elementaryDConjugator : S := Equiv.swap 1 2 * Equiv.swap 3 4
private abbrev k : S := elementaryDConjugator
private abbrev D' : Subgroup S := (D 6).map (MulAut.conj k).toMonoidHom

private def chain : Fin 16 → S :=
  ![1, 1, 1, 1, 1, 1, 1, 1,
    Equiv.swap 4 1 * Equiv.swap 1 5 * Equiv.swap 1 2,
    Equiv.swap 3 4 * Equiv.swap 1 2,
    Equiv.swap 3 5 * Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 1 2,
    Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 1 2,
    Equiv.swap 3 4 * Equiv.swap 1 2,
    Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 1 2,
    Equiv.swap 3 4 * Equiv.swap 1 2,
    Equiv.swap 3 4 * Equiv.swap 1 2]

private theorem chain_generates (v : S) (N : Subgroup S)
    (hv : ∀ i : Fin 5,
      (MulAut.conj v) (Equiv.swap i.castSucc i.succ) ∈ N) : N = ⊤ := by
  apply top_unique
  have hh := congrArg (Subgroup.map (MulAut.conj v).toMonoidHom)
    (Subgroup.closure_eq_top_of_mclosure_eq_top
      (Equiv.Perm.mclosure_swap_castSucc_succ 5))
  rw [map_top_of_surjective (MulAut.conj v).toMonoidHom
      (MulAut.conj v).surjective] at hh
  rw [← hh, Subgroup.map_le_iff_le_comap, closure_le]
  rintro _ ⟨i, rfl⟩
  exact hv i

private theorem dLattice_generates_fixed_cube (E : Subgroup S) (hE : E ≤ D 6)
    (hcard : 2 < Nat.card E) : D' ⊔ E = ⊤ := by
  obtain ⟨r, rfl⟩ := (subgroup_le_D_iff E).mp hE
  have hc : 2 < (dLatticeIndices r).card := by
    rwa [card_dLattice] at hcard
  apply chain_generates (chain r)
  intro i
  have cert : ∀ r : Fin 16, 2 < (dLatticeIndices r).card →
      ∀ i : Fin 5, ∃ j : Fin 8, j ∈ dLatticeIndices r ∧ ∃ l : Fin 3,
        (MulAut.conj (chain r)) (Equiv.swap i.castSucc i.succ) =
          (MulAut.conj (dWords j)) ((MulAut.conj k) (pairSwap 6 l)) := by
    decide +kernel
  obtain ⟨j, hj, l, he⟩ := cert r hc i
  rw [he]
  exact (D' ⊔ dLattice r).mul_mem
    ((D' ⊔ dLattice r).mul_mem
      (mem_sup_right ((dWords_mem_dLattice r j).mpr hj))
      (mem_sup_left (mem_map_of_mem _
        (pairSwap_mem (n := 6) (m := 3) l (by omega)))))
    ((D' ⊔ dLattice r).inv_mem
      (mem_sup_right ((dWords_mem_dLattice r j).mpr hj)))

/-- Every subgroup of order greater than two in a marked cube generates the
whole symmetric-six image together with the compatible conjugate cube. -/
theorem elementary_dLattice_generates_conjugate_cube
    (u : S) (E : Subgroup S)
    (hE : E ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    (hcard : 2 < Nat.card E) :
    (D 6).map (MulAut.conj (u * elementaryDConjugator)).toMonoidHom ⊔ E = ⊤ := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  let E' := E.map f
  have hE' : E' ≤ D 6 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmap := map_mono (f := (MulAut.conj u⁻¹).toMonoidHom) hE
    have hDu : ((D 6).map (MulAut.conj u).toMonoidHom).map
        (MulAut.conj u⁻¹).toMonoidHom = D 6 := by
      rw [map_map]
      have hfcomp : (MulAut.conj u⁻¹).toMonoidHom.comp
          (MulAut.conj u).toMonoidHom = MonoidHom.id S := by
        apply MonoidHom.ext
        intro x
        change u⁻¹ * (u * x * u⁻¹) * u = x
        group
      rw [hfcomp, Subgroup.map_id]
    rw [hDu] at hmap
    exact hmap ⟨y, hy, rfl⟩
  have hcard' : 2 < Nat.card E' := by
    change 2 < Nat.card (E.map (MulAut.conj u⁻¹).toMonoidHom)
    rw [Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective]
    exact hcard
  have hgen' : D' ⊔ E' = ⊤ := dLattice_generates_fixed_cube E' hE' hcard'
  have hmap := congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) hgen'
  rw [Subgroup.map_sup] at hmap
  have hD : D'.map (MulAut.conj u).toMonoidHom =
      (D 6).map (MulAut.conj (u * k)).toMonoidHom := by
    rw [map_map]
    congr 1
  have hEeq : E'.map (MulAut.conj u).toMonoidHom = E := by
    rw [map_map]
    have hfcomp : (MulAut.conj u).toMonoidHom.comp
        (MulAut.conj u⁻¹).toMonoidHom = MonoidHom.id S := by
      apply MonoidHom.ext
      intro x
      change u * (u⁻¹ * x * (u⁻¹)⁻¹) * u⁻¹ = x
      group
    rw [hfcomp, Subgroup.map_id]
  rw [hD, hEeq, map_top_of_surjective (MulAut.conj u).toMonoidHom
      (MulAut.conj u).surjective] at hmap
  exact hmap

/- The finite generation equality lifts through the complete kernel of the
literal symmetric projection. No section of that projection is chosen. -/
theorem elementary_cube_generation_lift
    {H : Type*} [Group H] (π : H →* S) (hπ : Function.Surjective π)
    (u : S) (C E : Subgroup H) (hker : π.ker ≤ C)
    (hC : C.map π = (D 6).map (MulAut.conj (u * elementaryDConjugator)).toMonoidHom)
    (hE : E.map π ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    (hcard : 2 < Nat.card (E.map π)) : C ⊔ E = ⊤ := by
  apply map_injective_of_ker_le π (hker.trans le_sup_left) le_top
  rw [Subgroup.map_sup,hC,map_top_of_surjective π hπ]
  exact elementary_dLattice_generates_conjugate_cube u (E.map π) hE hcard

/-- The selected cube may be marked by a rotation of the original cube.
The quotient generation certificate is parameterized by that actual marking;
an equality of the rotated and original cubes transports the image-side
containment without changing the literal kernel lift. -/
theorem elementary_cube_generation_lift_of_cube_eq
    {H : Type*} [Group H] (π : H →* S) (hπ : Function.Surjective π)
    (u v : S) (C E : Subgroup H) (hker : π.ker ≤ C)
    (hC : C.map π = (D 6).map (MulAut.conj (v * elementaryDConjugator)).toMonoidHom)
    (hE : E.map π ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    (hEq : (D 6).map (MulAut.conj u).toMonoidHom =
      (D 6).map (MulAut.conj v).toMonoidHom)
    (hcard : 2 < Nat.card (E.map π)) : C ⊔ E = ⊤ := by
  apply elementary_cube_generation_lift π hπ v C E hker hC
  · simpa only [hEq] using hE
  · exact hcard

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

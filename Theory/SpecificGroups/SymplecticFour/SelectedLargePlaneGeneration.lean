module
public import Theory.SpecificGroups.SymplecticFour.LargeSylowGeneration
public import Theory.SpecificGroups.SymplecticFour.SelectedPlaneGeneration

/-!
# Simultaneous full-plane selection at large quadratic images

Place the large quadratic actor in a plane radical. Its invertible shear
and the opposite full radical generate the symplectic group. Choose the
second conjugator to move that opposite radical back onto the actor's
plane. The same pair therefore gives generation and full-plane-pair
generation, without assuming the actor lies in the original radical.

All field degrees and the literal conjugation maps are retained.
The full-kernel consumer is NonbinarySymplectic.CriticalReduction.LargeSelection.
Source: MS93 (5.6)(b,c), printed pp.917--918, full-plane large-image branch.
-/

public noncomputable section
open Subgroup Representation
namespace Theory.SpecificGroups.SymplecticFour.SelectedLargePlaneGeneration
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] [Finite F] in
private theorem map_conj_mul (A : Subgroup (Sp F)) (g h : Sp F) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

/-- A full plane radical and a large quadratic actor admit the same
selector for generation and for a generating pair of plane radicals. -/
theorem exists_plane_large_quadratic_selection
    (E A : Subgroup (Sp F))
    (hE : ∃ k : Sp F, E.map (MulAut.conj k).toMonoidHom =
      (wing true).map (unipotent (F := F)).subtype)
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hc : Nat.card F < Nat.card A) :
    ∃ g x : Sp F,
      E.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ ∧
      E.map (MulAut.conj g).toMonoidHom ⊔
        (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨k,hk⟩ := hE
  rw [←SymplecticConjugatePair.planeRadical_eq_wing] at hk
  obtain ⟨c,hcA⟩ := LargePlaneGeneration.large_quadratic_plane_coordinates A hq hc
  let o := TwoConjugate.opposition (F := F)
  let g := c⁻¹*o*k
  let x := c⁻¹*o*c
  have hgen := LargePlaneGeneration.opposite_plane_large_subactor_generate
    (A.map (MulAut.conj c).toMonoidHom) hcA
    (by rw [card_map_of_injective (MulAut.conj c).injective]; exact hc)
  have htop : (⊤ : Subgroup (Sp F)).map (MulAut.conj c).toMonoidHom = ⊤ :=
    map_top_of_surjective _ (MulAut.conj c).surjective
  have hEgc : (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      SymplecticConjugatePair.planeRadical.map (MulAut.conj o).toMonoidHom := by
    rw [map_conj_mul,show c*g=o*k by dsimp [g]; group,←map_conj_mul,hk]
  have hfull : E.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
    apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [Subgroup.map_sup,hEgc,htop]
    exact hgen
  have hsecond : A ≤ (E.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x⁻¹).toMonoidHom := by
    apply (map_le_map_iff_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective).mp
    rw [map_conj_mul,map_conj_mul,
      show c*x⁻¹*g=k by dsimp [x,g]; group,hk]
    exact hcA
  exact ⟨g,x,hfull,top_unique (hfull ▸ sup_le_sup_left hsecond _)⟩

end Theory.SpecificGroups.SymplecticFour.SelectedLargePlaneGeneration

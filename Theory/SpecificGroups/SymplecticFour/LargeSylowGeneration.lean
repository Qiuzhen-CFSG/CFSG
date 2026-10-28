module
public import Theory.SpecificGroups.SymplecticFour.LargePlaneGeneration

/-!
# A large quadratic actor and a conjugate Sylow generate Sp₄(4)

The displacement of a large quadratic actor is an isotropic plane.
Move that plane to the standard plane and use an invertible shear in the
actor. The opposite plane radical lies in an opposite Sylow, and the
checked shear calculation supplies generation. Sylow conjugacy retains
an actual conjugator for any prescribed original Sylow.

The original full-kernel lift is OriginalLargeSylowGeneration; the tensor
consumer excludes the remaining large-distance paths.
Source: MS93 (3.3), (5.5)--(5.11), pp.867,915--924.
-/
public noncomputable section
open Matrix Subgroup Representation
namespace Theory.SpecificGroups.SymplecticFour.LargePlaneGeneration
open TwoLocalCover InvolutionTypes InvolutionCentralizers CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] in
/-- A large quadratic actor lies in a conjugate of the literal plane radical. -/
theorem large_quadratic_plane_coordinates (A : Subgroup (Sp F))
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hc : Nat.card F < Nat.card A) :
    ∃ k : Sp F, A.map (MulAut.conj k).toMonoidHom ≤
      SymplecticConjugatePair.planeRadical := by
  have hd : Module.finrank F (displacementSpace A) = 2 := by
    have hle := finrank_le_two_of_isotropic (displacementSpace A)
      (quadratic_displacement_isotropic A hq)
    have hbound := card_actor_le_displacement_dimension A
    have hp : 0 < Nat.card F := Nat.card_pos
    interval_cases hh : Module.finrank F (displacementSpace A) <;> simp at hbound <;> omega
  have hn : displacementSpace A ≠ ⊥ := by
    intro h
    rw [h,finrank_bot] at hd
    omega
  obtain ⟨k,hk⟩ := isotropic_subspace_conjugate_standard (displacementSpace A) hn
    (quadratic_displacement_isotropic A hq)
  have hp : (displacementSpace A).map (toLinear k).toLinearMap = plane F := by
    rcases hk with hk | hk
    · have hh := (toLinear k).finrank_map_eq (displacementSpace A)
      rw [hk,finrank_point,hd] at hh
      omega
    · exact hk
  refine ⟨k,?_⟩
  rintro g ⟨x,hx,rfl⟩
  have hm : movedSpace (k*x*k⁻¹) ≤ plane F := by
    rw [movedSpace_conj,←hp]
    apply Submodule.map_mono
    rintro w ⟨v,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp A.subtype) ⟨x,hx⟩ v
  obtain ⟨he,hs⟩ := matrix_of_movedSpace_le_plane (k*x*k⁻¹) hm
  apply (SymplecticConjugatePair.mem_planeRadical_iff _).mpr
  exact ⟨⟨(k*x*k⁻¹).val.toBlocks₁₂,hs⟩,Subtype.ext he.symm⟩

/-- Any prescribed Sylow has a conjugate generating with the large
quadratic actor, in the same symplectic marking. -/
theorem exists_sylow_large_quadratic_generator (hF : Nat.card F = 4)
    (P : Sylow 2 (Sp F)) (A : Subgroup (Sp F))
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hc : Nat.card F < Nat.card A) :
    ∃ g : Sp F, (P : Subgroup (Sp F)).map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨k,hk⟩ := large_quadratic_plane_coordinates A hq hc
  obtain ⟨l,hl⟩ := MulAction.exists_smul_eq (Sp F) P
    (unipotentSylow (n := 2) hF (by decide))
  have hlP : (P : Subgroup (Sp F)).map (MulAut.conj l).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hl
  let o := TwoConjugate.opposition (F := F)
  have hgen := opposite_plane_large_subactor_generate (A.map (MulAut.conj k).toMonoidHom)
    hk (by rw [card_map_of_injective (MulAut.conj k).injective]; exact hc)
  have hw : SymplecticConjugatePair.planeRadical (F := F) ≤ unipotent := by
    rw [SymplecticConjugatePair.planeRadical_eq_wing]
    exact map_subtype_le _
  refine ⟨k⁻¹*o*l,?_⟩
  apply Subgroup.map_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr (MulAut.conj k).surjective]
  have hm : ((P : Subgroup (Sp F)).map (MulAut.conj (k⁻¹*o*l)).toMonoidHom).map
      (MulAut.conj k).toMonoidHom = unipotent.map (MulAut.conj o).toMonoidHom := by
    rw [←hlP,Subgroup.map_map,Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change k*((k⁻¹*o*l)*x*(k⁻¹*o*l)⁻¹)*k⁻¹=o*(l*x*l⁻¹)*o⁻¹
    group
  rw [hm]
  exact top_unique (hgen ▸ sup_le_sup_right (map_mono hw) _)

end Theory.SpecificGroups.SymplecticFour.LargePlaneGeneration

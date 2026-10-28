module
public import Theory.SpecificGroups.SymplecticFour.FourLongRoots
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.NormalForms
public import Theory.SpecificGroups.SymplecticFour.QuadraticPlane

/-!
# Recognizing a full transvection root from its displacement line

A quadratic actor with a one-dimensional displacement space can be conjugated
to move only the standard point. Symplecticity then puts it in the literal
long-root matrix subgroup. Equality of orders identifies the entire root,
and the four-conjugate generation theorem applies to this original actor.

Source: MS93 (3.3), printed p.867, the four-root argument after the critical
image is proved to have order q. No root marking is assumed in this step.
-/

@[expose] public noncomputable section
open Matrix Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.FourLongRoots
open InvolutionTypes InvolutionCentralizers TwoLocalCover
variable {F : Type*} [Field F]

/-- A symplectic operator moving only the standard point lies in its literal
long-root subgroup. -/
theorem mem_root_zero_of_movedSpace_le_point (g : Sp F)
    (hg : movedSpace g ≤ point F) : g ∈ RootSubgroup.group 0 := by
  obtain ⟨hM,hs⟩ := matrix_of_movedSpace_le_plane g (hg.trans point_le_plane)
  have hb (j : Fin 2) : g.val.toBlocks₁₂ 1 j = 0 := by
    have hx := hg (show g • (Pi.single (.inr j) (1 : F) : Vector F) - Pi.single (.inr j) 1 ∈
      movedSpace g from ⟨Pi.single (.inr j) 1,rfl⟩)
    have he := (mem_point_iff _).mp hx |>.1
    simpa [smul_eq_mulVec, Matrix.mulVec_single, Matrix.toBlocks₁₂] using he
  have he := hs.apply 0 1
  apply (RootSubgroup.mem_group_iff 0 g).mpr
  refine ⟨g.val.toBlocks₁₂ 0 0,?_⟩
  symm
  apply Subtype.ext
  rw [hM]
  change fromBlocks 1 g.val.toBlocks₁₂ 0 1 = rootMatrix 0 (g.val.toBlocks₁₂ 0 0)
  have hB : g.val.toBlocks₁₂ = single 0 0 (g.val.toBlocks₁₂ 0 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single,hb,←he]
  exact congrArg (fun B : Matrix (Fin 2) (Fin 2) F => fromBlocks 1 B 0 1) hB

variable [Finite F] [CharP F 2]

omit [CharP F 2] in
/-- A full field-sized actor with one-dimensional displacement is a conjugate
of the entire long-root group, rather than merely a binary subgroup of it. -/
theorem exists_conjugate_root_of_displacement_one
    (A : Subgroup (Sp F)) (hc : Nat.card A = Nat.card F)
    (hd : Module.finrank F (displacementSpace A) = 1)
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    ∃ h : Sp F, A.map (MulAut.conj h).toMonoidHom = RootSubgroup.group 0 := by
  have hn : displacementSpace A ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hd
    omega
  obtain ⟨h,hh⟩ := isotropic_subspace_conjugate_standard (displacementSpace A) hn
    (quadratic_displacement_isotropic A hq)
  have hp : (displacementSpace A).map (toLinear h).toLinearMap = point F := by
    rcases hh with hh | hh
    · exact hh
    · have he := (toLinear h).finrank_map_eq (displacementSpace A)
      rw [hh,finrank_plane,hd] at he
      omega
  refine ⟨h,?_⟩
  have hle : A.map (MulAut.conj h).toMonoidHom ≤ RootSubgroup.group 0 := by
    rintro g ⟨x,hx,rfl⟩
    apply mem_root_zero_of_movedSpace_le_point
    change movedSpace (h*x*h⁻¹) ≤ point F
    rw [movedSpace_conj,←hp]
    apply Submodule.map_mono
    rintro w ⟨v,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp A.subtype) ⟨x,hx⟩ v
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [←Nat.card_congr (A.equivMapOfInjective (MulAut.conj h).toMonoidHom
    (MulAut.conj h).injective).toEquiv,RootSubgroup.card]
  exact hc.ge

/-- The actual line-displacement actor has four conjugates generating Sp₄. -/
theorem exists_four_conjugates_of_displacement_one (hF : 2 < Nat.card F)
    (A : Subgroup (Sp F)) (hc : Nat.card A = Nat.card F)
    (hd : Module.finrank F (displacementSpace A) = 1)
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    ∃ g : Fin 4 → Sp F, (⨆ i, A.map (MulAut.conj (g i)).toMonoidHom) = ⊤ := by
  obtain ⟨h,hh⟩ := exists_conjugate_root_of_displacement_one A hc hd hq
  obtain ⟨g,hg⟩ := exists_four_conjugates_generate hF
  refine ⟨fun i => g i*h,?_⟩
  have he (i : Fin 4) : A.map (MulAut.conj (g i*h)).toMonoidHom =
      (RootSubgroup.group 0).map (MulAut.conj (g i)).toMonoidHom := by
    rw [←hh,Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  simpa only [he] using hg

end Theory.SpecificGroups.SymplecticFour.FourLongRoots

module
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.BlockRealization.Algebra
public import Theory.SpecificGroups.PSL3Two.EmbeddingObstructions
public import Theory.SpecificGroups.SymplecticFour.SevenNormalizer
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# No even G₂ carrier in symplectic four-space

The determinant-one block action on split octonions embeds SL₃(K) faithfully
in the actual G₂(K) model. Its binary subgroup supplies a seven-element
conjugate to its square, contradicting the symplectic spectrum. Since this
binary subgroup is perfect, it also lies in the actual derived subgroup;
thus the binary derived G₂ endpoint is excluded by the same literal map.

Source: Aschbacher--Smith G.4.1, printed p.342.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Matrix Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour.NativeG2
open Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
open Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization
variable {K F : Type*} [Field K] [CharP K 2] [Field F] [CharP F 2]

private def binarySL3 : Matrix.PSL3Two.PSL →* SL(3,K) :=
  (SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) K)).comp Matrix.PSL3Two.equiv.symm.toMonoidHom
private theorem binarySL3_injective : Function.Injective (binarySL3 (K:=K)) := by
  have hi : Function.Injective (SpecialLinearGroup.map (n:=Fin 3) (ZMod.castHom (dvd_refl 2) K)) := by
    intro x y h
    apply Subtype.ext
    ext i j
    apply (ZMod.castHom (dvd_refl 2) K).injective
    exact congrArg (fun z : SL(3,K) => z.val i j) h
  exact hi.comp Matrix.PSL3Two.equiv.symm.injective
private def binaryG2 : Matrix.PSL3Two.PSL →* Atlas.G2.Model K := blockHom.comp binarySL3
private theorem binaryG2_injective : Function.Injective (binaryG2 (K:=K)) := by
  have hb : Function.Injective (blockHom (K:=K)) := by
    intro x y h
    apply Subtype.ext
    simpa only [peirceMatrix_blockHom] using congrArg peirceMatrix h
  exact hb.comp binarySL3_injective

private theorem obstruction (G : Type*) [Group G]
    (l : Matrix.PSL3Two.PSL →* G) (hl : Function.Injective l)
    (j : G →* Sp F) : ¬Function.Injective j := by
  intro hj
  let f := j.comp l
  have hf : Function.Injective f := hj.comp hl
  obtain ⟨a,b,ha,han,hab⟩ := Matrix.PSL3Two.exists_seven_conjugate_square
  apply SevenNormalizer.seven_not_conjugate_square (f a) (f b)
  · rw [←map_pow,ha,map_one]
  · exact fun h => han (hf (h.trans f.map_one.symm))
  · simpa only [map_mul,map_inv,map_pow] using congrArg f hab

/-- The actual split-octonion G₂ carrier has no faithful Sp₄ action. -/
theorem model_not_injective (j : Atlas.G2.Model K →* Sp F) : ¬Function.Injective j :=
  obstruction _ binaryG2 binaryG2_injective j

/-- The same obstruction occurs inside the actual derived G₂ carrier. -/
theorem derived_not_injective (j : commutator (Atlas.G2.Model K) →* Sp F) :
    ¬Function.Injective j := by
  letI : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect 3 (by decide)
  have hle : (binaryG2 (K:=K)).range ≤ commutator (Atlas.G2.Model K) := by
    rw [MonoidHom.range_eq_map, ←Group.IsPerfect.commutator_eq_top,
      map_commutator_eq]
    exact Subgroup.commutator_mono
      (show (binaryG2 (K:=K)).range ≤ ⊤ from le_top) le_top
  let l := (binaryG2 (K:=K)).codRestrict (commutator (Atlas.G2.Model K)) (fun x => hle ⟨x,rfl⟩)
  have hl : Function.Injective l := by
    intro a b h
    exact binaryG2_injective (congrArg Subtype.val h)
  exact obstruction _ l hl j
end Theory.SpecificGroups.SymplecticFour.NativeG2

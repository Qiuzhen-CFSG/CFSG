module
public import Theory.SpecificGroups.SymplecticFour.RootDisplacement
public import Theory.Representation.BinaryOffender.ConjugateSubgroupSaturation
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedIndex

/-!
# Saturating the original symplectic cover inside a larger binary module

A quadratic field-sized actor with a displacement line has four conjugates
generating the derived symplectic group. A fixed-codimension bound on the
larger binary module therefore bounds its global fixed quotient. The covered
natural moving layer attains that bound, so it spans with the global fixed
space. The literal cover and its central attachment are retained throughout.

Source: MS93 (3.3), printed p.867, the deduction X = U C_X(L) from the
critical root movement bound. The geometric producer of that bound remains
a distinct earlier input.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Algebra (ZMod 2) F] in
/-- Four generating conjugates lift through the exact derived-to-full
symplectic identification. -/
theorem derived_four_conjugates_of_displacement_one (hF : 2 < Nat.card F)
    (A : Subgroup (L (K := F))) (hc : Nat.card A = Nat.card F)
    (hd : Module.finrank F (displacementSpace (A.map (commutator (Sp F)).subtype)) = 1)
    (hq : ∀ x ∈ A.map (commutator (Sp F)).subtype,
      ∀ y ∈ A.map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    ∃ g : Fin 4 → L (K := F), (⨆ i, A.map (MulAut.conj (g i)).toMonoidHom) = ⊤ := by
  let d : L (K := F) ≃* Sp F :=
    (MulEquiv.subgroupCongr
      (OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF)).trans Subgroup.topEquiv
  have hdmap : d.toMonoidHom = (commutator (Sp F)).subtype := rfl
  have hcard : Nat.card (A.map (commutator (Sp F)).subtype) = Nat.card F :=
    (Nat.card_congr (A.equivMapOfInjective _ (commutator (Sp F)).subtype_injective).toEquiv).symm.trans hc
  obtain ⟨g,hg⟩ := FourLongRoots.exists_four_conjugates_of_displacement_one hF
    (A.map (commutator (Sp F)).subtype) hcard hd hq
  refine ⟨fun i => d.symm (g i),?_⟩
  apply Subgroup.map_injective (f := d.toMonoidHom) d.injective
  rw [Subgroup.map_iSup,Subgroup.map_top_of_surjective _ d.surjective]
  have he (i : Fin 4) : (A.map (MulAut.conj (d.symm (g i))).toMonoidHom).map d.toMonoidHom =
      (A.map (commutator (Sp F)).subtype).map (MulAut.conj (g i)).toMonoidHom := by
    rw [Subgroup.map_map,Subgroup.map_map,←hdmap]
    congr 1
  simpa only [he] using hg

/-- The full natural fixed quotient has binary degree four times the field degree. -/
theorem fixedCodim_binaryNatural_top : fixedCodim (binaryNatural (K := F)) ⊤ =
    4 * Module.finrank (ZMod 2) F := by
  have hfix : fixedSpace (binaryNatural (K := F)) ⊤ = ⊥ := by
    apply bot_unique
    intro v hv
    apply (binary_natural_fixed (K := F)).le
    exact fun g => hv ⟨g,mem_top g⟩
  have he := fixedCodim_add_finrank (binaryNatural (K := F)) ⊤
  rw [hfix,finrank_bot,add_zero] at he
  rw [he]
  simp [Natural,Module.finrank_pi_fintype]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The natural moving cover already fills the four-root movement budget,
so it supplements the full fixed space in the original ambient module. -/
theorem sup_fixed_eq_top_of_root_budget (hF : 2 < Nat.card F)
    (ρ : Representation (ZMod 2) (L (K := F)) V) (U : Subrepresentation ρ)
    (p : U.toRepresentation.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (A : Subgroup (L (K := F))) (hc : Nat.card A = Nat.card F)
    (hd : Module.finrank F (displacementSpace (A.map (commutator (Sp F)).subtype)) = 1)
    (hq : ∀ x ∈ A.map (commutator (Sp F)).subtype,
      ∀ y ∈ A.map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hbound : fixedCodim ρ A ≤ Module.finrank (ZMod 2) F) :
    U.toSubmodule ⊔ fixedSpace ρ ⊤ = ⊤ := by
  obtain ⟨g,hg⟩ := derived_four_conjugates_of_displacement_one hF A hc hd hq
  apply subrepresentation_sup_fixed_of_conjugate_budget ρ U ⊤ A g hg.ge
  rw [Fintype.card_fin,fixedCodim_of_binaryCover p hp]
  rw [fixedCodim_binaryNatural_top]
  exact Nat.mul_le_mul_left 4 hbound

end Representation.SymplecticFourOrthogonalCover

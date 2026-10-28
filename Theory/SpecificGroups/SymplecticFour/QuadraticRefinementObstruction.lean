module
public import Theory.SpecificGroups.SymplecticFour.RootDisplacement
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.ArbitraryOrthogonalActors
public import Theory.Representation.SymplecticFourOrthogonalCover.Roots


/-!
# Quadratic actors excluding invariant refinements

A full nonbinary long-root group cannot preserve a quadratic refinement:
its parameter t would satisfy t=c t² for every field element. Coordinate
transport gives the same obstruction for a field-sized quadratic actor with
one-dimensional displacement. A quadratic actor of order at least q² is
excluded by the orthogonal plane estimate 2q < q².

These are the two model cases used in MS93 (3.4), printed p.869, retaining
the original field rather than specializing to four elements.
-/

public noncomputable section
open Matrix Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
/-- A full long-root group at nonbinary degree preserves no quadratic refinement. -/
theorem root_no_invariant_refinement (hF : 2 < Nat.card F) :
    ¬ ∃ c : Vector F, ∀ a : RootSubgroup.group (F := F) 0, ∀ v,
      refinement c (a.val • v) = refinement c v := by
  classical
  rintro ⟨c,hc⟩
  have ht (t : F) : t = c (.inl 0)*t^2 := by
    have hh := hc ⟨rootElement 0 t,(RootSubgroup.mem_group_iff 0 _).mpr ⟨t,rfl⟩⟩
      (Pi.single (.inr 0) 1)
    change refinement c ((rootElement 0 t).val *ᵥ Pi.single (.inr 0) 1) = _ at hh
    rw [Representation.SymplecticFourOrthogonalCover.Roots.natural_root] at hh
    simp [refinement_apply,Fintype.sum_sum_type,
      Pi.single_apply,ClassicalOrthogonal.e] at hh
    have hz : t + c (.inl 0)*t^2 = 0 :=
      add_right_cancel (by simpa only [add_assoc,zero_add] using hh)
    exact CharTwo.add_eq_zero.mp hz
  have hc0 : c (.inl 0) = 1 := by simpa using (ht 1).symm
  have hs (t : F) : t^2=t := by simpa only [hc0,one_mul] using (ht t).symm
  let f : F → Bool := fun t => decide (t ≠ 0)
  have hf : Function.Injective f := by
    intro a b he
    rcases eq_zero_or_one_of_sq_eq_self (hs a) with rfl | rfl <;>
      rcases eq_zero_or_one_of_sq_eq_self (hs b) with rfl | rfl
    · rfl
    · simp [f] at he
    · simp [f] at he
    · rfl
  have hcard := Nat.card_le_card_of_injective f hf
  have htwo : Nat.card Bool = 2 := by simp
  omega

/-- A field-sized quadratic actor with one-dimensional displacement is a
full root group, so the same obstruction holds in its original coordinates. -/
theorem no_refinement_of_displacement_one (hF : 2 < Nat.card F)
    (A : Subgroup (Sp F)) (hc : Nat.card A = Nat.card F)
    (hd : Module.finrank F (displacementSpace A) = 1)
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    ¬ ∃ c : Vector F, ∀ a : A, ∀ v, refinement c (a.val • v) = refinement c v := by
  rintro ⟨c,hpres⟩
  obtain ⟨g,hg⟩ := FourLongRoots.exists_conjugate_root_of_displacement_one A hc hd hq
  obtain ⟨d,hdc⟩ := refinement_comp_symplectic c g⁻¹
  apply root_no_invariant_refinement hF
  refine ⟨d,?_⟩
  rintro ⟨x,hx⟩ v
  rw [←hg] at hx
  obtain ⟨a,ha,rfl⟩ := hx
  rw [←hdc,←hdc]
  change refinement c (g⁻¹ • ((g*a*g⁻¹) • v)) = refinement c (g⁻¹ • v)
  simp only [mul_smul,inv_smul_smul]
  exact hpres ⟨a,ha⟩ _

/-- A quadratic actor of order at least q squared also has no invariant
refinement: the orthogonal plane bound is only 2q. -/
theorem no_refinement_of_large_quadratic (hF : 2 < Nat.card F)
    (A : Subgroup (Sp F)) (hlarge : Nat.card F^2 ≤ Nat.card A)
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    ¬ ∃ c : Vector F, ∀ a : A, ∀ v, refinement c (a.val • v) = refinement c v := by
  rintro ⟨c,hc⟩
  have hbig : Nat.card F < Nat.card A := by nlinarith
  have hP := large_quadratic_displacement_self_orthogonal A hq hbig
  have hfix := displacementSpace_le_fixedSpace_of_quadratic A hq
  have hcard := card_le_of_fixes_self_orthogonal_plane A (displacementSpace A) hP
    (fun a v hv => hfix hv a.val a.property) c hc
  nlinarith

end Theory.SpecificGroups.SymplecticFour

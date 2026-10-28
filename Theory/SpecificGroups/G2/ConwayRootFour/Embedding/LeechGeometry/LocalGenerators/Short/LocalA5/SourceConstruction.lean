module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.Data
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Inputs

/-!
# Assembling the Leech local A₅ from geometry and its factor action

The actual common reflection makes both projections nontrivial. Simplicity
of A₅ makes them injective, and the actual SL₂(4)–A₅ equivalence makes them
surjective. Their comparison defines the automorphism `twist`; the literal
reflection and torus actions prove its two prescribed restrictions. The
single scalar-class witness in the geometric input supplies the shear class
by A₅ involution fusion. The lift has precisely the original subgroup as its
image and still centralizes the placed D₁₀ in the actual Leech quotient.

The geometry and factorization remain explicit in these conditional results.
`exists_data` is not yet asserted: its final assembly must construct both
inputs. No diagonal-selection or whole-centralizer faithfulness is used.
Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
using Lemmas 47.2 and 48.8.
-/

open Matrix Atlas.Conway Atlas.Algebra
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
variable {L : LongFrame} {G : Geometry L}

theorem FactorAction.reflection (A : FactorAction G) :
    A.hom G.reflection = (flip, flip) := by
  apply pairRepresentation_injective
  apply LinearEquiv.ext
  intro v
  apply L.coordinates_injective
  rw [← A.on_action, G.reflection_action]

theorem FactorAction.cubic (A : FactorAction G) (t : Fˣ) :
    A.hom (G.cubic t) = (torus t, (torus t)⁻¹) := by
  apply pairRepresentation_injective
  apply LinearEquiv.ext
  intro v
  apply L.coordinates_injective
  rw [← A.on_action, G.cubic_action]

private theorem flip_ne_one : (flip : SL(2,F)) ≠ 1 := by
  intro h
  have he := congrArg (fun a : SL(2,F) => a.val 0 1) h
  simp [flip] at he

/-- Simplicity and equal cardinalities make each nontrivial projection an
isomorphism. This uses the actual common reflection to exclude the zero map. -/
theorem Geometry.projection_bijective (G : Geometry L) (f : G.subgroup →* SL(2,F))
    (hf : f G.reflection = flip) : Function.Bijective f := by
  let : IsSimpleGroup G.subgroup := G.alternating.isSimpleGroup
  have hi : Function.Injective f := by
    rcases f.normal_ker.eq_bot_or_eq_top with h | h
    · exact f.ker_eq_bot_iff.mp h
    · have hr : G.reflection ∈ f.ker := h ▸ Subgroup.mem_top _
      exact False.elim (flip_ne_one (hf.symm.trans (MonoidHom.mem_ker.mp hr)))
  apply (Nat.bijective_iff_injective_and_card f).mpr
  exact ⟨hi, (Nat.card_congr G.alternating.toEquiv).trans
    (Nat.card_congr alternatingEquiv.toEquiv).symm⟩

def FactorAction.first (A : FactorAction G) : G.subgroup ≃* SL(2,F) :=
  MulEquiv.ofBijective ((MonoidHom.fst _ _).comp A.hom)
    (G.projection_bijective _ (congrArg Prod.fst A.reflection))

def FactorAction.second (A : FactorAction G) : G.subgroup ≃* SL(2,F) :=
  MulEquiv.ofBijective ((MonoidHom.snd _ _).comp A.hom)
    (G.projection_bijective _ (congrArg Prod.snd A.reflection))

theorem FactorAction.first_reflection (A : FactorAction G) : A.first G.reflection = flip :=
  congrArg Prod.fst A.reflection

theorem FactorAction.second_reflection (A : FactorAction G) : A.second G.reflection = flip :=
  congrArg Prod.snd A.reflection

theorem FactorAction.first_cubic (A : FactorAction G) (t : Fˣ) :
    A.first (G.cubic t) = torus t := congrArg Prod.fst (A.cubic t)

theorem FactorAction.second_cubic (A : FactorAction G) (t : Fˣ) :
    A.second (G.cubic t) = (torus t)⁻¹ := congrArg Prod.snd (A.cubic t)

private theorem shear_order : orderOf (shear : SL(2,F)) = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    change (!![1,1;0,1] : Matrix (Fin 2) (Fin 2) F) ^ 2 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  · intro h
    have he := congrArg (fun a : SL(2,F) => a.val 0 1) h
    simp [shear] at he

/-- Assemble the actual lift and its factor automorphism, proving the marked
restrictions and scalar class. The two independent source inputs remain explicit. -/
def FactorAction.data (A : FactorAction G) : Data L where
  twist := A.first.symm.trans A.second
  lift := G.subgroup.subtype.comp A.first.symm.toMonoidHom
  lift_mem a := G.mem _
  on_action a v := by
    change quotientModTwoRepresentation (A.first.symm a : LeechCentralQuotient)
      (L.coordinates v) =
      L.coordinates (pairRepresentation (a, A.second (A.first.symm a)) v)
    rw [A.on_action]
    have hp : A.hom (A.first.symm a) = (a, A.second (A.first.symm a)) := by
      apply Prod.ext
      · exact A.first.apply_symm_apply a
      · rfl
    rw [hp]
  twist_flip := by
    change A.second (A.first.symm flip) = flip
    have h : A.first.symm flip = G.reflection := by
      rw [← A.first_reflection, A.first.symm_apply_apply]
    rw [h, A.second_reflection]
  twist_torus t := by
    change A.second (A.first.symm (torus t)) = (torus t)⁻¹
    have h : A.first.symm (torus t) = G.cubic t := by
      rw [← A.first_cubic t, A.first.symm_apply_apply]
    rw [h, A.second_cubic]
  scalar_class := by
    apply G.involution_class
    change orderOf (A.first.symm shear) = 2
    rw [A.first.symm.orderOf_eq]
    exact shear_order

/-- The constructed lift is precisely the source subgroup, with its literal
inclusion into the Leech central quotient. -/
theorem FactorAction.data_lift_range (A : FactorAction G) :
    A.data.lift.range = G.subgroup := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact (A.first.symm a).property
  · intro hg
    refine ⟨A.first ⟨g, hg⟩, ?_⟩
    change (A.first.symm (A.first ⟨g, hg⟩) : LeechCentralQuotient) = g
    rw [A.first.symm_apply_apply]

/-- The output retains genuine ambient centralization, beyond commutation
of the two coordinate actions. -/
theorem FactorAction.data_lift_commutes (A : FactorAction G) (a : SL(2,F))
    (d : DihedralGroup 5) : Commute (A.data.lift a) (dihedralLift L d) :=
  G.centralizes (A.first.symm a) d

/-- The conditional source application; both independent inputs must still
be constructed for the unconditional `LocalA5.exists_data`. -/
theorem exists_data_of_geometry (L : LongFrame) (G : Geometry L) (A : FactorAction G) :
    Nonempty (Data L) := ⟨A.data⟩

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction

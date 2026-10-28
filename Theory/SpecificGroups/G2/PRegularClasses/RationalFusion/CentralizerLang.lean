module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.Frobenius
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.FrobeniusGeometry
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedReduction
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedFixedWeight
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight

/-!
# Lang equations in the actual odd-order G₂ centralizer

The closed coordinate model and its point equivalence identify the algebraic
centralizer with the literal octonion-automorphism centralizer. Coefficient
Frobenius restricts surjectively and has zero differential there. The proved
general zero-differential Lang theorem therefore constructs the required
solution once connectedness is established.

Geometric torus normal form reduces connectedness to two exhaustive torus
cases, both proved by the imported coordinate parametrizations. The final
`exists_lang` discharges these cases in `exists_lang_of_torus_cases`, retaining
only the permitted geometric normal-form hypothesis. This includes repeated
eigenvalues and order three, and requires no lower bound on the finite field's
cardinality. The identity case is left to the rational-fusion consumer.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 8.5, 10.7--10.8 and 12.5;
GLS III, Section 2.1 (`refs/KGroup/GLS3/chapter2.tex`). The general theorem used
here has no D₄-model premises and uses only the standard Lean axioms.
-/

public section

open Theory.AlgebraicGroup
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang
open FieldExtension
noncomputable section
variable (F : Type*) [Field F] [Finite F]
local notation "K" => AlgebraicClosure F

/-- Connectedness of the actual closed centralizer suffices: the Frobenius
morphism, its surjectivity and its zero differential are all constructed. -/
theorem exists_lang_of_connected (g : Model F)
    (hconn : Variety.IsConnected
      (centralizerVariety (fieldEmbedding (algebraMap F K) g)))
    (z : Model K) (hz : Commute z (fieldEmbedding (algebraMap F K) g)) :
    ∃ u : Model K, Commute u (fieldEmbedding (algebraMap F K) g) ∧
      u * (frobenius F u)⁻¹ = z := by
  let E := centralizerPointEquiv (fieldEmbedding (algebraMap F K) g)
  let Z : Subgroup.centralizer ({fieldEmbedding (algebraMap F K) g} : Set (Model K)) :=
    ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr hz.eq⟩
  obtain ⟨v,hv⟩ := langMorphism_surjective_of_differential_eq_zero
    (centralizerFrobeniusMorphism F g) (centralizerFrobeniusMorphism_surjective F g)
    hconn (centralizerFrobeniusMorphism_differential F g) (E.symm Z)
  refine ⟨(E v).val, Subgroup.mem_centralizer_singleton_iff.mp (E v).property, ?_⟩
  rw [langMorphism_apply, map_inv] at hv
  have ht := congrArg (fun p => (E p).val) hv
  have hCompat (p) : (E ((centralizerFrobeniusMorphism F g).onPoints p)).val =
      frobenius F (E p).val := centralizerPointFrobenius_apply F g p
  simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
    hCompat, MulEquiv.apply_symm_apply] using ht

/-- Conditional assembly from the two torus-centralizer
connectedness cases and the permitted geometric normal form. -/
theorem exists_lang_of_torus_cases [CharP F 2]
    (hgeom : ∀ x : Model K, ¬ 2 ∣ orderOf x →
      ∃ l m : Kˣ, IsConj x (torus l m))
    (hnoFixedWeight : ∀ l m : Kˣ, l ≠ 1 → m ≠ 1 → l ≠ m →
      Variety.IsConnected (centralizerVariety (torus l m)))
    (hfixedWeight : ∀ l m : Kˣ, torus l m ≠ 1 →
      (l = 1 ∨ m = 1 ∨ l = m) →
      Variety.IsConnected (centralizerVariety (torus l m)))
    (g : Model F) (hg : ¬ 2 ∣ orderOf g) (hg1 : g ≠ 1)
    (z : Model K) (hz : Commute z (fieldEmbedding (algebraMap F K) g)) :
    ∃ u : Model K, Commute u (fieldEmbedding (algebraMap F K) g) ∧
      u * (frobenius F u)⁻¹ = z := by
  apply exists_lang_of_connected F g ?_ z hz
  apply centralizer_connected_of_torus_cases hgeom hnoFixedWeight hfixedWeight
  · simpa only [fieldEmbedding_orderOf] using hg
  · intro he
    apply hg1
    apply fieldEmbedding_injective (algebraMap F K)
    simpa only [map_one] using he

omit [Finite F] in
/-- Every nonidentity odd-order element has connected centralizer, given
geometric torus normal form. Both torus-weight cases are discharged. -/
theorem centralizer_connected [CharP F 2]
    (hgeom : ∀ x : Model K, ¬ 2 ∣ orderOf x →
      ∃ l m : Kˣ, IsConj x (torus l m))
    (g : Model K) (hg : ¬ 2 ∣ orderOf g) (hg1 : g ≠ 1) :
    Variety.IsConnected (centralizerVariety g) := by
  exact centralizer_connected_of_torus_cases hgeom
    centralizer_connected_no_fixed_weight centralizer_connected_fixed_weight g hg hg1

/-- Frobenius Lang surjectivity in the actual centralizer of every
nonidentity odd-order finite-field element. Geometric torus normal form is
the only additional hypothesis; no connectedness or Lang premise remains. -/
theorem exists_lang [CharP F 2]
    (hgeom : ∀ x : Model K, ¬ 2 ∣ orderOf x →
      ∃ l m : Kˣ, IsConj x (torus l m))
    (g : Model F) (hg : ¬ 2 ∣ orderOf g) (hg1 : g ≠ 1)
    (z : Model K) (hz : Commute z (fieldEmbedding (algebraMap F K) g)) :
    ∃ u : Model K, Commute u (fieldEmbedding (algebraMap F K) g) ∧
      u * (frobenius F u)⁻¹ = z := by
  exact exists_lang_of_torus_cases F hgeom
    centralizer_connected_no_fixed_weight centralizer_connected_fixed_weight g hg hg1 z hz

end
end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang

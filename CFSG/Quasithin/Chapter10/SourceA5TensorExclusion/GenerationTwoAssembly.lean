module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoData
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Placement

/-!
# Conditional assembly of the original tensor exclusion

The earlier Cartan and amalgam inputs construct the actual generation-two
overgroup. Excluding its linear and G2 action images leaves Sp4(4).
A marked plane-local quotient then places the original full module inside
the block module; equality of their orders contradicts the original full
normalizer. The point-control extension applies this tensor exclusion to the original
chosen module and the reselected minimal Chapter13 setup.

The model-row and marked-plane inputs below are explicit mathematical
contracts, not additional conclusions included in the tensor model. They
remain to be constructed, as do the three earlier source inputs. Thus these
exports are conditional assembly, not a completed proof of Chapter9.

Source: Aschbacher--Smith 9.3.8--10 and the final paragraph of9.3,
printed pp.734--735; 10.2.9--12 and13.3.2(2), pp.750--754,884--885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterC.MSCentralOrbit
open ClassicalOrthogonal.FourPlusMatrix Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

namespace SourceA5TensorModel

/-- The literal plane quotient and natural quotient required by the
terminal paragraph of9.3. The normalization is by the actual overcomponent. -/
structure OriginalPlaneModel (D : FundamentalSetup KnownSimple.IsKnownSimple T L) where
  U : Subgroup G
  K : Subgroup G
  quotient : L →* planeLocal (F := Binary.F)
  onto : Function.Surjective quotient
  kernel : quotient.ker = U.subgroupOf L
  natural : D.fullModule.subgroupOf L →* Multiplicative (Fin 2 → Binary.F)
  natural_onto : Function.Surjective natural
  natural_kernel : natural.ker ≤ (U.subgroupOf L).comap (D.fullModule.subgroupOf L).subtype
  equivariant : letI := fullModule_component_normal (D := D)
    ∀ (g : L) (v : D.fullModule.subgroupOf L),
      natural (MulAut.conjNormal g v) =
        Multiplicative.ofAdd ((Plane.quotientMap (quotient g)).val *ᵥ (natural v).toAdd)
  card : Nat.card U = 256
  normalized : K ≤ normalizer (U : Set G)
  outside : ¬ K ≤ D.maximalLocal

variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The two Cartan contradictions on the actual action image in9.3.8--9. -/
@[expose] def LinearAndG2Exclusion : Prop :=
  ∀ c : m.GenerationTwoOvergroup,
    let W := omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ hr : IsPReduced 2 W,
      letI := hr.normal
      (¬ Nonempty (((pResidual 2 c.M).map (actionMk W)) ≃*
        SL(3,ChapterB.QuasisimpleSource.BinaryField.four.Carrier))) ∧
      (¬ Nonempty (((pResidual 2 c.M).map (actionMk W)) ≃*
        Atlas.G2.Model ChapterB.QuasisimpleSource.BinaryField.four.Carrier))

/-- Whole-block and plane-parabolic recognition in the surviving Sp4 row.
The model is on the literal centralizer quotient of the original Omega orbit. -/
@[expose] def SymplecticPlaneRecognition : Prop :=
  ∀ c : m.GenerationTwoOvergroup,
    let W := omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ hr : IsPReduced 2 W,
      letI := hr.normal
      Nonempty (((pResidual 2 c.M).map (actionMk W)) ≃*
        Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) →
      Nonempty (OriginalPlaneModel D)

include m in
/-- The genuine terminal plane calculation, with all maps retained. -/
theorem false_of_originalPlaneModel (p : OriginalPlaneModel D) : False :=
  m.false_of_original_plane_radical p.U p.K p.quotient p.onto p.kernel
    p.natural p.natural_onto p.natural_kernel p.equivariant p.card p.normalized p.outside

/-- Conditional downstream generation-two contradiction. The earlier
inputs construct an overgroup; the two independent row inputs close it. -/
theorem false_of_generationTwo_source_inputs
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G)
    (hrows : m.LinearAndG2Exclusion) (hplane : m.SymplecticPlaneRecognition) : False := by
  obtain ⟨c⟩ := m.exists_generationTwoOvergroup hout hnormal hzero hcontain
  obtain ⟨hr,hmodel⟩ := c.actor_models hout
  obtain ⟨hlinear,hg2⟩ := hrows c hr
  rcases hmodel with hlinearModel | hsymplecticModel | hg2Model
  · exact hlinear hlinearModel
  · obtain ⟨p⟩ := hplane c hr hsymplecticModel
    exact m.false_of_originalPlaneModel p
  · exact hg2 hg2Model

end SourceA5TensorModel

open SourceA5TensorModel

/-- Source tensor exclusion with exactly the five independent source
contracts still explicit. This is the assembly interface, not the final theorem. -/
theorem source_a5_tensor_exclusion_of_source_inputs
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : ∀ m : SourceA5TensorModel D e, m.NonzeroCoreCartanNormalization)
    (hzero : ∀ m : SourceA5TensorModel D e, m.ZeroCoreLineCentralization)
    (hcontain : A5PairContainment G)
    (hrows : ∀ m : SourceA5TensorModel D e, m.LinearAndG2Exclusion)
    (hplane : ∀ m : SourceA5TensorModel D e, m.SymplecticPlaneRecognition) :
    ¬ Nonempty (SourceA5TensorModel D e) := by
  rintro ⟨m⟩
  exact m.false_of_generationTwo_source_inputs hout (hnormal m) (hzero m)
    hcontain (hrows m) (hplane m)

end CFSG.Quasithin.Chapter10

module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.Setup
public import Theory.SpecificGroups.SU3.ExceptionalQuaternionRotation

/-!
# Marked hyperbolic coordinates for the exceptional outer involution

This interface records an actual map of the hyperbolic unitary plane into the
ambient group, its scalar marker, the image of its cyclic torus, and the
ambient implementation of its field action. It includes neither a conjugator
nor an inversion or centralizer-abelianness conclusion. The map may have the
odd scalar kernel of the projective ternary block embedding.

The source-model producer must identify the supplied cyclic core and the
exceptional pair in these coordinates. The separate quaternion calculation
then constructs the fusion witness. This is a conditional interface for
Aschbacher--Smith E.1.14(7), p.214, and Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open Matrix.UnitaryQuaternionRotation
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection

variable {G F : Type*} [Group G] [Field F]

/-- A marked unitary-plane realization of a supplied cyclic core and its
exceptional pair. No injectivity is imposed on the projective block map. -/
structure HyperbolicCoordinates {L T : Subgroup G} {z : G}
    (d : CyclicCoreData L T z) (J : HermitianForm 2 F) where
  form_eq : J.form = !![0, 1; 1, 0]
  two_ne_zero : (2 : F) ≠ 0
  r : Fˣ
  r_conj : J.conj (r : F) = -(r : F)
  i : F
  i_sq : i ^ 2 = -1
  i_conj : J.conj i = i
  embedding : J.unitarySubgroup →* G
  marker_eq : embedding (minusOne J form_eq) = z
  core_eq : d.core = zpowers (embedding (torus J form_eq r r_conj))
  swap_mem : embedding (swap J form_eq) ∈ T
  actor : G
  actor_action : ∀ u, actor * embedding u * actor⁻¹ =
    embedding (fieldConj J form_eq u)
  exceptional_pair : d.exceptional = actor ∨ d.exceptional = z * actor

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection

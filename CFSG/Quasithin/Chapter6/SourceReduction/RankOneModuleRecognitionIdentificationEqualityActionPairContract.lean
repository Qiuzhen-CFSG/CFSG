module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityAction

/-!
# Canonical pair output for the equality action

This structure specifies the output still to be constructed after the larger
G.6.4 action models have been excluded. It is not an earlier-source premise
and is not a proof of 6.2.13. Its producer must construct every field for the
normal closure of the actual layer inside the actual involution centralizer.

The quotient is K/O₂(K), while the embedded core P is a subgroup of H. The
center and pair intersection retain the subtype maps needed by the later
extension argument. In particular, this contract does not assert that H/P
is S₃ × C₂ or that P is self-centralizing.

Source: Aschbacher–Smith, 6.2.13, printed p.687 (PDF p.704), through the
application of 6.2.6 and the natural action of S₃ on U/⟨z⟩.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
variable {G : Type*} [Group G]

/-- Output contract for the canonical pair and core. A source assembly must
construct this package, rather than assume it as local analysis. -/
structure EqualityActionPairData (T L M R : Subgroup G) (z : G) : Prop where
  pair : ∃ g : G, g ∈ centralizer ({z} : Set G) ∧ g ∉ M ∧
    (equalityLayerClosure L R z).map (centralizer ({z} : Set G)).subtype =
      layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom ∧
    (layer L R ⊓ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex
      (layer L R) = 2 ∧
    ((layer L R).map (MulAut.conj g).toMonoidHom ⊓ normalizer (layer L R : Set G)).relIndex
      ((layer L R).map (MulAut.conj g).toMonoidHom) = 2 ∧
    layer L R ⊓ (layer L R).map (MulAut.conj g).toMonoidHom =
      (coreCenter (equalityCore L R z)).map (centralizer ({z} : Set G)).subtype
  quotient : Nonempty (((equalityLayerClosure L R z) ⧸ pCore 2 (equalityLayerClosure L R z))
    ≃* Equiv.Perm (Fin 3))
  plusType : Nonempty (QuaternionCentralProductData (equalityCore L R z))
  core_center : coreCenter (equalityCore L R z) = equalityLine z
  plane_le_core : equalityPlane T L R z ≤ equalityCore L R z
  natural_orbit : NaturalFourOrbit (equalityCore L R z) (equalityPlane T L R z)
  generation : centralizer ({z} : Set G) =
    (equalityLayerClosure L R z).map (centralizer ({z} : Set G)).subtype ⊔ T
  core_residual : pCore 2 (equalityLayerClosure L R z) ≤
    pResidual 2 (equalityLayerClosure L R z)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

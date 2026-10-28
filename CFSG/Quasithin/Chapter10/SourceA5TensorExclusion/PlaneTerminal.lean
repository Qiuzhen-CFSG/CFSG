module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Model
public import CFSG.Quasithin.Chapter10.SourceSetup
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.NoNaturalSubmodule

/-!
# The terminal plane-radical contradiction for the original tensor module

After the source Sp₄ block and plane-parabolic recognition, the quotient map
from the original local subgroup sends the original full module into the
actual plane radical. Its original natural quotient has kernel inside the
block module. The no-natural-submodule calculation therefore puts the full
module in that block module. Both have order256, so they coincide; the larger
component would then normalize the original full module, contradicting its
known normalizer.

The marked parabolic, natural quotient and containing component remain
explicit inputs from9.3.3--10. This module proves their terminal implication;
it does not assert that the tensor model alone produces those inputs.
Source: Aschbacher--Smith9.3, printed pp.734--735.
-/

public section
open Matrix Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
open ClassicalOrthogonal.FourPlusMatrix
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}

/-- The original natural quotient has zero image in the marked plane radical. -/
theorem source_fullModule_le_of_plane_radical (P U : Subgroup G)
    (hVP : D.fullModule ≤ P) [(D.fullModule.subgroupOf P).Normal]
    (q : P →* planeLocal (F := Binary.F)) (hq : Function.Surjective q)
    (hk : q.ker = U.subgroupOf P)
    (p : D.fullModule.subgroupOf P →* Multiplicative (Fin 2 → Binary.F))
    (hp : Function.Surjective p)
    (hpk : p.ker ≤ (U.subgroupOf P).comap (D.fullModule.subgroupOf P).subtype)
    (hR : (D.fullModule.subgroupOf P).map q ≤ Plane.radical)
    (he : ∀ (g : P) (v : D.fullModule.subgroupOf P),
      p (MulAut.conjNormal g v) =
        Multiplicative.ofAdd ((Plane.quotientMap (q g)).val *ᵥ (p v).toAdd)) :
    D.fullModule ≤ U := by
  have hcard : Nat.card Binary.F = 2 ^ 2 := by
    rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]
    norm_num
  have hker : p.ker ≤ (q.comp (D.fullModule.subgroupOf P).subtype).ker := by
    intro v hv
    have hh := hpk hv
    change v.val ∈ U.subgroupOf P at hh
    rw [← hk] at hh
    exact hh
  have hh := Plane.le_ker_of_natural_quotient hcard (by decide)
    (D.fullModule.subgroupOf P) q hq p hp hker hR he
  intro v hv
  have hmem := hh (show (⟨v, hVP hv⟩ : P) ∈ D.fullModule.subgroupOf P from hv)
  rw [hk] at hmem
  exact hmem

namespace SourceA5TensorModel

/-- The recognized plane-local configuration contradicts the original full normalizer. -/
theorem false_of_plane_radical
    (m : SourceA5TensorModel D e) (P U K : Subgroup G)
    (hVP : D.fullModule ≤ P) [(D.fullModule.subgroupOf P).Normal]
    (q : P →* planeLocal (F := Binary.F)) (hq : Function.Surjective q)
    (hk : q.ker = U.subgroupOf P)
    (p : D.fullModule.subgroupOf P →* Multiplicative (Fin 2 → Binary.F))
    (hp : Function.Surjective p)
    (hpk : p.ker ≤ (U.subgroupOf P).comap (D.fullModule.subgroupOf P).subtype)
    (hR : (D.fullModule.subgroupOf P).map q ≤ Plane.radical)
    (he : ∀ (g : P) (v : D.fullModule.subgroupOf P),
      p (MulAut.conjNormal g v) =
        Multiplicative.ofAdd ((Plane.quotientMap (q g)).val *ᵥ (p v).toAdd))
    (hU : Nat.card U = 256)
    (hK : K ≤ normalizer (U : Set G)) (hKM : ¬ K ≤ D.maximalLocal) : False := by
  have hVU := source_fullModule_le_of_plane_radical P U hVP q hq hk p hp hpk hR he
  have heq : D.fullModule = U := Subgroup.eq_of_le_of_card_ge hVU
    (by rw [hU, m.card_fullModule])
  apply hKM
  rwa [← heq, source_fullModule_normalizer D] at hK

end SourceA5TensorModel
end CFSG.Quasithin.Chapter10

module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.RankOne
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Coroots
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.Transport
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.Matching
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.TorusConjugacy

/-!
# Comparing concrete rank-one charts with an arbitrary F4 root model

Torus conjugacy and uniqueness at the concrete root weights identify each
actual opposite pair with a conjugated literal pair. Transporting a literal
SL₂ chart then supplies its actual parametrizations, regular SL₂ morphism,
and diagonal containment in the model torus. The displayed four roots need
not belong to the model's chosen base. Neither Cartan normalization nor an
identification with the stored coroot is used.

The conditional comparison remains available. The concrete torus-conjugacy,
root-weight uniqueness, and literal-chart theorems discharge all three of
its premises in characteristic two. This gives the four charts for every
supplied F4 root model, and in particular over the algebraic closure of the
finite field used for Ree F4. Neither semisimplicity nor the supplied
coroot-product isomorphism is needed for this geometric construction.

Sources: GLS3 1.9.5(b)--(d), Remarks 1.9.6, and the defining formulas of
1.12.1, `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
universe u

namespace Theory.AlgebraicGroup.RootSystemModel
open StandardRootSystem
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

/-- Concrete charts give charts for the four actual F4 pairs after the two
geometric comparison inputs have been supplied. All three producer premises
must be discharged before asserting unconditional chart existence. -/
theorem f4SimpleRoot_nonempty_sl2Chart_of_concrete
    (M : RootSystemModel typeF4RootPairingULift (F4Chevalley.Carrier (k := k)))
    (hconj : ∃ g : Variety.Point (F4Chevalley.Carrier (k := k)),
      M.torus = (F4Chevalley.splitTorus (k := k)).conjugate g)
    (hunique : ∀ (r : F4Chevalley.Root)
        (Y : ClosedSubgroup (F4Chevalley.Carrier (k := k))),
      IsTorusRootSubgroup F4Chevalley.splitTorus Y →
      RootWeightEquation F4Chevalley.splitTorus Y (F4Chevalley.rootWeight r) →
      Y = F4Chevalley.rootSubgroup r)
    (hcharts : ∀ r : F4Chevalley.Root,
      Nonempty (BinaryOppositeRootSL2Chart (F4Chevalley.splitTorus (k := k))
        (F4Chevalley.rootSubgroup r)
        (F4Chevalley.rootSubgroup (typeF4RootPairing.reflectionPerm r r))))
    (i : Fin 4) :
    Nonempty (BinaryOppositeRootSL2Chart M.torus
      (M.rootData.rootSubgroup (M.f4SimpleRoot i))
      (M.rootData.rootSubgroup (M.rootData.neg (M.f4SimpleRoot i)))) := by
  obtain ⟨g, hg⟩ := hconj
  obtain ⟨r, hr, hn⟩ := M.rootData.f4_oppositePair_eq_conjugate
    M.realization M.f4RootIndex g hg hunique (M.f4SimpleRoot i)
  rw [hr, hn, hg]
  obtain ⟨C⟩ := hcharts r
  exact ⟨C.conjugate g⟩

/-- Each displayed simple root of an arbitrary actual F4 model has a regular
SL₂ chart for its opposite pair, with its diagonal image in the model torus.
Concrete conjugacy, root-weight uniqueness and literal charts discharge all
comparison premises; no alignment with the model's chosen base is required. -/
theorem f4SimpleRoot_nonempty_sl2Chart
    (M : RootSystemModel typeF4RootPairingULift (F4Chevalley.Carrier (k := k)))
    (i : Fin 4) :
    Nonempty (BinaryOppositeRootSL2Chart M.torus
      (M.rootData.rootSubgroup (M.f4SimpleRoot i))
      (M.rootData.rootSubgroup (M.rootData.neg (M.f4SimpleRoot i)))) :=
  M.f4SimpleRoot_nonempty_sl2Chart_of_concrete
    (F4Chevalley.TorusConjugacy.model_torus_conjugate M)
    F4Chevalley.concreteRootSubgroup_eq
    F4Chevalley.ConcreteCharts.literalRootSL2Charts i

/-- The four actual opposite-root charts over the algebraic closure of the
finite field in the Ree F4 construction, retaining the source semisimplicity
hypothesis. Cartan normalization and comparison with the stored coroot are
separate assertions, not premises of chart existence. -/
theorem f4SimpleRoot_nonempty_sl2Chart_of_semisimple
    {E : Type u} [Field E] [Finite E] [CharP E 2]
    (M : RootSystemModel typeF4RootPairingULift
      (F4Chevalley.Carrier (k := AlgebraicClosure E)))
    (_hsemi : IsSemisimpleAlgebraicGroup
      (F4Chevalley.Carrier (k := AlgebraicClosure E)))
    (i : Fin 4) :
    Nonempty (BinaryOppositeRootSL2Chart M.torus
      (M.rootData.rootSubgroup (M.f4SimpleRoot i))
      (M.rootData.rootSubgroup (M.rootData.neg (M.f4SimpleRoot i)))) :=
  M.f4SimpleRoot_nonempty_sl2Chart i

end Theory.AlgebraicGroup.RootSystemModel

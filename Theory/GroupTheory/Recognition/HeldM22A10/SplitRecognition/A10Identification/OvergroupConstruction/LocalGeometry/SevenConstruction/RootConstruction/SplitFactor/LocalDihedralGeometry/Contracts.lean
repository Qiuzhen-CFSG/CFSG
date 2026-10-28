module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.Conjugation
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.ModelSylow

/-!
# Marked local isomorphisms for Held's root calculation

The first input identifies the full involution centralizer with its concrete
ten-point model, preserving the central involution. The second is a finite
permutation-group calculation: the centralizer of an element of order three
in that model is C3 times the seven-point involution centralizer.

These are mathematical intermediate contracts, not existence assertions.
Their producers need neither root quotient recognition nor the odd core.
The local product records both distinguished elements, so the subsequent
Sylow and quotient arguments apply to the literal ambient subgroups.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry

public abbrev MuModel : Subgroup (alternatingGroup (Fin 10)) :=
  centralizer ({doubleTransposition} : Set (alternatingGroup (Fin 10)))

@[expose] public def modelMu : MuModel :=
  ⟨doubleTransposition, mem_centralizer_singleton_iff.mpr rfl⟩

@[expose] public def modelMuAt (c : MuModel) : centralizer ({c} : Set MuModel) :=
  ⟨modelMu, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp c.property).symm)⟩

@[expose] public def modelRootAt (c : MuModel) : centralizer ({c} : Set MuModel) :=
  ⟨c, mem_centralizer_singleton_iff.mpr rfl⟩

public abbrev LocalProductModel := Multiplicative (ZMod 3) × sevenInvolutionCentralizer

/-- The finite calculation to be proved for every element of order three
in the concrete involution centralizer. -/
public structure ModelThreeCentralizer (c : MuModel) where
  equiv : centralizer ({c} : Set MuModel) ≃* LocalProductModel
  involution : equiv (modelMuAt c) = (1, sevenCentralInvolution)
  root : (equiv (modelRootAt c)).2 = 1

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e)

/-- The full source involution centralizer, with its central involution marked. -/
public structure MarkedMuModel where
  equiv : muCentralizer D e ≃* MuModel
  involution : equiv (centralMu D e) = modelMu

/-- Actual local product coordinates, with the root in the odd factor and
pi*mu equal to the central involution of the seven-point factor. -/
public structure LocalProduct where
  equiv : intersection D e L ≃* LocalProductModel
  involution : equiv (intersectionInvolution D e L) = (1, sevenCentralInvolution)
  root : (equiv (intersectionRoot D e L)).2 = 1

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry


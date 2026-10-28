module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.Assembly
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.ModelTransport

/-!
# Conditional assembly of Held's local dihedral geometry

Marked product coordinates give the order-72 intersection, a dihedral Sylow
subgroup in the central root quotient, and its actual involution centralizer.
The two model constructors are explicit inputs here. `SourceAssembly`
discharges them using the full mu-centralizer model and both cubic cycle types.
Keeping these reductions below those constructors avoids a circular import
while preserving the original public theorem names.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry

variable {G : Type*} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e)

/-- Assemble all three local conclusions from actual marked product coordinates.
Existence of those coordinates remains an obligation of the source assembly. -/
public theorem local_geometry_of_localProduct (P : LocalProduct D e L) :
    Nat.card (centralizer ({pi D e * mu D e} : Set G) ⊓ rootCentralizer D e L : Subgroup G) = 72 ∧
    (∃ S : Sylow 2 (rootQuotient D e L), Nonempty (S ≃* DihedralGroup 4)) ∧
    (∃ t : rootQuotient D e L, orderOf t = 2 ∧
      Nonempty (centralizer ({t} : Set (rootQuotient D e L)) ≃* sevenInvolutionCentralizer)) :=
  ⟨P.card D e L, P.quotient_sylow D e L,
    quotientInvolution D e L, quotientInvolution_order D e L,
    ⟨P.quotientCentralizerEquiv D e L⟩⟩

/-- The source conclusions follow from two independent model constructions:
the marked full involution centralizer and its order-three centralizers. -/
public theorem local_geometry_of_models
    (hmu : Nonempty (MarkedMuModel D e))
    (hmodel : ∀ c : MuModel, orderOf c = 3 → Nonempty (ModelThreeCentralizer c)) :
    Nat.card (centralizer ({pi D e * mu D e} : Set G) ⊓ rootCentralizer D e L : Subgroup G) = 72 ∧
    (∃ S : Sylow 2 (rootQuotient D e L), Nonempty (S ≃* DihedralGroup 4)) ∧
    (∃ t : rootQuotient D e L, orderOf t = 2 ∧
      Nonempty (centralizer ({t} : Set (rootQuotient D e L)) ≃* sevenInvolutionCentralizer)) := by
  obtain ⟨M⟩ := hmu
  obtain ⟨P⟩ := exists_localProduct_of_muModel D e L M hmodel
  exact local_geometry_of_localProduct D e L P

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry

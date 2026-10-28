module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Selection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Prime
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Attainment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Components
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.HallOrder
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.LinearAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.SymplecticAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Equal
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Section
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Contained
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.CoreImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.AlternatingResidual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.CommonBorel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.RadicalAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.PrimeFrattini
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.SymplecticDerived
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.OddBlock
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.PrimeSelection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Witness.OddExtension
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Witness.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Witness.G2Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Assembly

/-!
# Chosen-flag consumers of the outside component products and selection

All groups below come from the original field flag via ofFlag. The full
11.3.2 implication supplies fixed-space vanishing. The actual normalizer
and centralizer products and the residual-compatible H choice then follow
from the literal quotient-action proofs.

The prime PSL₂ branch is excluded from the preceding radical containment.
The re-exported Models.Source application discharges the outer-group model
calculation from the surviving source list. Witness.Equal constructs the
actual R₁ O²(H) carrier, its escape and R₁-Sylow subgroup when K=L₁.
Generation.Attainment proves the positive attained lower bounds;
Generation.Components constructs the E.2.2 component and the faithful
Hall actor in the quotient kernel for this row. Generation.HallOrder
proves seed normalization and Hall-order coprimality for all three original
natural equality rows. Generation.LinearAction, SymplecticAction and G2Action
prove n(H)=1 for every outside H in their respective equality rows, through
the literal natural actions and quotient maps. Generation.Equal combines
them and supplies the selected H together with its actual R₁-Sylow carrier.
Generation.Section restricts the literal K-quotient kernel to the first
residual, proves generation one in the quotient-centralizing branch without
K=L₁, and constructs a selected H whenever that kernel escapes M. For an
arbitrary H it reduces large generation to an actual escaping component
contained in K. These retain the exact OddKernelNormalizer input only for
Hall faithfulness.
Generation.Contained puts R₁ in O₂(H) in that remaining case. It proves
generation one and the actual selected-H application when N_G(R₁)≤M;
the earlier 11.1.5 alternative leaves only its field-four block branch.
Generation.CoreImage identifies O₂(H)=R₁ and the normal escaping component
with O²(H). Its literal radical quotient must be A₅: PrimeResidual excludes
the full prime-PSL₂ image above five using genuine E-generation. The selected
H receives this same alternative, retaining the full solvable kernel.
Generation.PrimeSelection constructs a solvable outside H in the strict
prime row from the actual involution centralizer above R₁. Combining it
with the equality and odd-extension choices supplies a source-selected H
with n(H)=1 in every surviving row, retaining its literal O² alternative.
Generation.AlternatingResidual strengthens the remaining case to n(H)=2,
with full two-core quotient A₅ or S₅ and an actual faithful cubic Hall actor
in L∩K whose normalizer escapes M. The universal bound n(H)≤2 follows; the final configuration is excluded
by SymplecticDerived and OddBlock below.
Generation.CommonBorel identifies the actual intersection H∩L₁T with H∩M
and the cubic–Sylow product BT. It has index five in both original sides,
and its normal core in each is exactly R₁. Their join therefore normalizes
R₁, retaining the ambient action needed for the remaining exclusion.
Generation.RadicalAction proves O₂(N_G(R₁))=R₁ and C_G(R₁)≤R₁. The literal
action on R₁/Φ(R₁) has kernel exactly R₁. Its two original A₅/S₅ images
remain distinct, with the same Sylow image and their index-five intersection.
Generation.PrimeFrattini proves that the remaining prime-PSL₂ branch
forces |R₁/Φ(R₁)|>256: the common Sylow image excludes sixteen from the
full action order, and the small general-linear order excludes every
remaining prime parameter. Its small-action variant applies to any normalized
elementary subgroup on which K acts nontrivially. Generation.SymplecticDerived
puts [R₁,R₁] inside V, bounds its order by q⁴ and exhibits nontrivial point-root
action. At q=4 this excludes the prime-PSL₂ row and proves n(H)=1 for every
original outside H in that row, using the exact earlier 11.1.5 alternative.
Generation.OddBlock uses the original Cartan to put V in O₂(KT). Shortness
then makes the actual L₁ map to odd SL₂ factor through the binary point-local
model, whose image must be trivial. Its solvable kernel contradicts the local
membership of L₁. This closes the odd-extension row, proves n(H)=1 for every
original outside H, and supplies the selected-H application with its O² alternative.
Witness.OddExtension
constructs the source odd-extension H and its R₁-Sylow witness with both
generation parameters equal to one. Witness.NormalSection applies rank-one
weak closure inside the normal R₁O²(H) carrier. With the literal earlier
G₂ weak-closure clauses it closes the equality row and proves the smaller
carrier's generation bound. Witness.Source assembles the original outside
R₁-Sylow witness and feeds it to E.3.19 for every surviving source row.
Witness.G2Source discharges those G₂ closure clauses from the original
preceding flag and component inputs and feeds the constructed R₁O²(H)
witness to the completed source rank-one contradiction. Outside.Source applies
the proved OddKernelNormalizer on the same chosen module, discharging Hall
faithfulness in the products, universal generation-one theorem and G₂ witness.
Outside.Assembly supplies that theorem to the original component reduction,
selected-source and marked endgame consumers. Only the preceding geometry
remains with its registered producers and final assembly owner.
Source: Aschbacher--Smith, 11.4.3--11.5.1, printed pp.778--779.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- Both source products on the original chosen flag, with 11.4.1(1)
discharged from its earlier sources. Only the outer model input is extra. -/
theorem ofFlag_products
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H₀ : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H₀))
    (he : (ofFlag S f X z H₀).Kz = (ofFlag S f X z H₀).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (ho : ChapterE.IsTwoClosed
      (MulAut.Outer ((ofFlag S f X z H₀).K ⧸ pCore 2 (ofFlag S f X z H₀).K)))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ H, Hypothesis1131At D S (c.binarySubspace (f.space 0)) H →
      Proposition1132At D S (c.binarySubspace (f.space 0)) H) :
    let E := ofFlag S f X z H₀
    (∀ g ∈ Gz E, ∃ k ∈ E.K, ∃ y ∈ Yz E, ∃ m ∈ Mz E, g = k * y * m) ∧
      (∀ g ∈ E.G₁, ∃ k ∈ E.K, ∃ y ∈ E.Y, ∃ m ∈ E.M₁, g = k * y * m) := by
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  exact ⟨point_product _ h he hNT ho,
    line_product _ h (f.invariant 0) hf hNT ho⟩

/-- The selected subgroup is inserted into the same source geometry, with
both alternatives using its literal two-residual. No generation bound is assumed. -/
theorem ofFlag_exists_selected_H
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H₀ : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H₀))
    (he : (ofFlag S f X z H₀).Kz = (ofFlag S f X z H₀).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (ho : ChapterE.IsTwoClosed
      (MulAut.Outer ((ofFlag S f X z H₀).K ⧸ pCore 2 (ofFlag S f X z H₀).K)))
    (h1132 : ∀ H, Hypothesis1131At D S (c.binarySubspace (f.space 0)) H →
      Proposition1132At D S (c.binarySubspace (f.space 0)) H) :
    ∃ H, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      H ≤ Gz (ofFlag S f X z H) ∧ SelectedResidualAlternative (ofFlag S f X z H) := by
  exact exists_selected_H (ofFlag S f X z H₀) h he hNT ho h1132

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside

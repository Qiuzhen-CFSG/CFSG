module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Intersections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Calculations
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Path
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Kernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Layer

/-!
# The complete first source calculations

All five clauses of (4.5.1) hold on the chosen source path, at the three
forward and three reversed centers. The intersection calculation and the
bound |H| ≤ 4 combine with the kernel and second-layer calculations to give
the full record, including |H| = 4. The literal quotient map, relative
B-normality and setwise products are retained; the subgroup containment is
also derived from the setwise-product containment.

The path constructor uses the preceding regular extension and replacement
to supply every turn, including the one at index twelve. Consequently
`sourcePath_firstFacts_nonempty` constructs both the path and all its first
facts from LocalSource, CommonFacts and the explicit preceding (4.4) input
Earlier. The parent core-factor assembly retains the discharge of Earlier.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1), printed p.896.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem firstFacts_of_calculations (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c d e f t : Vertex R} (ha : color R a = false)
    (hc : ⁅V R a, V R d⁆ = H R a ⊓ H R d)
    (hn : Nat.card (⁅V R a, V R d⁆ : Subgroup (FreeAmalgam R)) = 2)
    (kernel : First.KernelCalculation R geometry a e f)
    (layer : (hatW R a c d : Set (FreeAmalgam R)) * (Q R d : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R)))
    (lower : 4 ≤ Nat.card (H R a)) : FirstFacts R geometry a c d e f t where
  commutator_eq := hc
  commutator_card := hn
  intersection_le := by
    intro x hx
    obtain ⟨z, hz, q, hq, rfl⟩ := kernel.intersection_product_le hx
    exact (Z R a ⊔ Q R f).mul_mem
      ((show Z R a ≤ Z R a ⊔ Q R f from le_sup_left) hz)
      ((show Q R f ≤ Z R a ⊔ Q R f from le_sup_right) hq)
  intersection_product_le := kernel.intersection_product_le
  B_le := kernel.B_le
  B_normal := kernel.B_normal
  quotient_centralizer := kernel.quotient_centralizer
  hatW_product := layer
  H_card := le_antisymm (H_card_le_four common earlier ha) lower

/-- All six first-calculation records, conditional precisely on the two remaining
calculation families. Source-path existence is not supplied by this constructor. -/
theorem firstFactsOnPath_of_remaining_calculations (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a)
    (kernel : First.KernelFactsOnPath R geometry p)
    (layer : First.LayerFactsOnPath R p) : FirstFactsOnPath R geometry p where
  forward := by
    intro i hi hi2 hi6
    obtain ⟨hc, hn⟩ := p.first_commutator source common earlier hi hi2 (by omega)
    exact firstFacts_of_calculations common earlier (p.even_color hi (by omega)) hc hn
      (kernel.forward i hi hi2 hi6) (layer.forward_product i hi hi2 hi6)
      (layer.H_card_lower _ (p.even_color hi (by omega)))
  backward := by
    intro i hi hi8 hi12
    obtain ⟨hc, hn⟩ := p.first_commutator_backward source common earlier hi hi8 hi12
    exact firstFacts_of_calculations common earlier (p.even_color hi (by omega)) hc hn
      (kernel.backward i hi hi8 hi12) (layer.backward_product i hi hi8 hi12)
      (layer.H_card_lower _ (p.even_color hi (by omega)))

/-- All clauses of (4.5.1), including the translated and reversed applications,
on any supplied source path. Both calculation families are constructed here. -/
theorem firstFactsOnPath (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) : FirstFactsOnPath R geometry p :=
  firstFactsOnPath_of_remaining_calculations source common earlier p
    (First.kernelFactsOnPath source common earlier p)
    (First.Layer.layerFactsOnPath source common earlier p)

/-- At each M-vertex, construct the chosen path and all five first-calculation
clauses in both required directions. The proposition-valued facts use PSigma. -/
theorem sourcePath_firstFacts_nonempty (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (a : Vertex R) (ha : color R a = false) :
    Nonempty (Σ' p : SourcePath R a, FirstFactsOnPath R geometry p) := by
  obtain ⟨p⟩ := sourcePath_nonempty source common earlier a ha
  exact ⟨⟨p, firstFactsOnPath source common earlier p⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early

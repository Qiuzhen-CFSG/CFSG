module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingGeometry
public import Theory.Representation.BinaryPermutation.SevenParabolic.Conjugation
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!+# Compatible coordinates for the ordinary A₇ marking

The local source argument must identify the actual KS action on the whole
U(K), the transposition image of R, the five-letter image of L, and the
full module [Ω₁Z(Λ),L]. These coordinates contain no marked-vector or
generation conclusion. The separate finite geometry argument constructs
those conclusions, after which the constructor below assembles the original
marking. Neither interface is asserted to follow from the source here.

Source: Aschbacher--Smith, original C.4.1(1) and 4.3.7, printed pp.151,616.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Simultaneous coordinates on the literal block, its ambient normalizer,
the original R and L, and the full module. The fixed letters are 0 and 1. -/
structure BlockAlternatingCoordinates (c : SourceConfiguration T L) where
  chart : BinaryPermutation.SevenParabolic.Ordinary.Chart
    (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))
    (c.K.map c.H.subtype)
    ((ChapterC.blockU (c.K.map c.H.subtype)).map (c.K.map c.H.subtype).subtype)
  kernel : chart.actor.ker =
    pCore 2 (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G)
  transposition : ((c.I.pCoreIn 2).subgroupOf
    (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map chart.actor =
      zpowers (Equiv.swap (0 : Fin 7) 1)
  five_image : (L.subgroupOf
    (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map chart.actor =
      (fixingSubgroup (alternatingGroup (Fin 7))
        ({0,1} : Set (Fin 7))).map (alternatingGroup (Fin 7)).subtype
  full_module :
    ⁅(ChapterC.blockU (c.K.map c.H.subtype)).map (c.K.map c.H.subtype).subtype,L⁆ =
      Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)

/-- The source placement and the two remaining local normalizer calculations.
Centrality of e₁₂ in SΛ is not a field. -/
structure BlockAlternatingLocalGeometry (c : SourceConfiguration T L) extends
    BlockAlternatingCoordinates c where
  factorization : (T : Subgroup G) = ((T : Subgroup G) ⊓ c.H) ⊔
    (L ⊔ (T : Subgroup G)).pCoreIn 2
  levi_normalizes :
    (pResidual 2 (c.K.map c.H.subtype ⊓ normalizer (c.I.pCoreIn 2 : Set G) : Subgroup G)).map
      (c.K.map c.H.subtype ⊓ normalizer (c.I.pCoreIn 2 : Set G)).subtype ≤
        normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)

/-- The vector and generation output of the finite seven-letter calculation. -/
structure BlockAlternatingVectorGeometry (c : SourceConfiguration T L) where
  z : G
  k : G
  z_ne : z ≠ 1
  z_two : z ^ 2 = 1
  z_commutator : z ∈
    ⁅(ChapterC.blockU (c.K.map c.H.subtype)).map (c.K.map c.H.subtype).subtype,
      c.I.pCoreIn 2⁆
  z_centralizes : z ∈ centralizer (L : Set G)
  k_mem : k ∈ c.K.map c.H.subtype
  conjugate_mem : MulAut.conj k⁻¹ z ∈
    Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)
  generation : c.K.map c.H.subtype = L ⊔ L.map (MulAut.conj k⁻¹).toMonoidHom

/-- Actual C.6 input, with the residual and quotient constructed from the
source coordinates rather than supplied as additional conclusions. -/
theorem BlockAlternatingLocalGeometry.pushingUp {c : SourceConfiguration T L}
    (d : BlockAlternatingLocalGeometry c) (ha : ChapterC.IsAlternatingBlock c.K 7) :
    Nonempty (ChapterC.Section06.AlternatingCentralVector.Input
      (c.K.map c.H.subtype) (c.I.pCoreIn 2) ((T : Subgroup G) ⊓ c.H)
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)) :=
  c.alternating_pushingUp_input_of_action ha d.factorization d.chart.actor
    d.kernel d.chart.component_image d.transposition d.levi_normalizes

/-- Conditional assembly of the two separately owned pieces of the marking.
The source theorem still requires constructing both arguments. -/
theorem SourceConfiguration.alternating_marking_of_geometry
    (c : SourceConfiguration T L) (ha : ChapterC.IsAlternatingBlock c.K 7)
    (d : BlockAlternatingLocalGeometry c) (v : BlockAlternatingVectorGeometry c) :
    Nonempty (BlockAlternatingMarking c) := by
  obtain ⟨h⟩ := d.pushingUp ha
  exact ⟨{
    pushingUp := h
    factorization := d.factorization
    z := v.z
    k := v.k
    z_ne := v.z_ne
    z_two := v.z_two
    z_commutator := v.z_commutator
    z_centralizes := v.z_centralizes
    k_mem := v.k_mem
    conjugate_mem := v.conjugate_mem
    generation := v.generation }⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness

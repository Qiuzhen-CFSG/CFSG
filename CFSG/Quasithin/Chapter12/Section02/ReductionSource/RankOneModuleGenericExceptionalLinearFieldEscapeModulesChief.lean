module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesFiltration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChief
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.FixedIndex

/-!
# The original cubic chief count and the Fitting application

The Cartan and LocalData select a moving element of the actual cubic.
On its G.2.3 two-core, the cubic fixed-index length and every complete
chief count of I are rank(A*)+1 for the same faithful projection used
by the existing filtration and constituent arguments.

The same cubic length is transported to the original Sylow subgroup T∩L
using the Cartan normalizers. A lower bound of three there supplies the
strict rank inequality to the D.2.13 consumer. That lower bound and
[A,S₂]≤⟨z⟩ remain explicit source obligations of this task. No constituent
is reselected, and neither abelianness nor a cubic lower bound is asserted.

Source: Aschbacher--Smith 5.1.23, printed pp.645--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The count is constructed for the actual cubic and the original action image. -/
theorem linear_cubic_nonabelian_chief_count
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    let s := linear_cubic_centralizer_setup h d
    ∃ g ∈ C, g ∉ normalizer (zpowers z : Set G) ∧
      let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
      conjugationCubicLength C (S.S g) = rank E + 1 ∧
      ∀ a : ChiefSeries (S.I g), a.head = ⊥ → a.last = ⊤ →
        a.noncentralTwoCount = rank E + 1 := by
  let s := linear_cubic_centralizer_setup h d
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  obtain ⟨g,hg,hgn⟩ := d.exists_moving_cubic
  have hga : g ∈ CubicEscape.actor T C := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨hI,_,_,_,_⟩ := binary_source_inputs s b s.U_normal_in_T.1 g hga hgn
  have hCI : C ≤ (CubicEscape.setup T (centralizer ({z} : Set G)) C z).I g :=
    (le_conjugateSpanBy C (T : Subgroup G)).trans (le_sup_left.trans hI.ge)
  exact ⟨g,hg,hgn,
    SpanAction.binary_cubic_length_eq_opposite_rank_add_one s b g hga hgn C c.cubic_card hCI,
    fun a ha0 ha1 => SpanAction.binary_complete_noncentral_chief_count s b g hga hgn a ha0 ha1⟩

/-- The count on the constructed core equals the cubic fixed-index length
on the original Sylow subgroup T∩L. -/
theorem linear_cubic_nonabelian_sylow_length
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    let s := linear_cubic_centralizer_setup h d
    conjugationCubicLength C ((T : Subgroup G) ⊓ L) =
      rank (((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)) + 1 := by
  let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
  let s := linear_cubic_centralizer_setup h d
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  let Q := (T : Subgroup G) ⊓ L
  have hga : g ∈ S.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨hI,_,_,_,_⟩ := binary_source_inputs s b s.U_normal_in_T.1 g hga hgn
  have hCI : C ≤ S.I g :=
    (le_conjugateSpanBy C (T : Subgroup G)).trans (le_sup_left.trans hI.ge)
  have hCL : C ≤ L := c.cubic_le.trans (c.left_le.trans inf_le_left)
  have hCQ : C ≤ normalizer (Q : Set G) := c.cubic_le.trans (c.left_le.trans inf_le_right)
  have hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer D.sylow_normalizes_component).trans
      inf_normalizer_le_normalizer_inf
  have hLIQ : S.L ≤ normalizer (Q : Set G) :=
    conjugateSpanBy_le hCQ (hTQ.trans (normalizer (Q : Set G)).le_normalizer)
  have hIQ : S.I g ≤ normalizer (Q : Set G) := by
    rw [hI]
    exact sup_le hLIQ (s.U_normal_in_T.1.trans hTQ)
  have hTU : (T : Subgroup G) ≤ normalizer (S.U : Set G) :=
    (normal_subgroupOf_iff_le_normalizer s.U_normal_in_T.1).mp s.U_normal_in_T.2
  have hTI : (T : Subgroup G) ≤ normalizer (S.I g : Set G) := by
    rw [hI]
    exact (le_inf s.T_normalizes_L hTU).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hthree : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using c.cubic_card)
  have hQtwo : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  have hlenQ := CubicComparison.intersection_length_eq C Q (S.I g)
    hthree hQtwo hCI (inf_le_left.trans hTI) hIQ
  have hcap : Q ⊓ S.I g ≤ S.S g :=
    le_pCoreIn_of_normalizes (hQtwo.to_le inf_le_left) inf_le_right
      ((le_inf hIQ (S.I g).le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hlower : conjugationCubicLength C Q ≤ conjugationCubicLength C (S.S g) := by
    rw [← hlenQ]
    exact conjugationCubicLength_mono C hcap
  have hST : S.S g ≤ (T : Subgroup G) :=
    (binary_S_le_LT_core s.U_normal_in_T.1 g hga
      (binaryStarEquiv s.toBaseHypothesis b s.U_normal_in_T.1)
      (binary_source_star_generation s b s.U_normal_in_T.1 g hga hgn)).trans
        s.toBaseHypothesis.binary_core_le_T
  have hCS : C ≤ normalizer (S.S g : Set G) := hCI.trans (S.binary_core_normalized g)
  have hCN : C ≤ normalizer (S.S g ⊓ L : Set G) :=
    (le_inf hCS (hCL.trans L.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hSN : S.S g ≤ normalizer (S.S g ⊓ L : Set G) :=
    (le_inf (S.S g).le_normalizer (hST.trans D.sylow_normalizes_component)).trans
      inf_normalizer_le_normalizer_inf
  let : ((S.S g ⊓ L).subgroupOf (S.S g)).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hSN
  have hcomm : ⁅S.S g,C⁆ ≤ S.S g ⊓ L := le_inf
    (le_normalizer_iff_commutator_le_left.mp hCS)
    ((commutator_mono le_rfl hCL).trans
      (le_normalizer_iff_commutator_le_right.mp (hST.trans D.sylow_normalizes_component)))
  have hlenS := CubicComparison.length_eq_of_commutator_le C (S.S g) (S.S g ⊓ L)
    hthree (T.isPGroup'.to_le hST) inf_le_left hCS hCN hcomm
  have hupper : conjugationCubicLength C (S.S g) ≤ conjugationCubicLength C Q := by
    rw [← hlenS]
    exact conjugationCubicLength_mono C (le_inf (inf_le_left.trans hST) inf_le_right)
  exact (le_antisymm hlower hupper).trans
    (SpanAction.binary_cubic_length_eq_opposite_rank_add_one s b g hga hgn C c.cubic_card hCI)


/-- A cubic fixed-index length of at least three on the original T∩L
supplies rank(A*)>1 in the actual minimum-offender application of D.2.13.
The lower bound and middle-layer fixedness still require their ambient proofs. -/
theorem linear_cubic_fitting_of_sylow_cubic_length
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hfix : let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      ⁅conjugate (S.W g) g,S.S₂ g⁆ ≤ zpowers z)
    (hthree : 3 ≤ conjugationCubicLength C ((T : Subgroup G) ⊓ L)) :
    let s := linear_cubic_centralizer_setup h d
    let i := inclusion (point_centralizer_le_residual_normalizer
      h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne)
    let C₁ := ((linearResidualAction H).comp i).ker
    let N := C₁.map (SpanAction.projection s)
    ∃ E : Subgroup (SpanAction.Actor s),
      E ≤ ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map
        (SpanAction.projection s) ∧
      E ∈ ChapterD.QhatStar (SpanAction.representation s) ∧
      (fittingSubgroup N).map N.subtype ≤ centralizer (E : Set (SpanAction.Actor s)) := by
  have hc := linear_cubic_nonabelian_sylow_length D h hpsl c d hne g hg hgn
  have hm : let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      1 < rank (((conjugate (S.W g) g).subgroupOf S.H).map
        (SpanAction.projection (linear_cubic_centralizer_setup h d))) := by
    rw [hc] at hthree
    omega
  exact linear_cubic_fitting_of_opposite_geometry D h hH hK hnf hlinear hpsl c d hne
    g hg hgn hfix hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

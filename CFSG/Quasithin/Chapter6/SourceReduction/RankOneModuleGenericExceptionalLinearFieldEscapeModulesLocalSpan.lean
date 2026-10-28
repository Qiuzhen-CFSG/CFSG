module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesRankOne
public import Theory.Representation.BinaryConjugationSection.FixedMoving

/-!
# Fixed opposite elements locate the original local span

In the G.2.3 natural S₃ quotient, an element of U outside W moves every
nonzero vector of the opposite summand. Thus an element of U commuting
modulo S₂ with a nontrivial opposite element must belong to W.

Apply this to a nontrivial opposite-image subgroup fixing the original
H-span modulo ⟨z⟩. It puts that span in W. The original plane centralizes
S, so its H-span is then abelian. The local kernel computation also
constructs the literal faithful H/O₂(H)-action whenever the H-span is
elementary. No conclusion about the full centralizer span is assumed.

Source: Aschbacher--Smith G.2.3 and 5.1.23, printed pp.333--334,645--646,
refs/quasithin.pdf. The Chapter 12 application supplies the fixing subgroup
from the original local-core image, including when both opposite factors survive.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]

namespace SpanAction
variable {D : Setup G}

/-- Fixing a nonzero opposite vector forces an element of U into W. -/
theorem binary_opposite_fixed_mod_middle_le_W
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (x : G) (hx : x ∈ conjugate (D.W g) g) (hxE : x ∉ D.S₂ g)
    (u : G) (hu : u ∈ D.U) (hcomm : ⁅u,x⁆ ∈ D.S₂ g) :
    u ∈ D.W g := by
  have hUT := h.U_normal_in_T.1
  obtain ⟨hI, he, hnorm, hindex, hgI⟩ := binary_source_inputs h b hUT g hgL hgN
  obtain ⟨hN, hA, σ, d, hS, hprod, hVE, hES, hVC, hVN, hEN,
    hEC, hEE, hcoord, hfinite, hcompl, htensor, hcard, hmarks, hfix⟩ :=
    D.binary_source_clauses_three_to_seven h b hUT h.frattini_U_le_point
      g hgL hgN hI (binarySourceCoreEquiv h b hUT g hgL hgN) hnorm hindex
  let := hN
  let := hA
  have hXS : conjugate (D.W g) g ≤ D.S g := le_sup_right.trans hS.ge
  by_contra huw
  apply hxE
  let ui : D.I g := ⟨u, mem_sup_left hu⟩
  let xs : D.S g := ⟨x, hXS hx⟩
  have hxc : (d.coordinates xs).toAdd ∈ d.imageSpace (conjugate (D.W g) g) :=
    (d.mem_imageSpace_iff _ _).mpr ⟨xs, hx, rfl⟩
  have hxf : σ (D.binaryCoreProjection g
      (binarySourceCoreEquiv h b hUT g hgL hgN) ui) (d.coordinates xs).toAdd =
      (d.coordinates xs).toAdd := by
    let xa : D.S g := ⟨u * x * u⁻¹,
      (mem_normalizer_iff.mp (d.normalized ui.property) x).mp xs.property⟩
    have hz := (d.coordinates_eq_one_iff (xa * xs⁻¹)).mpr hcomm
    rw [map_mul, map_inv, mul_inv_eq_one] at hz
    exact (d.equivariant ui xs).symm.trans (congrArg Multiplicative.toAdd hz)
  have hxw : (d.coordinates xs).toAdd ∈ d.imageSpace (D.W g) := by
    rw [← (hmarks ui hu huw).1]
    exact sub_eq_zero.mpr hxf
  exact (d.coordinates_eq_one_iff xs).mp (hcompl.disjoint.le_bot ⟨hxw,hxc⟩)

end SpanAction

variable {T : Sylow 2 G} {H C : Subgroup G} {z : G}

/-- A nontrivial opposite fixer locates the original H-span in W. -/
theorem LocalData.local_span_le_W_of_opposite_fixer
    (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (b : (setup T (centralizer ({z} : Set G)) C z).BinaryNaturalData)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (F : Subgroup (SpanAction.Actor s))
    (hFE : F ≤ ((conjugate ((setup T (centralizer ({z} : Set G)) C z).W g) g).subgroupOf
       (centralizer ({z} : Set G))).map (SpanAction.projection s))
    (hF : F ≠ ⊥)
    (hfix : (SpanAction.conjugationSection s).imageSpace (setup T H C z).U ≤
      fixedSpace (SpanAction.representation s) F) :
    (setup T H C z).U ≤ (setup T (centralizer ({z} : Set G)) C z).W g := by
  let D := setup T (centralizer ({z} : Set G)) C z
  let q := SpanAction.conjugationSection s
  have hga : g ∈ D.L := le_conjugateSpanBy C (T : Subgroup G) hg
  have hHC : H ≤ centralizer ({z} : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  have hUU : (setup T H C z).U ≤ D.U := conjugateSpanBy_mono le_rfl hHC
  obtain ⟨a,ha⟩ := ne_bot_iff_exists_ne_one.mp hF
  obtain ⟨x,hx,he⟩ := hFE a.property
  have hxE : (x : G) ∉ D.S₂ g := by
    intro hm
    have hk : x ∈ (SpanAction.projection s).ker := by
      have hh : x ∈ (SpanAction.projection s).ker ⊓
          (conjugate (D.W g) g).subgroupOf D.H := by
        rw [SpanAction.binary_opposite_kernel s b g hga hgn]
        exact hm
      exact hh.1
    exact ha (Subtype.ext (he.symm.trans hk))
  intro u hu
  let u' : D.U := ⟨u,hUU hu⟩
  have hv : (q.coordinates u').toAdd ∈ q.imageSpace (setup T H C z).U :=
    (q.mem_imageSpace_iff _ _).mpr ⟨u',hu,rfl⟩
  have hf : (SpanAction.representation s) (SpanAction.projection s x)
      (q.coordinates u').toAdd = (q.coordinates u').toAdd := by
    rw [he]
    exact hfix hv a
  have hc : ⁅u,(x : G)⁆ ∈ D.V₁ :=
    (q.fixed_coordinate_iff_commutator_mem x u').mp hf
  exact SpanAction.binary_opposite_fixed_mod_middle_le_W s b g hga hgn x hx hxE
    u (hUU hu) ((s.point_le.trans
      (SpanAction.binary_opposite_commutator_filtration s b g hga hgn).2.2.2.2) hc)

/-- The literal local span is abelian once it lies in the opposite core. -/
theorem local_span_abelian_of_le_W
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (b : (setup T (centralizer ({z} : Set G)) C z).BinaryNaturalData)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hle : (setup T H C z).U ≤ (setup T (centralizer ({z} : Set G)) C z).W g) :
    IsMulCommutative (setup T H C z).U := by
  let D := setup T (centralizer ({z} : Set G)) C z
  have hga : g ∈ D.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨hI,_,hnorm,hi,_⟩ := binary_source_inputs s b s.U_normal_in_T.1 g hga hgn
  obtain ⟨_,_,_,_,_,_,_,_,hVC,_⟩ :=
    D.binary_source_clauses_three_to_seven s b s.U_normal_in_T.1 s.frattini_U_le_point
      g hga hgn hI (binarySourceCoreEquiv s b s.U_normal_in_T.1 g hga hgn) hnorm hi
  apply (conjugateSpanBy_commutative_iff (plane C z) H).mpr
  exact (hVC.trans inf_le_right).trans (centralizer_le (hle.trans inf_le_right))

/-- Construct the original faithful H/O₂(H)-action as soon as its span is elementary. -/
def LocalData.localSpanAction (d : LocalData T H C z)
    [IsElementaryAbelian 2 (setup T H C z).U] :
    Chapter15.Section03.AbelianAmalgam.LocalQuotientAction H
      (setup T H C z).U (zpowers z) := by
  letI : ((zpowers z).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer d.g2.H_le
  apply Chapter15.Section03.AbelianAmalgam.ModuleBound.localQuotientAction H
    (setup T H C z).U (zpowers z)
    (d.g2.point_le.trans (le_conjugateSpanBy _ _)) d.g2.U_le_H
    (le_normalizer_conjugateSpanBy _ _) d.g2.H_le
  rw [← d.local_projection_kernel]
  ext x
  change x ∈ centralizerModulo (⊤ : Subgroup H)
    ((setup T H C z).U.subgroupOf H) ((zpowers z).subgroupOf H) ↔
      SpanAction.projection d.g2 x = 1
  rw [mem_centralizerModulo_iff]
  constructor
  · rintro ⟨_,hx⟩
    apply (SpanAction.projection_eq_one_iff d.g2 x).mpr
    intro u hu
    exact hx ⟨u,d.g2.U_le_H hu⟩ hu
  · intro hx
    have hh := (SpanAction.projection_eq_one_iff d.g2 x).mp hx
    exact ⟨mem_top x,fun u hu => hh u hu⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape

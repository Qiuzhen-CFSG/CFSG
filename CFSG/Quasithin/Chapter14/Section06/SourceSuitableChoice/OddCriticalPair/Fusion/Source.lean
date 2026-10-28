module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Fusion.Geometry
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Fusion.Lifts
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Fusion.Nonfusion
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Fusion.Singular

/-!
# The original orthogonal crossing and its terminal application

The same chosen suitable vector is used throughout. The original normalizer
and local Sylow results exclude its fusion to the central line and, by the
singular centralizer comparison, to a singular vector. Nonsingular lift
transitivity supplies full fusion inside the moved module.

Critical-pair noncentrality gives a nonsingular point in the conjugate moved
module. Moving this point to the chosen vector preserves noncommutation,
and fusion supplies the required left-conjugation matching equation.
The terminal application reuses the full parabolic and core index; only
residual coordinates and the module-rank bound remain explicit for their owner.

The marked orthogonal action, critical pair, and suitability conditions are
permitted earlier-source inputs here; their construction remains with the
original source producers. No fusion, matching, crossing, or outside-centralizer
hypothesis is added.

Source: Aschbacher--Smith, 14.6.13 and 14.6.17(2--5), printed pp.1031--1036.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
private theorem critical_point_not_le_plane
    {H U Z Q Mc : Subgroup G} (d : SourceOrthogonalFourAction H U Z Q)
    (c : SourceOrthogonalCriticalPair d Mc) (u : G)
    (hZcard : Nat.card Z = 2) (hMc : Mc = centralizer (Z : Set G))
    (horbit : ∀ w ∈ d.plane c.first, w ∉ Z → ∃ k ∈ H, (MulAut.conj k) u = w)
    (hpoint : ∀ z ∈ Z, ¬ IsConj u z) :
    ¬ Z.map (MulAut.conj c.g).toMonoidHom ≤ d.plane c.first := by
  intro hle
  have hnot : ¬ Z.map (MulAut.conj c.g).toMonoidHom ≤
      Z := by
    intro hl
    have he : Z.map (MulAut.conj c.g).toMonoidHom =
        Z := by
      apply eq_of_le_of_card_ge hl
      rw [card_map_of_injective (MulAut.conj c.g).injective]
    apply c.outside
    apply hMc.ge
    exact normalizer_le_centralizer_of_card_two _ hZcard
      (mem_normalizer_iff_map_conj_eq.mpr he)
  obtain ⟨w,hw,hwz⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨k,hk,hku⟩ := horbit w (hle hw) hwz
  obtain ⟨z,hz,hzw⟩ := hw
  apply hpoint z hz
  apply (isConj_iff.mpr ⟨k, hku⟩).trans
  exact (isConj_iff.mpr ⟨c.g,hzw⟩).symm

private theorem critical_crossing_conjugate
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (Mc : Subgroup G) (c : SourceOrthogonalCriticalPair d Mc) (u : G)
    (horbit : ∀ w ∈ d.plane c.first, w ∉ D.V₁ →
      ∃ k ∈ D.H, (MulAut.conj k) u = w)
    (hnoPoint : ¬ D.V₁.map (MulAut.conj c.g).toMonoidHom ≤ d.plane c.first)
    (hfusion : ∀ x : G, (MulAut.conj x) u ∈ ⁅D.UH,D.H⁆ →
      ∃ k ∈ D.H, (MulAut.conj k) u = (MulAut.conj x) u) :
    ∃ g : G, u ∈ (⁅D.UH,D.H⁆).map (MulAut.conj g).toMonoidHom ∧
      (∃ k ∈ D.H, (MulAut.conj k) u = (MulAut.conj g⁻¹) u) ∧
      ¬ ⁅D.UH,D.H⁆ ≤ centralizer ((⁅D.UH,D.H⁆).map (MulAut.conj g).toMonoidHom : Set G) := by
  let U := D.UH
  let H := D.H
  let A := ⁅U,H⁆
  have hcross := OddCriticalPair.critical_pair_crosses h d Mc c hnoPoint
  obtain ⟨w,hw,hwz⟩ := SetLike.not_le_iff_exists.mp c.noncentral
  have hwW : w ∈ d.plane c.first :=
    (le_normalizer_iff_commutator_le_left.mp (c.normalizes.trans inf_le_right)) hw
  have hwAg : w ∈ A.map (MulAut.conj c.g).toMonoidHom :=
    OddCriticalPair.critical_commutator_le_moved_conjugate d Mc c hw
  obtain ⟨k,hk,hkw⟩ := horbit w hwW hwz
  let g' := k⁻¹ * c.g
  have huAg : u ∈ A.map (MulAut.conj g').toMonoidHom := by
    obtain ⟨a,ha,hea⟩ := hwAg
    refine ⟨a,ha,?_⟩
    have he := congrArg (MulAut.conj k⁻¹) (hea.trans hkw.symm)
    simpa [g',MulAut.conj_apply,mul_assoc] using he
  have hmatch : ∃ k ∈ H, (MulAut.conj k) u = (MulAut.conj g'⁻¹) u := by
    apply hfusion
    obtain ⟨a,ha,he⟩ := huAg
    rw [←he]
    simpa [MulAut.conj_apply,mul_assoc] using ha
  have hcross' : ¬ A ≤ centralizer (A.map (MulAut.conj g').toMonoidHom : Set G) := by
    intro hc
    apply hcross
    intro a ha b hb
    obtain ⟨v,hv,rfl⟩ := hb
    have ha' : (MulAut.conj k⁻¹) a ∈ A :=
      (normalizer_commutator_ge_right U H (H.inv_mem hk) a).mp ha
    have hc' := hc ha' ((MulAut.conj g') v) (mem_map_of_mem _ hv)
    have he := congrArg (MulAut.conj k) hc'
    simpa [g',MulAut.conj_apply,mul_assoc] using he
  exact ⟨g',huAg,hmatch,hcross'⟩

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))

include hG hempty hM hunique hmany hcard e hab H hH

private theorem source_orthogonal_crossing_of_singular_centralizers
    (d : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2))
    (c : SourceOrthogonalCriticalPair d Mc)
    (u : G) (hu : u ∈ d.plane c.first) (huz : u ∉ centralInvolutions T)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hsingular : ∀ w ∈ ⁅conjugateSpanBy (localModule T M) H,H⁆,
      (∀ i, w ∉ d.plane i) →
        IsPGroup 2 (H ⊓ centralizer ({w} : Set G) : Subgroup G) ∧
        Nat.card (T : Subgroup G) ≤ 2 * Nat.card (H ⊓ centralizer ({w} : Set G) : Subgroup G)) :
    Nonempty (SourceCrossingGeometry (localModule T M) H Mc u) := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let U := conjugateSpanBy (localModule T M) H
  let A := ⁅U,H⁆
  have huA : u ∈ A := d.plane_le c.first hu
  have hAU : A ≤ U := le_normalizer_iff_commutator_le_left.mp d.normalized
  have huU : u ∈ U := hAU huA
  have hHMc : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
      H hH.1 hH.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.2.trans hHMc
  have hQMcT : Mc.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] using
      pCoreIn_le_sylow Mc (T.subtype hTMc)
  have hQle : Mc.pCoreIn 2 ≤ H.pCoreIn 2 :=
    (le_inf (hQMcT.trans hH.1.2) le_rfl).trans (inf_pCoreIn_le_of_le 2 hHMc)
  have hmoveQ : ¬ H.pCoreIn 2 ≤ centralizer ({u} : Set G) :=
    fun hh => hmove (hQle.trans hh)
  have horbit (j : OrthogonalPlaneIndex) (w : G) (hw : w ∈ d.plane j)
      (hwz : w ∉ centralInvolutions T) :
      ∃ k ∈ H, (MulAut.conj k) u = w :=
    OddCriticalPair.nonsingular_lifts_conjugate h d c.first j ⟨u,huA⟩
      ⟨w,d.plane_le j hw⟩ hu hw huz hwz hmoveQ
  have hpoint (z : G) (hz : z ∈ centralInvolutions T) : ¬ IsConj u z :=
    source_suitable_not_isConj_point hG T hempty hM hunique hmany hcard e hab H hH
      u huU hindex hmove hproduct hU3 z hz
  have hSylow := (source_suitable_normalizer_of_local_normalizer
    hG T hempty hM hunique hmany hcard e hab H hH u huU hindex hmove hproduct hU3).2.1
  have hfour := (source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
    u huU hindex hmove hproduct).2.1
  have hfusion (x : G) (hx : (MulAut.conj x) u ∈ A) :
      ∃ k ∈ H, (MulAut.conj k) u = (MulAut.conj x) u := by
    have hc : IsConj u ((MulAut.conj x) u) := isConj_iff.mpr ⟨x,rfl⟩
    have hwz : (MulAut.conj x) u ∉ centralInvolutions T := fun hz => hpoint _ hz hc
    by_cases hs : ∃ i, (MulAut.conj x) u ∈ d.plane i
    · obtain ⟨i,hi⟩ := hs
      exact horbit i _ hi hwz
    · have hn : ∀ i, (MulAut.conj x) u ∉ d.plane i := not_exists.mp hs
      obtain ⟨hp,hsize⟩ := hsingular _ hx hn
      exact (OddCriticalPair.not_isConj_of_centralizer_size (T : Subgroup G)
        u ((MulAut.conj x) u) hSylow hfour _ hp inf_le_right hsize hc).elim
  have hMc := (plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard
    (plane_centralInvolutions_card T M hM.1.2 hcard e)).2.2.1
  have hnoPoint := critical_point_not_le_plane d c u
    (plane_centralInvolutions_card T M hM.1.2 hcard e) hMc (horbit c.first) hpoint
  obtain ⟨g',huAg,hmatch,hcross'⟩ := critical_crossing_conjugate h d Mc c u
    (horbit c.first) hnoPoint hfusion
  exact ⟨{
    A := A
    contained := hAU.trans (conjugateSpanBy_mono le_rfl hHMc)
    normalizes := normalizer_commutator_ge_right U H
    g := g'
    mem_conjugate := huAg
    matching := hmatch
    crossing := hcross' }⟩

end CFSG.Quasithin.Chapter14.Section06

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2))
    (critical : SourceOrthogonalCriticalPair d Mc)
    (u : G) (hu : u ∈ d.plane critical.first) (huz : u ∉ centralInvolutions T)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))

include hG hempty hM hunique hmany hcard e hab H hH d critical hu huz hindex hmove hproduct hU3

/-- Construct the crossing for the same chosen first-support suitable vector.
All singular and nonsingular fusion, central-line exclusion, and moved-module
noncommutation are proved from the stated earlier-source inputs. -/
theorem source_orthogonal_crossing :
    Nonempty (SourceCrossingGeometry (localModule T M) H Mc u) := by
  apply source_orthogonal_crossing_of_singular_centralizers hG T hempty hM hunique hmany
    hcard e hab H hH d critical u hu huz hindex hmove hproduct hU3
  intro w hw hplanes
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let h : D.Hypothesis :=
    source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  exact OddCriticalPair.singular_lift_centralizer_bound h d ⟨w,hw⟩ hplanes

/-- The source terminal application discharges crossing, parabolic action and
core index. Residual coordinates and module rank remain with their independent
owner; the earlier orthogonal markings retain their original source producer. -/
theorem source_terminal_witness_of_orthogonal_fusion
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (coordinates : SourceResidualSpanCoordinates (localModule T M) (centralInvolutions T)
      ((pResidual 2 ((source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab
        H hH).kernel (zpowers u))).map
        ((source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab
          H hH).kernel (zpowers u)).subtype)) :
    SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab := by
  obtain ⟨f⟩ := source_orthogonal_crossing hG T hempty hM hunique hmany hcard e hab H hH
    d critical u hu huz hindex hmove hproduct hU3
  let j := critical.first * Multiplicative.ofAdd (1 : ZMod 2)
  have hj : j ≠ critical.first := by
    have hh : ∀ i : OrthogonalPlaneIndex, i * Multiplicative.ofAdd (1 : ZMod 2) ≠ i := by decide
    exact hh critical.first
  exact source_terminal_witness_of_orthogonal_parabolic hG T hempty hM hunique hmany
    hcard e hab H hH d critical.first j hj u hu huz hindex hmove hproduct hU3 hrank coordinates f

end CFSG.Quasithin.Chapter14.Section06

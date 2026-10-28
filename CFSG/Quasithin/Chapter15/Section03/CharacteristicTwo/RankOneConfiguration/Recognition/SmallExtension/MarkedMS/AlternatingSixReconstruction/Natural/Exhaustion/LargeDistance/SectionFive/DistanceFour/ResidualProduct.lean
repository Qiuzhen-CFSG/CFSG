module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Kernel
public import Theory.GroupAction.SymmetricSixResidualProduct

/-!
# The whole residual-core product obstruction at distance four

For a nonabelian selected span P with a small forward Baumann slice, its
midpoint kernel Y has the same derived line as P. This line is fixed by
the starting stabilizer and is noncentral at the midpoint. Put
C = [Q_mid,Ltilde_mid], using the entire midpoint two-core.

Adjoining C to Y gives a subgroup normal in the midpoint stabilizer. If
|C′| |[Y,C]| were at most four, its derived subgroup would have order at
most eight. The symmetric-six small-section theorem would then make the
midpoint residual fix Y′. The incident radical already fixes Y′, so their
generation contradicts its noncentrality at the midpoint.

The terminal application therefore needs only this product bound, instead
of a cross-commutator inclusion into C′. The literal edge coordinates,
both central covers and all radical images are retained. Nonabelian
small-slice selection, the residual product upper bound, and the large-slice
branch remain source obligations; this is not DistanceFourInput.

Source: MS93 (3.10) and (5.12), printed pp.879--881 and 924--927.
The edge-coordinate argument follows SectionFive.ResidualTerminal;
the product estimate replaces its separate three order-two bounds.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include h in
private theorem residual_radical_sup : replacementComponent d ⊔ d.radical = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d g
  exact mul_mem (mem_sup_left hk) (mem_sup_right hr)

include h in
private theorem edge_coordinates {c t : Vertex d.radical}
    (hc : color d.radical c = false) (hct : Adjacent d.radical c t) :
    ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical c ∧ d.radical.map i = Q d.radical t ∧
      (pCore 2 d.overgroup).map i = Q d.radical c ∧
      (replacementComponent d).map i = Ltilde d.radical c := by
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_⟩
    · have he := stabilizer_act d.radical g (alpha d.radical)
      rw [alpha,stabilizer_m_base] at he
      simpa only [i,alpha,act_mVertex,one_mul,MonoidHom.range_comp,Mbar] using he.symm
    · have he := Q_act d.radical g (beta d.radical)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
    · have he := Q_act d.radical g (alpha d.radical)
      rw [Q_alpha d.radical (replacement_radical_isPGroup h d)
        (replacement_core_le_radical h d)] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have he := Ltilde_act d.radical g (alpha d.radical)
      rw [Ltilde_alpha,replacement_residual h d] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at hc
    cases hc

include e hz hn in
/-- A nonabelian small-slice path forces the product of the whole residual
derived order and its cross-commutator order with the selected kernel to
exceed four, for both covers and every radical image. -/
theorem small_slice_residual_product_gt_four_knownSimple
    (hb : replacementDistance h d = 4) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2) :
    let C := ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆
    let Y := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2)
    4 < Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam d.radical)) *
      Nat.card (⁅Y,C⁆ : Subgroup (FreeAmalgam d.radical)) := by
  dsimp only
  by_contra! hsmall
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan d.radical c (alpha d.radical)
  let Y := P ⊓ Q d.radical c
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hQa : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hQc : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hYN : Q d.radical t ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
    (le_inf (hQa.trans (localZSpan_normalized d.radical _ _))
      (hQc.trans (Q_normalized d.radical c))).trans inf_normalizer_le_normalizer_inf
  obtain ⟨i,hi,hir,hiR,hiQ,hiL⟩ := edge_coordinates (h := h) hcol hct
  let D := Y.comap i
  let C := ⁅pCore 2 d.overgroup,replacementComponent d⁆
  have hDm : D.map i = Y := map_comap_eq_self
    (inf_le_right.trans (hiQ ▸ map_le_range i _))
  have hCm : C.map i = ⁅Q d.radical c,Ltilde d.radical c⁆ := by
    rw [map_commutator,hiQ,hiL]
  have hDQ : D ≤ pCore 2 d.overgroup := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [hDm,hiQ]
    exact inf_le_right
  have hDN : d.radical ≤ normalizer (D : Set d.overgroup) :=
    ((map_le_iff_le_comap).mp (hiR ▸ hYN)).trans (le_normalizer_comap i)
  have hd := small_slice_kernel_configuration_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hnon hslice
  have hDcard : Nat.card (⁅D,D⁆ : Subgroup d.overgroup) = 2 := by
    rw [←card_map_of_injective hi,map_commutator,hDm]
    exact hd.2.1
  have hprod : Nat.card (⁅C,C⁆ : Subgroup d.overgroup) *
      Nat.card (⁅D,C⁆ : Subgroup d.overgroup) ≤ 4 := by
    have hCC : Nat.card (⁅C,C⁆ : Subgroup d.overgroup) =
        Nat.card (⁅⁅Q d.radical c,Ltilde d.radical c⁆,
          ⁅Q d.radical c,Ltilde d.radical c⁆⁆ :
          Subgroup (FreeAmalgam d.radical)) := by
      rw [←card_map_of_injective hi,map_commutator,hCm]
    have hDC : Nat.card (⁅D,C⁆ : Subgroup d.overgroup) =
        Nat.card (⁅Y,⁅Q d.radical c,Ltilde d.radical c⁆⁆ :
          Subgroup (FreeAmalgam d.radical)) := by
      rw [←card_map_of_injective hi,map_commutator,hDm,hCm]
    rw [hCC,hDC]
    exact hsmall
  have hfixed := derived_centralizes_residual_of_symmetricSix_product
    s.projection s.surjective (by rw [s.projection_kernel]; exact pCore_isPGroup)
    d.radical D (s.projection_kernel.trans_le (replacement_core_le_radical h d))
    (by rw [replacement_residual h d]; exact residual_radical_sup (h := h))
    (hDQ.trans_eq s.projection_kernel.symm) hDN (by
      rw [s.projection_kernel,replacement_residual h d,hDcard,mul_assoc]
      exact Nat.mul_le_mul_left 2 hprod)
  rw [replacement_residual h d] at hfixed
  have hf := (map_mono (f := i) hfixed).trans (map_centralizer_le_centralizer_image _ _)
  change (⁅D,D⁆ : Subgroup d.overgroup).map i ≤
    centralizer ((replacementComponent d).map i : Set (FreeAmalgam d.radical)) at hf
  rw [map_commutator,hDm,hiL] at hf
  have hgen : Ltilde d.radical c ⊔ Q d.radical t = stabilizer d.radical c := by
    rw [←hiL,←hiR,←Subgroup.map_sup,residual_radical_sup (h := h),←MonoidHom.range_eq_map,hir]
  apply hd.2.2.2.2.2.2
  apply le_centralizer_iff.mpr
  rw [←hgen]
  exact sup_le (le_centralizer_iff.mp hf)
    (hQa.trans (le_centralizer_iff.mp (hd.1 ▸ hd.2.2.2.1)))

include e hz hn in
/-- The literal small-slice terminal argument now only requires a product
bound on two whole residual-core orders. No cross-subgroup inclusion,
endpoint commutator or natural-quotient recognition is assumed. -/
theorem small_slice_terminal_false_of_residual_product_knownSimple
    (hb : replacementDistance h d = 4) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hproduct :
      let C := ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆
      let Y := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2)
      Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam d.radical)) *
        Nat.card (⁅Y,C⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 4) : False :=
  (Nat.not_lt_of_ge hproduct) (small_slice_residual_product_gt_four_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hnon hslice)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

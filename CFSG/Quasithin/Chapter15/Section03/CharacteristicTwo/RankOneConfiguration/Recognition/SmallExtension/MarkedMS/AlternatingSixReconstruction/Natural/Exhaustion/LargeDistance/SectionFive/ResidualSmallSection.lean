module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Graph
public import Theory.GroupTheory.PerfectFiveSectionSmallCore
public import Theory.GroupTheory.PerfectSimpleImageOrder
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Paths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport

/-!
# Small sections invariant under the actual replacement residual

A radius subgroup with section order at most eight over the full starting
seed lies in the Baumann slice if the component residual normalizes it.
Only that residual must preserve the subgroup. Its action factors through
a two-group section of order dividing eight, whose automorphism group has
order prime to five. Every nontrivial image of the original perfect
component retains its A6 central quotient, so this action is trivial.

The proof transports the original component through both subgroup-of
inclusions into each characteristic replacement, then through the literal
natural-graph embedding. Conjugation gives the statement at every component
vertex. No equality with an exceptional graph or quotient kernel is used.
SylowUnequalFixer applies it to the full reverse-kernel fixer span.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the residual-invariance step in (5.7), printed p.919. The elementary
small-action proof is adapted from Exceptional/OriginalSylow/CentralStrict,
with all component and graph maps reconstructed for the natural replacement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {d : Replacement L R}

include h e in
private theorem component_hom_eq_one_of_five_coprime
    {H : Type*} [Group H] [Finite H] (f : L →* H)
    (hf : Nat.Coprime 5 (Nat.card H)) : f = 1 := by
  let := h.component_perfect
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.core_quasisimple_of_centralCore
    (e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)))
  let q := QuotientGroup.mk' (pCore 2 L)
  let N := f.ker
  let : (N.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  apply MonoidHom.ker_eq_top_iff.mp
  rcases IsQuasisimple.normal_le_center_or_eq_top (N.map q) with hn | hn
  · have hN : N ≤ centralPreimage (pCore 2 L) := map_le_iff_le_comap.mp hn
    have hdiv := index_dvd_of_le hN
    have he := e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp))
    have hc : (centralPreimage (pCore 2 L)).index = 360 := by
      rw [index_eq_card,Nat.card_congr he.toEquiv]
      exact Theory.SpecificGroups.SymmetricSix.a6_order
    rw [hc] at hdiv
    have hncard : 5 ∣ Nat.card H := (show 5 ∣ 360 by decide).trans
      (hdiv.trans (by
        change f.ker.index ∣ Nat.card H
        rw [index_ker]
        exact f.range.card_subgroup_dvd_card))
    exact (Nat.prime_five.coprime_iff_not_dvd.mp hf hncard).elim
  · have hsup : N ⊔ pCore 2 L = ⊤ := by
      have he := congrArg (Subgroup.comap q) hn
      simpa only [q,comap_map_eq,QuotientGroup.ker_mk',comap_top] using he
    exact top_le_iff.mp (perfect_le_of_le_sup_two ⊤ N (pCore 2 L) pCore_isPGroup hsup.ge)

include e in
private theorem residual_small_radius_le_slice_base
    (hb : 2 < replacementDistance h d)
    (Y : Subgroup (FreeAmalgam d.radical))
    (hYV : Y ≤ V d.radical (alpha d.radical))
    (hYN : Ltilde d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hsmall : (Z d.radical (alpha d.radical)).relIndex Y ≤ 8) :
    Y ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
  let Y₀ := Y.comap (embedM d.radical)
  let Z₀ := (Z d.radical (alpha d.radical)).comap (embedM d.radical)
  let K := (L.subgroupOf (L ⊔ R)).subgroupOf d.overgroup
  have hYm : Y₀.map (embedM d.radical) = Y := map_comap_eq_self
    ((hYV.trans ((replacementGeometry h d).V_local _ rfl hb)).trans_eq (stabilizer_m_base d.radical))
  have hZm : Z₀.map (embedM d.radical) = Z d.radical (alpha d.radical) := map_comap_eq_self
    ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
  have hKm : K.map (embedM d.radical) = Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
  have hg (m : d.overgroup) : embedM d.radical m ∈ stabilizer d.radical (alpha d.radical) := by
    change embedM d.radical m ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : Z₀.Normal := ⟨by
    intro z hz m
    change embedM d.radical (m*z*m⁻¹) ∈ Z d.radical (alpha d.radical)
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp ((Z_normalized d.radical _) (hg m)) (embedM d.radical z)).mp hz⟩
  have hKN : K ≤ normalizer (Y₀ : Set d.overgroup) := by
    intro k hkK
    apply mem_normalizer_iff.mpr
    intro y
    change embedM d.radical y ∈ Y ↔ embedM d.radical (k*y*k⁻¹) ∈ Y
    rw [map_mul,map_mul,map_inv]
    exact mem_normalizer_iff.mp (hYN (hKm ▸ mem_map_of_mem _ hkK)) _
  let q := QuotientGroup.mk' Z₀
  let W := Y₀.map q
  have hKW : K.map q ≤ normalizer (W : Set (d.overgroup ⧸ Z₀)) :=
    (map_mono hKN).trans (le_normalizer_map q)
  let f : K →* MulAut W := W.normalizerMonoidHom.comp
    ((q.comp K.subtype).codRestrict (normalizer (W : Set (d.overgroup ⧸ Z₀)))
      (fun k => hKW (mem_map_of_mem q k.property)))
  have hYQ : Y₀ ≤ pCore 2 d.overgroup := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [hYm,←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    exact hYV.trans (V_le_Q d.radical rfl hb)
  have hc : Nat.card W ≤ 8 := by
    rw [←relIndex_ker Y₀ q]
    rw [show q.ker = Z₀ from QuotientGroup.ker_mk' Z₀]
    rw [←relIndex_map_map_of_injective _ _ (embedM_injective d.radical),hYm,hZm]
    exact hsmall
  have hdiv : Nat.card W ∣ 8 := by
    obtain ⟨n,hn⟩ := ((pCore_isPGroup (p := 2) (G := d.overgroup)).to_le hYQ |>.map q).exists_card_eq
    change Nat.card W = 2 ^ n at hn
    have hn3 : n ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by
      simpa only [hn] using hc)
    rw [hn]
    exact pow_dvd_pow 2 hn3
  let j : K ≃* L :=
    (subgroupOfEquivOfLe (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)).trans
      (subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left))
  have hf := component_hom_eq_one_of_five_coprime (h := h) (e := e) (f.comp j.symm.toMonoidHom)
    (five_coprime_card_mulAut_of_card_dvd_eight hdiv)
  have hf' : f = 1 := by
    apply MonoidHom.ext
    intro k
    obtain ⟨l,rfl⟩ := j.symm.surjective k
    exact DFunLike.congr_fun hf l
  have hcent : K.map q ≤ centralizer (W : Set (d.overgroup ⧸ Z₀)) := by
    rintro _ ⟨k,hkK,rfl⟩ w hw
    have he := congrArg (fun a : MulAut W => (a ⟨w,hw⟩ : d.overgroup ⧸ Z₀))
      (DFunLike.congr_fun hf' (⟨k,hkK⟩ : K))
    change q k * w * (q k)⁻¹ = w at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hcomm : ⁅Y₀,K⁆ ≤ Z₀ := by
    rw [←QuotientGroup.ker_mk' Z₀,←Subgroup.map_eq_bot_iff,map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcent)
  have hm := map_mono (f := embedM d.radical) hcomm
  rw [map_commutator,hYm,hKm,hZm,commutator_comm] at hm
  intro y hy
  exact (mem_B_iff d.radical (alpha d.radical) _ ((replacementGeometry h d).V_local _ rfl hb) y).mpr
    ⟨hYV hy,fun l hl => hm (commutator_mem_commutator hl hy)⟩

include e in
/-- Residual invariance alone places a radius section of order at most eight
in the actual Baumann slice, at every component vertex. -/
theorem residual_small_radius_le_slice_knownSimple
    (hb : 2 < replacementDistance h d)
    {a : Vertex d.radical} (ha : color d.radical a = false)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYV : Y ≤ V d.radical a)
    (hYN : Ltilde d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hindex : (Z d.radical a).relIndex Y ≤ 8) :
    Y ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  have hbase : act d.radical g⁻¹ (mVertex d.radical g) = alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  let j := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  have hh := residual_small_radius_le_slice_base (e := e) hb
  rw [←hbase] at hh
  have hm := hh (Y.map j)
    (by rw [V_act]; exact map_mono hYV)
    (by rw [Ltilde_act]; exact (map_mono hYN).trans (Y.le_normalizer_map j))
    (by rw [Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]; exact hindex)
  rw [Escape.PairingControl.FirstPairing.B_act hb g⁻¹ (mVertex d.radical g) ha] at hm
  exact (map_le_map_iff_of_injective (MulAut.conj (g⁻¹)⁻¹).injective).mp hm

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

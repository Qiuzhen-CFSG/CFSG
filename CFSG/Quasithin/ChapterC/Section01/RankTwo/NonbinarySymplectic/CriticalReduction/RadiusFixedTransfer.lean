module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.InnerAction
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NormalizationTransfer

/-!
# Full radius fixed-core transfer for the actual nonbinary replacement

The generic two-perfect generator argument applies to the actual finite
vertex stabilizer. Its quotient is the original-degree simple Sp group;
its full kernel is Q. Equal orders of the neighboring Q groups come from
literal graph conjugation. Thus fixed-core containment of [Vcirc,Y]
transfers to [V,Y] for every normal Y≤Q, with all central attachments.

The private import reuses only generic group arguments and native subgroup
transport, not the binary LocalSource or its SL3 action. This supplies the
moving-to-full-radius inference used in MS93 (5.12)(2), p.925. It does not
assert that either fixed-core containment holds without its premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionThree
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

private theorem residual_le_simple_closure {G D : Type*} [Group G] [Finite G]
    [Group D] [IsSimpleGroup D] (π : G →* D) (hπ : Function.Surjective π)
    (hp : IsPGroup 2 π.ker) (J : Subgroup G) (hJ : ¬ J ≤ π.ker) :
    pResidual 2 G ≤ normalClosure (J : Set G) := by
  let N := normalClosure (J : Set G)
  have hn : (N.map π).Normal := (inferInstance : N.Normal).map π hπ
  have hm : N.map π = ⊤ := by
    rcases hn.eq_bot_or_eq_top with h | h
    · exact (hJ ((le_normalClosure (H := J)).trans ((Subgroup.map_eq_bot_iff _).mp h))).elim
    · exact h
  have hsup : N ⊔ π.ker = ⊤ := by
    have hh := congrArg (fun A => A.comap π) hm
    simpa only [comap_map_eq,comap_top] using hh
  exact sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top N π.ker hp hsup⟩

omit h [Finite H] in
private theorem core_card_eq {a c : Vertex d.radical}
    (ha : color d.radical a=false) (hc : color d.radical c=false) :
    Nat.card (Q d.radical a) = Nat.card (Q d.radical c) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical ha
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical hc
  have hy : act d.radical (g⁻¹*j) a=c := by
    rw [hg,act_mVertex,mul_inv_cancel_left,←hj]
  rw [←hy,Q_act,card_map_of_injective (MulAut.conj (g⁻¹*j)⁻¹).injective]

include h
private theorem radius_generator_fixed_transfer
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    (a : Vertex d.radical) (ha : color d.radical a = false)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYQ : Y ≤ Q d.radical a)
    (hYn : (Y.subgroupOf (stabilizer d.radical a)).Normal)
    (htriple : ⁅Vcirc d.radical a,Y⁆ ≤ fixedCore d.radical a)
    (δ : Vertex d.radical) (hδ : color d.radical δ = false)
    (hd : (cosetGraph d.radical).dist δ a ≤ 2) : ⁅Z d.radical δ,Y⁆ ≤ fixedCore d.radical a := by
  let S := stabilizer d.radical a
  have hQa : Q d.radical a ≤ S := fun _ hx => hx.1
  have hQδ : Q d.radical δ ≤ S := Q_le_stabilizer_of_dist_le_two δ a hδ ha hd
  have hQad : Q d.radical a ≤ stabilizer d.radical δ :=
    Q_le_stabilizer_of_dist_le_two a δ ha hδ (by rwa [SimpleGraph.dist_comm])
  have hAV : Z d.radical δ ≤ V d.radical a := le_iSup_of_le δ (le_iSup_of_le hd le_rfl)
  have hVQ := geometry.V_le_Q (by omega) a ha
  have hAS := hAV.trans (hVQ.trans hQa)
  let : Finite S := finite_stabilizer d.radical a
  let : Finite (Q d.radical a) := Finite.of_injective (inclusion hQa) (inclusion_injective hQa)
  by_cases hle : Q d.radical δ ≤ Q d.radical a
  · have he : Q d.radical δ = Q d.radical a := eq_of_le_of_card_ge hle (by
      exact (core_card_eq d ha hδ).le)
    have hc : ⁅Z d.radical δ,Y⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono le_rfl (hYQ.trans he.ge)).trans (Z_centralizes_Q d.radical δ hδ).le)
    rw [hc]
    exact bot_le
  · obtain ⟨E,hE,π,hπ,hkerMap,_⟩ := h.replacement_inner_natural_action d geometry hb ha
    have hlarge : 3 < Nat.card E.Carrier := by
      rw [E.card_eq,hE]
      exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
    let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
    let : IsSimpleGroup (Theory.SpecificGroups.SymplecticFour.Sp E.Carrier) :=
      Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
    have hker : π.ker = (Q d.radical a).subgroupOf S := by
      apply map_injective S.subtype_injective
      rw [hkerMap,map_subgroupOf_eq_of_le hQa]
    let Q₀ := (Q d.radical a).subgroupOf S
    let V₀ := (V d.radical a).subgroupOf S
    let Y₀ := Y.subgroupOf S
    let A₀ := (Z d.radical δ).subgroupOf S
    let J₀ := (Q d.radical δ).subgroupOf S
    let L₀ := pResidual 2 S
    let : Q₀.Normal := Q_normal d.radical a
    let : Y₀.Normal := hYn
    have hpQ : IsPGroup 2 Q₀ :=
      (Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) a ha).of_equiv
        (subgroupOfEquivOfLe hQa).symm
    have hcover : Q₀ ⊔ L₀ = ⊤ := by
      change (Q d.radical a).subgroupOf (stabilizer d.radical a) ⊔ pResidual 2 (stabilizer d.radical a) = ⊤
      apply map_injective S.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hQa]
      change Q d.radical a ⊔ Ltilde d.radical a = (⊤ : Subgroup S).map S.subtype
      rw [←MonoidHom.range_eq_map,range_subtype,sup_comm]
      obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ :=
        CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison.vertex_coordinates_with_kernel
          d.radical (h.replacement_two_group d) (h.replacement_core_le d) ha
      rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
        h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]
    have hnot : ¬ J₀ ≤ π.ker := by
      intro h
      apply hle
      rw [hker] at h
      change (Q d.radical δ).subgroupOf S ≤ (Q d.radical a).subgroupOf S at h
      have hh := map_mono (f := S.subtype) h
      simpa only [map_subgroupOf_eq_of_le hQδ, map_subgroupOf_eq_of_le hQa] using hh
    have hclosure : L₀ ≤ normalClosure (J₀ : Set S) :=
      residual_le_simple_closure π hπ (hker.symm ▸ hpQ) J₀ hnot
    have hL : (Ltilde d.radical a).subgroupOf S = L₀ := by
      exact comap_map_eq_self_of_injective S.subtype_injective _
    have hQA : Q₀ ≤ normalizer A₀ :=
      (comap_mono (hQad.trans (Z_normalized d.radical δ))).trans
        (le_normalizer_comap S.subtype)
    have htriple₀ : ⁅⁅V₀,L₀⁆,Y₀⁆ ≤ Q₀ ⊓ centralizer (L₀ : Set S) := by
      rw [← fixedCore_native a]
      have hh := comap_mono (f := S.subtype) htriple
      change (⁅Vcirc d.radical a,Y⁆).subgroupOf S ≤ (fixedCore d.radical a).subgroupOf S at hh
      rw [← commutator_native S (Vcirc d.radical a) Y
        ((Subgroup.commutator_le_sup _ _).trans
          (sup_le (hVQ.trans hQa) (Ltilde_le_stabilizer a)))
        (hYQ.trans hQa), Vcirc,
        ← commutator_native S (V d.radical a) (Ltilde d.radical a) (hVQ.trans hQa)
          (Ltilde_le_stabilizer a), hL] at hh
      exact hh
    have hAJ : ⁅A₀,J₀⁆ = ⊥ := by
      rw [commutator_native S (Z d.radical δ) (Q d.radical δ) hAS hQδ, Z_centralizes_Q d.radical δ hδ]
      exact S.subtype.ker_eq_bot S.subtype_injective
    have hbound := generator_transfer Q₀ L₀ V₀ Y₀ A₀ J₀ hpQ
      (isPPerfect_pResidual 2) hcover (comap_mono hVQ) (comap_mono hYQ)
      (comap_mono hAV) hQA htriple₀ hAJ hclosure
    rw [← fixedCore_native a, commutator_native S (Z d.radical δ) Y hAS (hYQ.trans hQa)] at hbound
    change (⁅Z d.radical δ,Y⁆).subgroupOf S ≤ (fixedCore d.radical a).subgroupOf S at hbound
    have hh := map_mono (f := S.subtype) hbound
    simpa only [map_subgroupOf_eq_of_le
      ((Subgroup.commutator_le_sup _ _).trans (sup_le hAS (hYQ.trans hQa))),
      map_subgroupOf_eq_of_le (show fixedCore d.radical a ≤ S from inf_le_left.trans hQa)] using hh

/-- Fixed-core containment on the moved radius transfers to the whole
radius for an actual normal subgroup of its vertex kernel. -/
theorem Input.replacement_radius_fixed_transfer
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    (a : Vertex d.radical) (ha : color d.radical a=false)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYQ : Y ≤ Q d.radical a)
    (hYn : (Y.subgroupOf (stabilizer d.radical a)).Normal)
    (hc : ⁅Vcirc d.radical a,Y⁆ ≤ fixedCore d.radical a) :
    ⁅V d.radical a,Y⁆ ≤ fixedCore d.radical a := by
  have hVnorm : V d.radical a ≤ normalizer (fixedCore d.radical a) :=
    (geometry.V_le_Q (by omega) a ha).trans
      ((show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1).trans
        (SectionThree.fixedCore_normalized d.radical a))
  apply SectionThree.commutator_iSup_le_of_normalizes _ _ _ hVnorm
  intro δ
  apply SectionThree.commutator_iSup_le_of_normalizes
  · apply iSup_le
    intro hd
    exact (le_iSup_of_le δ (le_iSup_of_le hd le_rfl) : Z d.radical δ ≤ V d.radical a).trans hVnorm
  · intro hd
    by_cases hδ : color d.radical δ = false
    · exact radius_generator_fixed_transfer h d geometry hb a ha Y hYQ hYn hc δ hδ hd
    · have hδ' : color d.radical δ = true := by cases hh : color d.radical δ <;> simp_all
      obtain ⟨p,hp⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist δ a
      have hnEven : ¬ Even p.length := by
        rw [walk_even_iff_color_eq, hδ', ha]
        decide
      have hlen : p.length = 1 := by
        have hle : p.length ≤ 2 := hp.trans_le hd
        rw [Nat.even_iff] at hnEven
        omega
      have hadj : Adjacent d.radical a δ :=
        adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp (p.adj_of_length_eq_one hlen))
      have hδZ : Z d.radical δ ≤ Z d.radical a := by
        rw [Z, if_neg hδ, Z, if_pos ha]
        exact le_iSup_of_le δ (le_iSup_of_le hadj le_rfl)
      exact (commutator_mono hδZ hYQ).trans ((Z_centralizes_Q d.radical a ha).le.trans bot_le)


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

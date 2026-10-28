module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates.Centralizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates.CriticalCommutator
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# The actual derived critical endpoint images

The natural quotient gives a lower bound for displacement on the whole
central omega layer X. Every nontrivial elementary subgroup of A₆ has
rank at most its natural fixed codimension, since its unique offender
has equality. Comparing the two ends of an actual critical pair therefore
makes their displacement indices equal. The opposite X-image is consequently
the even four-group and is self-centralizing in A₆.

The proof retains the literal replacement map and both possible central
moved covers. It does not identify X with that cover or choose a complement.
Source: MS93 (2.2)(vi) and the first paragraph of (3.8), pp.857,877.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

local notation "π" => projection h e hz hn d
local notation "ρ" => BinaryPermutation.naturalRepresentation (Fin 6)
local notation "X₀" => omegaCenterIn (pCore 2 d.overgroup)

private theorem even_rank_le_codim (A : Subgroup (Equiv.Perm (Fin 6)))
    (ha : A ≤ alternatingGroup (Fin 6)) (he : IsElementaryTwo A) :
    rank A ≤ fixedCodim ρ A := by
  by_contra hh
  have ho : IsOffender ρ A := ⟨he, (lt_of_not_ge hh).le⟩
  have hc := ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_card ha ho
  have hd := ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_codim ha ho
  have hr : rank A = 2 := by change Nat.log 2 (Nat.card A) = 2; rw [hc]; decide
  exact hh (hr.trans hd.symm).le

private theorem natural_index_le_X_index (E : Subgroup d.overgroup) :
    2 ^ fixedCodim ρ (E.map π) ≤ (centralizer (E : Set d.overgroup)).relIndex X₀ := by
  let := replacementMoved_normal h d
  let q := (π).rangeRestrict
  let σ := (ρ).comp (π).range.subtype
  have hq : fixedCodim σ (E.map q) = fixedCodim ρ (E.map π) := by
    unfold fixedCodim σ
    rw [fixedSpace_comp_map, map_map]
    rfl
  have hle := fixedCodim_le_of_equivariant_surjection (Cover.action h e hz hn d) σ
    (SectionFive.coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
    (SectionFive.coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
    (Cover.map_equivariant h e hz hn d) (E.map q)
  rw [hq] at hle
  have hi : (centralizer (E : Set d.overgroup)).relIndex (replacementMoved d) =
      2 ^ fixedCodim (Cover.action h e hz hn d) (E.map q) :=
    NormalElementaryQuotient.centralizer_index_eq_fixedCodim _ _ _ _ E
  apply (Nat.pow_le_pow_right (by decide : 0 < 2) hle).trans
  rw [← hi]
  exact relIndex_le_of_le_right (replacementMoved_le_omegaCenter h d)
    (Subgroup.index_ne_zero_of_finite)

/-- The literal six-letter image of a subgroup in the base stabilizer. -/
def criticalImage (E : Subgroup (FreeAmalgam d.radical)) : Subgroup (Equiv.Perm (Fin 6)) :=
  (E.comap (embedM d.radical)).map π

include h in
private theorem X_alpha_map :
    X d.radical (alpha d.radical) = (X₀).map (embedM d.radical) := by
  rw [X, Q_alpha d.radical (replacement_radical_isPGroup h d)
    (replacement_core_le_radical h d), omegaCenter_map _ _ (embedM_injective _)]
  rfl

private theorem criticalImage_card (E : Subgroup (FreeAmalgam d.radical))
    (hE : E ≤ stabilizer d.radical (alpha d.radical)) :
    Nat.card (criticalImage h e hz hn d E) = (Q d.radical (alpha d.radical)).relIndex E := by
  rw [criticalImage, ← relIndex_ker, projection_kernel]
  have hm : (E.comap (embedM d.radical)).map (embedM d.radical) = E :=
    map_comap_eq_self (hE.trans_eq (stabilizer_m_base d.radical))
  rw [← relIndex_map_map_of_injective _ _ (embedM_injective d.radical), hm,
    ← Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]

private theorem criticalImage_elementary (E : Subgroup (FreeAmalgam d.radical))
    (hE : E ≤ stabilizer d.radical (alpha d.radical))
    (hne : ¬ E ≤ Q d.radical (alpha d.radical)) [IsElementaryAbelian 2 E] :
    IsElementaryTwo (criticalImage h e hz hn d E) := by
  let A := E.comap (embedM d.radical)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    ((embedM d.radical).subgroupComap E) (by
      intro x y hh
      apply Subtype.ext
      exact embedM_injective d.radical (congrArg Subtype.val hh))
  refine ⟨?_, IsElementaryAbelian.map π⟩
  intro he
  have hk := (Subgroup.map_eq_bot_iff A).mp he
  rw [projection_kernel] at hk
  have hm := map_mono (f := embedM d.radical) hk
  rw [map_comap_eq_self (hE.trans_eq (stabilizer_m_base d.radical)),
    ← Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at hm
  exact hne hm

private theorem natural_index_le_displacement (E : Subgroup (FreeAmalgam d.radical))
    (hE : E ≤ stabilizer d.radical (alpha d.radical)) :
    2 ^ fixedCodim ρ (criticalImage h e hz hn d E) ≤
      Offenders.displacement (X d.radical (alpha d.radical)) E := by
  have hm : (E.comap (embedM d.radical)).map (embedM d.radical) = E :=
    map_comap_eq_self (hE.trans_eq (stabilizer_m_base d.radical))
  have hc : (centralizer (E : Set (FreeAmalgam d.radical))).comap (embedM d.radical) =
      centralizer (E.comap (embedM d.radical) : Set d.overgroup) := by
    ext x
    constructor
    · intro hx y hy
      apply embedM_injective d.radical
      simpa only [map_mul] using hx _ hy
    · intro hx y hy
      rw [← hm] at hy
      obtain ⟨z,hz,rfl⟩ := hy
      simpa only [map_mul] using congrArg (embedM d.radical) (hx z hz)
  have hi := natural_index_le_X_index h e hz hn d (E.comap (embedM d.radical))
  rw [← hc, relIndex_comap, ← X_alpha_map h d] at hi
  exact hi

private theorem image_card_le_displacement
    (himage : (π).range = alternatingGroup (Fin 6))
    (E : Subgroup (FreeAmalgam d.radical))
    (hE : E ≤ stabilizer d.radical (alpha d.radical))
    (hne : ¬ E ≤ Q d.radical (alpha d.radical)) [IsElementaryAbelian 2 E] :
    (Q d.radical (alpha d.radical)).relIndex E ≤
      Offenders.displacement (X d.radical (alpha d.radical)) E := by
  have he := criticalImage_elementary h e hz hn d E hE hne
  have ha : criticalImage h e hz hn d E ≤ alternatingGroup (Fin 6) := by
    rw [← himage]
    exact map_le_range _ _
  rw [← criticalImage_card h e hz hn d E hE, he.card_eq_two_pow_rank]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) (even_rank_le_codim _ ha he)).trans
    (natural_index_le_displacement h e hz hn d E hE)


private theorem critical_reverse_pair
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha)) :
    CriticalPair d.radical b a ((replacementGeometry h d).exists_critical b
      (critical_endpoint_color d.radical a ha _ hc)) := by
  apply critical_reverse d.radical (replacementGeometry h d)
    (edgeCentralizerCondition h e hz hn d himage) a ha _ b (critical_endpoint_color d.radical a ha _ hc) hc
  rw [(replacementGeometry h d).distance_constant a ha]
  exact replacementDistance_pos h d

/-- The opposite X-layer lies in the first edge, and its index is the
literal displacement by the initial X-layer. -/
theorem critical_edge_data
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha))
    (t : Vertex d.radical) (hat : Adjacent d.radical a t)
    (ht : (cosetGraph d.radical).dist t b + 1 = (cosetGraph d.radical).dist a b) :
    X d.radical b ≤ Q d.radical t ∧ ¬ X d.radical b ≤ Q d.radical a ∧
      Offenders.displacement (X d.radical b) (X d.radical a) =
        (Q d.radical a).relIndex (X d.radical b) := by
  have hbcol := critical_endpoint_color d.radical a ha _ hc
  have htcol : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hNT : Q d.radical a ≤ Q d.radical t := Q_le_adjacent_h d.radical htcol hat
  have hsmall : (cosetGraph d.radical).dist b t <
      criticalDistance d.radical b ((replacementGeometry h d).exists_critical b hbcol) := by
    rw [SimpleGraph.dist_comm, (replacementGeometry h d).distance_constant b hbcol,
      ← (replacementGeometry h d).distance_constant a ha]
    have hd := hc.1
    omega
  have hE : X d.radical b ≤ Q d.radical t :=
    X_le_Q_of_dist_lt d.radical (replacementGeometry h d)
      (edgeCentralizerCondition h e hz hn d himage) b hbcol t hsmall
  have hCY : Q d.radical t ⊓ centralizer (X d.radical a : Set (FreeAmalgam d.radical)) =
      Q d.radical a := by
    apply le_antisymm
    · calc
        _ ≤ Q d.radical t ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
          inf_le_inf_left _ (centralizer_le ((replacementGeometry h d).omega_bound a ha (by
            rw [(replacementGeometry h d).distance_constant a ha]
            exact replacementDistance_pos h d)))
        _ = _ := edgeCentralizerCondition h e hz hn d himage a t ha hat
    · exact le_inf hNT (Q_le_centralizer_X d.radical a)
  have hZ : Z d.radical b ≤ X d.radical b :=
    (replacementGeometry h d).omega_bound b hbcol (by
      rw [(replacementGeometry h d).distance_constant b hbcol]
      exact replacementDistance_pos h d)
  refine ⟨hE, fun hh => (critical_reverse_pair h e hz hn d himage a ha b hc).2
    (hZ.trans hh), ?_⟩
  have he : X d.radical b ⊓ centralizer (X d.radical a : Set (FreeAmalgam d.radical)) =
      X d.radical b ⊓ Q d.radical a := by
    rw [← hCY, ← inf_assoc, inf_of_le_left hE]
  unfold Offenders.displacement
  rw [← inf_relIndex_left (X d.radical b), he, inf_relIndex_left]

private theorem critical_displacement_le
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha)) :
    Offenders.displacement (X d.radical b) (X d.radical a) ≤
      Offenders.displacement (X d.radical a) (X d.radical b) := by
  obtain ⟨t, hat, ht⟩ := exists_adjacent_dist_sub_one d.radical a b (by
    rw [hc.1, (replacementGeometry h d).distance_constant a ha]
    exact replacementDistance_pos h d)
  obtain ⟨g, hg⟩ := exists_mVertex_of_color d.radical ha
  let f := g⁻¹
  have hf : act d.radical f a = alpha d.radical := by
    rw [hg]
    simp only [f, act_mVertex, mul_inv_cancel]
    rfl
  have hfcol : color d.radical (act d.radical f a) = false := by rw [hf]; rfl
  have hc' := (criticalPair_act_iff d.radical f a b ((replacementGeometry h d).exists_critical a ha)
    ((replacementGeometry h d).exists_critical (act d.radical f a) hfcol)).mpr hc
  have hat' := (adjacent_act_iff d.radical f a t).mpr hat
  have ht' : (cosetGraph d.radical).dist (act d.radical f t) (act d.radical f b) + 1 =
      (cosetGraph d.radical).dist (act d.radical f a) (act d.radical f b) := by
    simpa only [dist_act] using ht
  have hcmp : Offenders.displacement (X d.radical (act d.radical f b))
      (X d.radical (act d.radical f a)) ≤
      Offenders.displacement (X d.radical (act d.radical f a)) (X d.radical (act d.radical f b)) := by
    simp only [hf] at hc' hat' ht' ⊢
    obtain ⟨hE, hne, hi⟩ := critical_edge_data h e hz hn d himage (alpha d.radical) rfl
      (act d.radical f b) hc' (act d.radical f t) hat' ht'
    rw [hi]
    let := X_elementary d.radical (act d.radical f b)
    exact image_card_le_displacement h e hz hn d himage _
      (hE.trans (CriticalCriterion.edge_le_stabilizer d.radical rfl hat')) hne
  simpa only [X_act, Offenders.displacement_map] using hcmp

/-- Neither endpoint can be a strict offender; reversing the critical pair
gives equality of the actual displacement indices. -/
theorem critical_displacement_eq
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha)) :
    Offenders.displacement (X d.radical a) (X d.radical b) =
      Offenders.displacement (X d.radical b) (X d.radical a) := by
  have hbcol := critical_endpoint_color d.radical a ha _ hc
  exact le_antisymm
    (critical_displacement_le h e hz hn d himage b hbcol a
      (critical_reverse_pair h e hz hn d himage a ha b hc))
    (critical_displacement_le h e hz hn d himage a ha b hc)

/-- The actual far endpoint acts as an offender on the natural quotient. -/
theorem critical_image_offender
    (himage : (π).range = alternatingGroup (Fin 6)) (b : Vertex d.radical)
    (hc : CriticalPair d.radical (alpha d.radical) b
      ((replacementGeometry h d).exists_critical (alpha d.radical) rfl))
    (t : Vertex d.radical) (hat : Adjacent d.radical (alpha d.radical) t)
    (ht : (cosetGraph d.radical).dist t b + 1 = (cosetGraph d.radical).dist (alpha d.radical) b) :
    IsOffender ρ (criticalImage h e hz hn d (X d.radical b)) := by
  let := X_elementary d.radical b
  obtain ⟨hE,hne,hi⟩ := critical_edge_data h e hz hn d himage (alpha d.radical) rfl b hc t hat ht
  have hES := hE.trans (CriticalCriterion.edge_le_stabilizer d.radical rfl hat)
  have he := criticalImage_elementary h e hz hn d (X d.radical b) hES hne
  refine ⟨he, ?_⟩
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [← he.card_eq_two_pow_rank, criticalImage_card h e hz hn d _ hES, ← hi,
    ← critical_displacement_eq h e hz hn d himage (alpha d.radical) rfl b hc]
  exact natural_index_le_displacement h e hz hn d _ hES

/-- The literal critical image is the even four-group, with its exact order
and self-centralizer. This is the source-(3.8) endpoint calculation. -/
theorem critical_image_structure
    (himage : (π).range = alternatingGroup (Fin 6)) (b : Vertex d.radical)
    (hc : CriticalPair d.radical (alpha d.radical) b
      ((replacementGeometry h d).exists_critical (alpha d.radical) rfl))
    (t : Vertex d.radical) (hat : Adjacent d.radical (alpha d.radical) t)
    (ht : (cosetGraph d.radical).dist t b + 1 = (cosetGraph d.radical).dist (alpha d.radical) b) :
    Nat.card (criticalImage h e hz hn d (X d.radical b)) = 4 ∧
      alternatingGroup (Fin 6) ⊓ centralizer
        (criticalImage h e hz hn d (X d.radical b) : Set (Equiv.Perm (Fin 6))) =
          criticalImage h e hz hn d (X d.radical b) := by
  have he : criticalImage h e hz hn d (X d.radical b) ≤ alternatingGroup (Fin 6) := by
    rw [← himage]; exact map_le_range _ _
  have ho := critical_image_offender h e hz hn d himage b hc t hat ht
  exact ⟨ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_card he ho,
    conjugate_evenPart_centralizer
      ((ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_iff _ he).mp ho)⟩


private theorem criticalImage_preimage (E : Subgroup (FreeAmalgam d.radical))
    (hE : E ≤ stabilizer d.radical (alpha d.radical)) :
    ((criticalImage h e hz hn d E).comap π).map (embedM d.radical) =
      E ⊔ Q d.radical (alpha d.radical) := by
  rw [criticalImage, comap_map_eq, Subgroup.map_sup, projection_kernel,
    map_comap_eq_self (hE.trans_eq (stabilizer_m_base d.radical)),
    ← Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]

private theorem edge_image_two_group (t : Vertex d.radical)
    (hat : Adjacent d.radical (alpha d.radical) t) :
    IsPGroup 2 (criticalImage h e hz hn d (Q d.radical t)) := by
  have hT : IsPGroup 2 (Q d.radical t) := by
    obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common d.radical (alpha d.radical) t).mp hat
    · have ht := hg.2
      rw [ht]
      have hh := Q_act d.radical g (beta d.radical)
      simp only [beta,act_hVertex,one_mul] at hh
      rw [hh]
      change IsPGroup 2 ((Q d.radical (beta d.radical)).map _)
      rw [Q_beta]
      exact ((replacement_radical_isPGroup h d).map (embedM d.radical)).map _
    · have hh := hg.1
      have hcol := congrArg (color d.radical) hh
      cases hcol
  exact (hT.of_injective ((embedM d.radical).subgroupComap (Q d.radical t))
    (fun _ _ he => Subtype.ext (embedM_injective d.radical (congrArg Subtype.val he)))).map π

private theorem critical_normalized_alpha
    (himage : (π).range = alternatingGroup (Fin 6)) (b : Vertex d.radical)
    (hc : CriticalPair d.radical (alpha d.radical) b
      ((replacementGeometry h d).exists_critical (alpha d.radical) rfl))
    (t : Vertex d.radical) (hat : Adjacent d.radical (alpha d.radical) t)
    (ht : (cosetGraph d.radical).dist t b + 1 = (cosetGraph d.radical).dist (alpha d.radical) b) :
    Q d.radical t ≤ normalizer ((X d.radical b ⊔ Q d.radical (alpha d.radical) :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let A := criticalImage h e hz hn d (X d.radical b)
  let T := criticalImage h e hz hn d (Q d.radical t)
  have hXS := (critical_edge_data h e hz hn d himage _ rfl b hc t hat ht).1
  have hT := CriticalCriterion.edge_le_stabilizer d.radical rfl hat
  have hAT : A ≤ T := map_mono (comap_mono hXS)
  have ho := critical_image_offender h e hz hn d himage b hc t hat ht
  have hnT : T ≤ normalizer (A : Set (Equiv.Perm (Fin 6))) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    apply ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_unique
      (edge_image_two_group h e hz hn d t hat)
      (show T ≤ alternatingGroup (Fin 6) by rw [← himage]; exact map_le_range _ _)
      ((map_mono hAT).trans_eq (mem_normalizer_iff_map_conj_eq.mp (T.le_normalizer hg))) hAT
    · refine ⟨ho.1.map_conj g, ?_⟩
      change fixedCodim ρ (A.map (MulAut.conj g).toMonoidHom) ≤
        rank (A.map (MulAut.conj g).toMonoidHom)
      rw [fixedCodim_map_conj, rank_map_conj]
      exact ho.2
    · exact ho
  have hnorm : (Q d.radical t).comap (embedM d.radical) ≤
      normalizer (A.comap π : Set d.overgroup) :=
    ((map_le_iff_le_comap).mp hnT).trans (le_normalizer_comap _)
  have hh := (map_mono (f := embedM d.radical) hnorm).trans (le_normalizer_map (embedM d.radical))
  rw [map_comap_eq_self (hT.trans_eq (stabilizer_m_base d.radical)),
    criticalImage_preimage h e hz hn d _ (hXS.trans hT)] at hh
  exact hh

private theorem critical_common_alpha
    (himage : (π).range = alternatingGroup (Fin 6)) (b : Vertex d.radical)
    (hc : CriticalPair d.radical (alpha d.radical) b
      ((replacementGeometry h d).exists_critical (alpha d.radical) rfl))
    (t : Vertex d.radical) (hat : Adjacent d.radical (alpha d.radical) t)
    (ht : (cosetGraph d.radical).dist t b + 1 = (cosetGraph d.radical).dist (alpha d.radical) b)
    (c : Vertex d.radical)
    (hcc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical (alpha d.radical) rfl))
    (htc : (cosetGraph d.radical).dist t c + 1 = (cosetGraph d.radical).dist (alpha d.radical) c) :
    X d.radical b ⊔ Q d.radical (alpha d.radical) =
      X d.radical c ⊔ Q d.radical (alpha d.radical) := by
  have hE := (critical_edge_data h e hz hn d himage _ rfl b hc t hat ht).1
  have hF := (critical_edge_data h e hz hn d himage _ rfl c hcc t hat htc).1
  have hT := CriticalCriterion.edge_le_stabilizer d.radical rfl hat
  have he : criticalImage h e hz hn d (X d.radical b) =
      criticalImage h e hz hn d (X d.radical c) :=
    ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_unique
      (edge_image_two_group h e hz hn d t hat)
      (show criticalImage h e hz hn d (Q d.radical t) ≤ alternatingGroup (Fin 6) by
        rw [← himage]; exact map_le_range _ _)
      (map_mono (comap_mono hE)) (map_mono (comap_mono hF))
      (critical_image_offender h e hz hn d himage b hc t hat ht)
      (critical_image_offender h e hz hn d himage c hcc t hat htc)
  have hh := congrArg (fun A : Subgroup (Equiv.Perm (Fin 6)) =>
    (A.comap π).map (embedM d.radical)) he
  simpa only [criticalImage_preimage h e hz hn d _ (hE.trans hT),
    criticalImage_preimage h e hz hn d _ (hF.trans hT)] using hh

private theorem critical_centralizer_alpha
    (himage : (π).range = alternatingGroup (Fin 6)) (b : Vertex d.radical)
    (hc : CriticalPair d.radical (alpha d.radical) b
      ((replacementGeometry h d).exists_critical (alpha d.radical) rfl)) :
    stabilizer d.radical (alpha d.radical) ⊓
        centralizer (X d.radical b : Set (FreeAmalgam d.radical)) ≤
      X d.radical b ⊔ Q d.radical (alpha d.radical) := by
  obtain ⟨t,hat,ht⟩ := exists_adjacent_dist_sub_one d.radical (alpha d.radical) b (by
    rw [hc.1,(replacementGeometry h d).distance_constant (alpha d.radical) rfl]
    exact replacementDistance_pos h d)
  have hE := (critical_edge_data h e hz hn d himage _ rfl b hc t hat ht).1
  have hES := hE.trans (CriticalCriterion.edge_le_stabilizer d.radical rfl hat)
  have hcen := (critical_image_structure h e hz hn d himage b hc t hat ht).2
  rintro x ⟨hxS,hxC⟩
  obtain ⟨y,rfl⟩ := (stabilizer_m_base d.radical ▸ hxS)
  have hy : π y ∈ criticalImage h e hz hn d (X d.radical b) := by
    rw [← hcen]
    refine ⟨himage ▸ ⟨y,rfl⟩, ?_⟩
    rintro a ⟨z,hz,rfl⟩
    have he : z*y = y*z := embedM_injective d.radical (by
      simpa only [map_mul] using hxC (embedM d.radical z) hz)
    simpa only [map_mul] using congrArg π he
  rw [← criticalImage_preimage h e hz hn d _ hES]
  exact mem_map_of_mem (embedM d.radical) hy

omit [Finite G] in
private theorem exists_to_alpha (a : Vertex d.radical) (ha : color d.radical a = false) :
    ∃ f : FreeAmalgam d.radical, act d.radical f a = alpha d.radical := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  exact ⟨g⁻¹, by simp only [act_mVertex,mul_inv_cancel]; rfl⟩

private theorem critical_to_alpha (a : Vertex d.radical) (ha : color d.radical a = false)
    (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha))
    (f : FreeAmalgam d.radical) (hf : act d.radical f a = alpha d.radical) :
    CriticalPair d.radical (alpha d.radical) (act d.radical f b)
      ((replacementGeometry h d).exists_critical (alpha d.radical) rfl) := by
  have hfcol : color d.radical (act d.radical f a) = false := by rw [hf]; rfl
  simpa only [hf] using (criticalPair_act_iff d.radical f a b
    ((replacementGeometry h d).exists_critical a ha)
    ((replacementGeometry h d).exists_critical (act d.radical f a) hfcol)).mpr hc

/-- Offender uniqueness normalizes the actual endpoint image modulo Q. -/
theorem critical_join_normalized
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha))
    (t : Vertex d.radical) (hat : Adjacent d.radical a t)
    (ht : (cosetGraph d.radical).dist t b + 1 = (cosetGraph d.radical).dist a b) :
    Q d.radical t ≤ normalizer ((X d.radical b ⊔ Q d.radical a :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  obtain ⟨f,hf⟩ := exists_to_alpha d a ha
  have hc' := critical_to_alpha h d a ha b hc f hf
  have hat' : Adjacent d.radical (alpha d.radical) (act d.radical f t) := by
    simpa only [hf] using (adjacent_act_iff d.radical f a t).mpr hat
  have ht' : (cosetGraph d.radical).dist (act d.radical f t) (act d.radical f b) + 1 =
      (cosetGraph d.radical).dist (alpha d.radical) (act d.radical f b) := by
    rw [← hf,dist_act,dist_act]; exact ht
  have hn : Q d.radical (act d.radical f t) ≤ normalizer
      ((X d.radical (act d.radical f b) ⊔ Q d.radical (act d.radical f a) :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    simpa only [hf] using critical_normalized_alpha h e hz hn d himage
      (act d.radical f b) hc' (act d.radical f t) hat' ht'
  rw [Q_act,X_act,Q_act,← Subgroup.map_sup,← Subgroup.map_equiv_normalizer_eq] at hn
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj f⁻¹).injective).mp hn

/-- Every critical endpoint through the same edge has the same quotient image. -/
theorem critical_join_common
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha))
    (t : Vertex d.radical) (hat : Adjacent d.radical a t)
    (ht : (cosetGraph d.radical).dist t b + 1 = (cosetGraph d.radical).dist a b)
    (c : Vertex d.radical)
    (hcc : CriticalPair d.radical a c ((replacementGeometry h d).exists_critical a ha))
    (htc : (cosetGraph d.radical).dist t c + 1 = (cosetGraph d.radical).dist a c) :
    X d.radical b ⊔ Q d.radical a = X d.radical c ⊔ Q d.radical a := by
  obtain ⟨f,hf⟩ := exists_to_alpha d a ha
  have hc' := critical_to_alpha h d a ha b hc f hf
  have hcc' := critical_to_alpha h d a ha c hcc f hf
  have hat' : Adjacent d.radical (alpha d.radical) (act d.radical f t) := by
    simpa only [hf] using (adjacent_act_iff d.radical f a t).mpr hat
  have ht' : (cosetGraph d.radical).dist (act d.radical f t) (act d.radical f b) + 1 =
      (cosetGraph d.radical).dist (alpha d.radical) (act d.radical f b) := by
    rw [← hf,dist_act,dist_act]; exact ht
  have htc' : (cosetGraph d.radical).dist (act d.radical f t) (act d.radical f c) + 1 =
      (cosetGraph d.radical).dist (alpha d.radical) (act d.radical f c) := by
    rw [← hf,dist_act,dist_act]; exact htc
  have he : X d.radical (act d.radical f b) ⊔ Q d.radical (act d.radical f a) =
      X d.radical (act d.radical f c) ⊔ Q d.radical (act d.radical f a) := by
    simpa only [hf] using critical_common_alpha h e hz hn d himage
      (act d.radical f b) hc' (act d.radical f t) hat' ht' (act d.radical f c) hcc' htc'
  rw [X_act,Q_act,X_act,← Subgroup.map_sup,← Subgroup.map_sup] at he
  exact Subgroup.map_injective (MulAut.conj f⁻¹).injective he

/-- The self-centralizing endpoint image gives the literal local preimage bound. -/
theorem critical_centralizer_le_join
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha)) :
    stabilizer d.radical a ⊓ centralizer (X d.radical b : Set (FreeAmalgam d.radical)) ≤
      X d.radical b ⊔ Q d.radical a := by
  obtain ⟨f,hf⟩ := exists_to_alpha d a ha
  have hc' := critical_to_alpha h d a ha b hc f hf
  have he : stabilizer d.radical (act d.radical f a) ⊓
      centralizer (X d.radical (act d.radical f b) : Set (FreeAmalgam d.radical)) ≤
      X d.radical (act d.radical f b) ⊔ Q d.radical (act d.radical f a) := by
    simpa only [hf] using critical_centralizer_alpha h e hz hn d himage (act d.radical f b) hc'
  rw [stabilizer_act,X_act,Q_act,← Subgroup.map_sup] at he
  apply (Subgroup.map_le_map_iff_of_injective
    (f := (MulAut.conj f⁻¹).toMonoidHom) (MulAut.conj f⁻¹).injective).mp
  apply le_trans _ he
  apply le_inf
  · exact map_mono inf_le_left
  · rintro x ⟨y,hy,rfl⟩ z ⟨w,hw,rfl⟩
    simpa only [map_mul] using congrArg (MulAut.conj f⁻¹).toMonoidHom (hy.2 w hw)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

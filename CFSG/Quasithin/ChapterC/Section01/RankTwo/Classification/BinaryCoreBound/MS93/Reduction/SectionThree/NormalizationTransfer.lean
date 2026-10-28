module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.LocalGroups
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# MS93 normalization transfer

We prove (4.2)(ii) with normality relative to the finite vertex stabilizer,
without assuming that the free amalgam is finite. The marked SL₃(2) quotient
and its kernel are transported through the actual vertex-group embedding.
No natural-module identification or later Section 4 consequence is used.

For a radius-two M-vertex δ, put K = [Z_δ,Y] and D = Q_α ∩ C(Ltilde_α).
The triple-commutator bound makes KD normalized by Ltilde_α; Q_α also
normalizes it, so KD is normal in the local group. If Q_δ ≤ Q_α, their equal
orders make them equal and K is trivial. Otherwise simplicity of the marked
quotient puts Ltilde_α in the local normal closure of Q_δ. Since Q_δ
centralizes K, normal-closure transfer gives [KD,Ltilde_α] ≤ D. Residual
commutator idempotence removes this central error and gives K ≤ D.
Taking the join over the radius-two generators completes the proof;
the generators of holomorph color already lie in Z_α and centralize Y.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.2)(ii), printed p.882.
-/

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionThree
variable {G : Type*} [Group G]

private theorem commutator_normalized_of_triple_eq_bot
    (A V Y L : Subgroup G) [Y.Normal] (hAV : A ≤ V)
    (htriple : ⁅⁅V,L⁆,Y⁆ = ⊥) : L ≤ normalizer (⁅A,Y⁆ : Subgroup G) := by
  apply le_normalizer_closure_iff.mpr
  rintro l hl _ ⟨a, ha, y, hy, rfl⟩
  have hy' : l * y * l⁻¹ ∈ Y := (inferInstance : Y.Normal).conj_mem y hy l
  have hc : ⁅l,a⁆ ∈ ⁅V,L⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hl (hAV ha)
  have hcy : Commute ⁅l,a⁆ (l * y * l⁻¹) :=
    (commutator_eq_bot_iff_le_centralizer.mp htriple hc _ hy').symm
  have hck : Commute ⁅l,a⁆ ⁅a,l * y * l⁻¹⁆ :=
    (commutator_eq_bot_iff_le_centralizer.mp htriple hc _
      (commutator_le_right A Y (commutator_mem_commutator ha hy'))).symm
  rw [conjugate_commutatorElement, show l * a * l⁻¹ = ⁅l,a⁆ * a by
    simp [commutatorElement_def, mul_assoc]]
  rw [commutatorElement_mul_left_eq_conj_mul, hcy.commutator_eq,
    hck.eq, mul_inv_cancel_right, mul_one]
  exact commutator_mem_commutator ha hy'

private theorem normalizes_commutator (B A Y : Subgroup G)
    (hBA : B ≤ normalizer A) (hBY : B ≤ normalizer Y) :
    B ≤ normalizer (⁅A,Y⁆ : Subgroup G) := by
  intro b hb
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hBA hb),
    mem_normalizer_iff_map_conj_eq.mp (hBY hb)]

/-- The quotient argument used on one radius-two generator. -/
private theorem generator_transfer [Finite G]
    (Q L V Y A J : Subgroup G) [Q.Normal] [L.Normal] [Y.Normal]
    (hpQ : IsPGroup 2 Q) (hpL : IsPPerfect 2 L)
    (hcover : Q ⊔ L = ⊤) (hVQ : V ≤ Q) (hYQ : Y ≤ Q) (hAV : A ≤ V)
    (hQA : Q ≤ normalizer A)
    (htriple : ⁅⁅V,L⁆,Y⁆ ≤ Q ⊓ centralizer (L : Set G))
    (hAJ : ⁅A,J⁆ = ⊥) (hclosure : L ≤ normalClosure (J : Set G)) :
    ⁅A,Y⁆ ≤ Q ⊓ centralizer (L : Set G) := by
  let D := Q ⊓ centralizer (L : Set G)
  have hDcentral : ⁅D,L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hYA : Y ≤ normalizer A := hYQ.trans hQA
  let K := ⁅A,Y⁆
  let N := K ⊔ D
  let q := QuotientGroup.mk' D
  have hKQ : K ≤ Q :=
    (le_normalizer_iff_commutator_le_left.mp hYA).trans (hAV.trans hVQ)
  have hNQ : N ≤ Q := sup_le hKQ inf_le_left
  have hNmap : N.map q = K.map q := by
    simp [N, Subgroup.map_sup, q]
  have hpreimage : (K.map q).comap q = N := by
    simp [comap_map_eq, q, N]
  have hLnorm : L ≤ normalizer N := by
    have hzero : ⁅⁅V.map q,L.map q⁆,Y.map q⁆ = ⊥ := by
      rw [← map_commutator, ← map_commutator, Subgroup.map_eq_bot_iff]
      simpa only [q, QuotientGroup.ker_mk'] using htriple
    let : (Y.map q).Normal := (inferInstance : Y.Normal).map q
      (QuotientGroup.mk'_surjective D)
    have hn := commutator_normalized_of_triple_eq_bot (A.map q) (V.map q)
      (Y.map q) (L.map q) (map_mono hAV) hzero
    rw [← map_commutator] at hn
    have hh := (map_le_iff_le_comap.mp hn).trans
      (le_normalizer_comap q)
    rwa [hpreimage] at hh
  have hQnorm : Q ≤ normalizer N := by
    apply (le_inf (normalizes_commutator Q A Y hQA le_normalizer_of_normal)
      (le_normalizer_of_normal (H := D))).trans
    exact normalizer_inf_normalizer_le_normalizer_sup K D
  let : N.Normal := normalizer_eq_top_iff.mp (top_unique
    (hcover ▸ sup_le hQnorm hLnorm))
  have hNJ : ⁅N,J⁆ ≤ D := by
    have hc : ⁅K,J⁆ = ⊥ := by
      apply le_bot_iff.mp
      exact (commutator_mono
        (le_normalizer_iff_commutator_le_left.mp hYA)
        le_rfl).trans hAJ.le
    have hm : (⁅N,J⁆).map q = ⊥ := by
      rw [map_commutator, hNmap, ← map_commutator, hc, Subgroup.map_bot]
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hm
  have hNL : ⁅N,L⁆ ≤ D := (commutator_mono le_rfl hclosure).trans
    (commutator_normalClosure_le_of_normal N J D hNJ)
  have hNLzero : ⁅N,L⁆ = ⊥ := by
    rw [← commutator_isPPerfect_idempotent L N hpL (hpQ.to_le hNQ) hLnorm]
    exact le_bot_iff.mp ((commutator_mono hNL le_rfl).trans hDcentral.le)
  exact le_inf hKQ (le_sup_left.trans (commutator_eq_bot_iff_le_centralizer.mp hNLzero))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionThree

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionThree
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem local_projection (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) :
    ∃ π : stabilizer R a →* SL, Function.Surjective π ∧
      π.ker = (Q R a).subgroupOf (stabilizer R a) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  let S := stabilizer R (mVertex R g)
  let f := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
  have hf : Function.Injective f := (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
  have hrange : f.range = S := by
    rw [MonoidHom.range_comp]
    exact (stabilizer_mVertex R g).symm
  let e : M ≃* S := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)
  have he : S.subtype.comp e.toMonoidHom = f := by ext x; rfl
  have hQ : (pCore 2 M).map e.toMonoidHom =
      (Q R (mVertex R g)).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [map_map, he, map_subgroupOf_eq_of_le (show Q R (mVertex R g) ≤ S from fun _ hx => hx.1)]
    rw [show f = (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R) from rfl, ← map_map,
      ← Q_alpha R source.two_group source.core_le]
    have hh := Q_act R g (alpha R)
    simpa only [alpha, act_mVertex, one_mul] using hh.symm
  refine ⟨source.projection.comp e.symm.toMonoidHom,
    source.projection_surjective.comp e.symm.surjective, ?_⟩
  rw [← MonoidHom.comap_ker, source.projection_kernel, ← hQ]
  ext x
  constructor
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    change e.symm (e y) ∈ pCore 2 M
    rw [MulEquiv.symm_apply_apply]
    exact hy

private theorem sl_two_perfect : IsPPerfect 2 SL := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  intro N hN hp
  rcases hN.eq_bot_or_eq_top with h | h
  · subst N
    have hSL : IsPGroup 2 SL := hp.of_equiv QuotientGroup.quotientBot
    obtain ⟨n,hn⟩ := hSL.exists_card_eq
    rw [Atlas.Comparisons.Exceptional.sl3Two_card] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; decide
    have hh := (show Nat.Prime 3 by decide).dvd_of_dvd_pow h3
    norm_num at hh
  · exact h

private theorem residual_cover {G : Type*} [Group G] [Finite G]
    (π : G →* SL) (hπ : Function.Surjective π) :
    π.ker ⊔ pResidual 2 G = ⊤ := by
  have hm : (pResidual 2 G).map π = ⊤ := by
    rw [map_pResidual_of_surjective 2 π hπ,
      (pResidual_eq_top_iff 2 SL).mpr sl_two_perfect]
  have hh := congrArg (fun A => A.comap π) hm
  simpa only [comap_map_eq, comap_top, sup_comm] using hh

private theorem residual_le_closure {G : Type*} [Group G] [Finite G]
    (π : G →* SL) (hπ : Function.Surjective π) (hp : IsPGroup 2 π.ker)
    (J : Subgroup G) (hJ : ¬ J ≤ π.ker) :
    pResidual 2 G ≤ normalClosure (J : Set G) := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  let N := normalClosure (J : Set G)
  have hn : (N.map π).Normal := (inferInstance : N.Normal).map π hπ
  have hm : N.map π = ⊤ := by
    rcases hn.eq_bot_or_eq_top with h | h
    · exact (hJ ((le_normalClosure (H := J)).trans ((Subgroup.map_eq_bot_iff _).mp h))).elim
    · exact h
  have hsup : N ⊔ π.ker = ⊤ := by
    have hh := congrArg (fun A => A.comap π) hm
    simpa only [comap_map_eq, comap_top] using hh
  exact sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top N π.ker hp hsup⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionThree

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionThree
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

omit [Finite M] in
private theorem fixedCore_native (a : Vertex R) :
    (fixedCore R a).subgroupOf (stabilizer R a) =
      (Q R a).subgroupOf (stabilizer R a) ⊓
        centralizer (pResidual 2 (stabilizer R a) : Set (stabilizer R a)) := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro l hl
    apply Subtype.ext
    exact hx.2 l (mem_map_of_mem (stabilizer R a).subtype hl)
  · rintro ⟨hx,hc⟩
    refine ⟨hx, ?_⟩
    rintro _ ⟨l,hl,rfl⟩
    exact congrArg Subtype.val (hc l hl)

private theorem commutator_native {G : Type*} [Group G]
    (S A B : Subgroup G) (hA : A ≤ S) (hB : B ≤ S) :
    ⁅A.subgroupOf S,B.subgroupOf S⁆ = (⁅A,B⁆).subgroupOf S := by
  apply map_injective S.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB,
    map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup _ _).trans (sup_le hA hB))]

private theorem radius_two_generator (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false)
    (Y : Subgroup (FreeAmalgam R)) (hYQ : Y ≤ Q R a)
    (hYn : (Y.subgroupOf (stabilizer R a)).Normal)
    (htriple : ⁅Vcirc R a,Y⁆ ≤ fixedCore R a)
    (δ : Vertex R) (hδ : color R δ = false)
    (hd : (cosetGraph R).dist δ a ≤ 2) : ⁅Z R δ,Y⁆ ≤ fixedCore R a := by
  let S := stabilizer R a
  have hQa : Q R a ≤ S := fun _ hx => hx.1
  have hQδ : Q R δ ≤ S := Q_le_stabilizer_of_dist_le_two δ a hδ ha hd
  have hQad : Q R a ≤ stabilizer R δ :=
    Q_le_stabilizer_of_dist_le_two a δ ha hδ (by rwa [SimpleGraph.dist_comm])
  have hAV : Z R δ ≤ V R a := le_iSup_of_le δ (le_iSup_of_le hd le_rfl)
  have hVQ := geometry.V_le_Q hb a ha
  have hAS := hAV.trans (hVQ.trans hQa)
  let : Finite S := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective (inclusion hQa) (inclusion_injective hQa)
  by_cases hle : Q R δ ≤ Q R a
  · have he : Q R δ = Q R a := eq_of_le_of_card_ge hle (by
      rw [source.Q_card a ha, source.Q_card δ hδ])
    have hc : ⁅Z R δ,Y⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono le_rfl (hYQ.trans he.ge)).trans (Z_centralizes_Q R δ hδ).le)
    rw [hc]
    exact bot_le
  · obtain ⟨π,hπ,hker⟩ := local_projection source a ha
    let Q₀ := (Q R a).subgroupOf S
    let V₀ := (V R a).subgroupOf S
    let Y₀ := Y.subgroupOf S
    let A₀ := (Z R δ).subgroupOf S
    let J₀ := (Q R δ).subgroupOf S
    let L₀ := pResidual 2 S
    let : Q₀.Normal := Q_normal R a
    let : Y₀.Normal := hYn
    have hpQ : IsPGroup 2 Q₀ :=
      (Q_isPGroup R source.two_group source.core_le a ha).of_equiv
        (subgroupOfEquivOfLe hQa).symm
    have hcover : Q₀ ⊔ L₀ = ⊤ := by
      change (Q R a).subgroupOf (stabilizer R a) ⊔ pResidual 2 (stabilizer R a) = ⊤
      rw [← hker]
      exact residual_cover π hπ
    have hnot : ¬ J₀ ≤ π.ker := by
      intro h
      apply hle
      rw [hker] at h
      change (Q R δ).subgroupOf S ≤ (Q R a).subgroupOf S at h
      have hh := map_mono (f := S.subtype) h
      simpa only [map_subgroupOf_eq_of_le hQδ, map_subgroupOf_eq_of_le hQa] using hh
    have hclosure : L₀ ≤ normalClosure (J₀ : Set S) :=
      residual_le_closure π hπ (hker.symm ▸ hpQ) J₀ hnot
    have hL : (Ltilde R a).subgroupOf S = L₀ := by
      exact comap_map_eq_self_of_injective S.subtype_injective _
    have hQA : Q₀ ≤ normalizer A₀ :=
      (comap_mono (hQad.trans (Z_normalized R δ))).trans
        (le_normalizer_comap S.subtype)
    have htriple₀ : ⁅⁅V₀,L₀⁆,Y₀⁆ ≤ Q₀ ⊓ centralizer (L₀ : Set S) := by
      rw [← fixedCore_native a]
      have hh := comap_mono (f := S.subtype) htriple
      change (⁅Vcirc R a,Y⁆).subgroupOf S ≤ (fixedCore R a).subgroupOf S at hh
      rw [← commutator_native S (Vcirc R a) Y
        ((Subgroup.commutator_le_sup _ _).trans
          (sup_le (hVQ.trans hQa) (Ltilde_le_stabilizer a)))
        (hYQ.trans hQa), Vcirc,
        ← commutator_native S (V R a) (Ltilde R a) (hVQ.trans hQa)
          (Ltilde_le_stabilizer a), hL] at hh
      exact hh
    have hAJ : ⁅A₀,J₀⁆ = ⊥ := by
      rw [commutator_native S (Z R δ) (Q R δ) hAS hQδ, Z_centralizes_Q R δ hδ]
      exact S.subtype.ker_eq_bot S.subtype_injective
    have hbound := generator_transfer Q₀ L₀ V₀ Y₀ A₀ J₀ hpQ
      (isPPerfect_pResidual 2) hcover (comap_mono hVQ) (comap_mono hYQ)
      (comap_mono hAV) hQA htriple₀ hAJ hclosure
    rw [← fixedCore_native a, commutator_native S (Z R δ) Y hAS (hYQ.trans hQa)] at hbound
    change (⁅Z R δ,Y⁆).subgroupOf S ≤ (fixedCore R a).subgroupOf S at hbound
    have hh := map_mono (f := S.subtype) hbound
    simpa only [map_subgroupOf_eq_of_le
      ((Subgroup.commutator_le_sup _ _).trans (sup_le hAS (hYQ.trans hQa))),
      map_subgroupOf_eq_of_le (show fixedCore R a ≤ S from inf_le_left.trans hQa)] using hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionThree
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionThree

private theorem commutator_iSup_le_of_normalizes {G : Type*} [Group G] {ι : Sort*}
    (A : ι → Subgroup G) (Y D : Subgroup G)
    (hn : (⨆ i, A i) ≤ normalizer D) (hc : ∀ i, ⁅A i,Y⁆ ≤ D) :
    ⁅⨆ i, A i,Y⁆ ≤ D := by
  apply commutator_le.mpr
  intro x hx y hy
  revert y
  induction hx using iSup_induction' with
  | hp i x hx =>
      intro y hy
      exact hc i (commutator_mem_commutator hx hy)
  | h1 =>
      intro y hy
      simpa only [commutatorElement_one_left] using D.one_mem
  | hmul x z hx _ ihx ihz =>
      intro y hy
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact D.mul_mem ((mem_normalizer_iff.mp (hn hx) _).mp (ihz y hy)) (ihx y hy)

private theorem fixedCore_normalized {M : Type*} [Group M] (R : Subgroup M)
    (a : Vertex R) : stabilizer R a ≤ normalizer (fixedCore R a) := by
  apply (normal_subgroupOf_iff_le_normalizer
    (show fixedCore R a ≤ stabilizer R a from inf_le_left.trans (fun _ hx => hx.1))).mp
  rw [fixedCore_native a]
  let : ((Q R a).subgroupOf (stabilizer R a)).Normal := Q_normal R a
  infer_instance

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionThree

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- MS93 (4.2)(ii): transfer the fixed-core commutator bound from Vcirc to V,
with normality of Y only in its vertex stabilizer. -/
theorem LocalSource.normalizationTransfer (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) : NormalizationTransfer R := by
  intro a ha Y hYQ hYn hc
  have hVnorm : V R a ≤ normalizer (fixedCore R a) :=
    (geometry.V_le_Q hb a ha).trans
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans
        (SectionThree.fixedCore_normalized R a))
  apply SectionThree.commutator_iSup_le_of_normalizes _ _ _ hVnorm
  intro δ
  apply SectionThree.commutator_iSup_le_of_normalizes
  · apply iSup_le
    intro hd
    exact (le_iSup_of_le δ (le_iSup_of_le hd le_rfl) : Z R δ ≤ V R a).trans hVnorm
  · intro hd
    by_cases hδ : color R δ = false
    · exact SectionThree.radius_two_generator source geometry hb a ha Y hYQ hYn hc δ hδ hd
    · have hδ' : color R δ = true := by cases hh : color R δ <;> simp_all
      obtain ⟨p,hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist δ a
      have hnEven : ¬ Even p.length := by
        rw [walk_even_iff_color_eq, hδ', ha]
        decide
      have hlen : p.length = 1 := by
        have hle : p.length ≤ 2 := hp.trans_le hd
        rw [Nat.even_iff] at hnEven
        omega
      have hadj : Adjacent R a δ :=
        adjacent_symm R ((cosetGraph_adj R _ _).mp (p.adj_of_length_eq_one hlen))
      have hδZ : Z R δ ≤ Z R a := by
        rw [Z, if_neg hδ, Z, if_pos ha]
        exact le_iSup_of_le δ (le_iSup_of_le hadj le_rfl)
      exact (commutator_mono hδZ hYQ).trans ((Z_centralizes_Q R a ha).le.trans bot_le)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93

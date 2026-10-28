module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.SourceGeometry
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Quadratic
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# A surviving central point in the original quintic four-ball kernel

An abelian second-vertex span excludes critical distance two: both modules
of such a critical pair lie in the same abelian neighbor span. The track
therefore has length at least three. The central point belongs to every
neighboring first-vertex module and consequently fixes the radius-four
ball at H. Its original order two proves that this ball kernel is nontrivial.

Source: Aschbacher--Smith F.7.10--11, pp.313--314, applied to the plane
and quintic closure in 14.2.20--21, pp.988--989. No model identification,
stabilizer order or path-transitivity hypothesis is used.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (exists_smul_base)
open CFSG.Quasithin.ChapterF.Section07
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

private theorem track_ge_three_of_abelian_span
    {K : Type*} [Group K] (F : Bool → Subgroup K)
    (D : Track.SourceSetup F) (hne : D.V ≠ ⊥)
    (hb : 1 < D.track hne)
    (hab : IsMulCommutative (conjugateSpanBy D.seed (F true))) :
    3 ≤ D.track hne := by
  by_contra hh
  have hb2 : D.track hne = 2 := by omega
  obtain ⟨v, hv, hcrit⟩ := (D.critical_witness hne).1
  have hvtype := CriticalPairs.even_endpoint_type F D hne hv (hb2 ▸ (by decide))
  have hav : base F false ≠ v := by
    intro he
    rw [← he] at hv
    simp only [SimpleGraph.dist_self] at hv
    omega
  obtain ⟨w, hvw, hw⟩ := exists_predecessor F D.generates (base F false) v hav
  have haw : (graph F).Adj (base F false) w :=
    SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  have hwtype : w.type = true := by
    have hn := haw.1
    change false ≠ w.type at hn
    cases hw' : w.type with
    | false => exact (hn hw'.symm).elim
    | true => rfl
  have hcomm : IsMulCommutative (CriticalPairs.vertexModule F D.seed w) := by
    obtain ⟨g, hg⟩ := exists_smul_base F w
    rw [hwtype] at hg
    rw [← hg, CriticalPairs.vertexModule_translate F D.seed D.seed_normalized,
      CriticalPairs.second_base_module_eq_conjugate_join F D.seed D.seed_normalized,
      ← conjugateSpanBy_eq_iSup_conj]
    let := hab
    exact Subgroup.map_isMulCommutative (conjugateSpanBy D.seed (F true))
      (MulAut.conj g).toMonoidHom
  have hleft : D.seed ≤ CriticalPairs.vertexModule F D.seed w := by
    calc
      D.seed = CriticalPairs.firstModule F D.seed (base F false) :=
        (CriticalPairs.firstModule_base F D.seed D.seed_normalized).symm
      _ ≤ CriticalPairs.vertexModule F D.seed w :=
        CriticalPairs.firstModule_le_vertexModule_of_adj F D.seed hwtype haw.symm
  have hright : CriticalPairs.vertexModule F D.seed v ≤
      CriticalPairs.vertexModule F D.seed w := by
    rw [CriticalPairs.vertexModule_first F D.seed hvtype]
    exact CriticalPairs.firstModule_le_vertexModule_of_adj F D.seed hwtype hvw.symm
  apply CriticalPairs.even_pair_commutator_ne_bot F D hne hv (hb2 ▸ (by decide)) hcrit
  exact bot_unique ((commutator_mono hleft hright).trans
    (commutator_self_eq_bot_iff.mpr hcomm).le)

private theorem central_seed_le_next_ball
    {K : Type*} [Group K] (F : Bool → Subgroup K)
    (D : Track.SourceSetup F) (hne : D.V ≠ ⊥)
    (hb : 3 ≤ D.track hne) (Z : Subgroup K)
    (hZ : Z ≤ D.seed) (hc : F true ≤ centralizer (Z : Set K)) :
    Z ≤ ballKernel F (base F true) 4 := by
  have hseed3 : D.seed ≤ ballKernel F (base F false) 3 :=
    (D.track_spec hne).2.1.trans (ballKernel_antitone F _ hb)
  have hZseed (w : Vertex F) (hw : (graph F).Adj (base F true) w) :
      Z ≤ CriticalPairs.firstModule F D.seed w := by
    obtain ⟨g, hg, he⟩ := locally_transitive F
      (show (graph F).Adj (base F true) (base F false) from
        ⟨by change true ≠ false; decide,
          Subgroup.CosetGeometry.incident_base F true false⟩) hw
    have hg' : g ∈ F true := by
      simpa only [stabilizer, Subgroup.CosetGeometry.stabilizer_base] using hg
    rw [← he, CriticalPairs.firstModule_translate_base F D.seed D.seed_normalized]
    intro z hz
    refine ⟨z, hZ hz, ?_⟩
    change g * z * g⁻¹ = z
    have hh := mem_centralizer_iff.mp (hc hg') z hz
    rw [← hh, mul_inv_cancel_right]
  intro z hz v hv
  rw [mem_ball_iff F D.generates] at hv
  by_cases he : base F true = v
  · subst v
    apply hseed3 (hZ hz) (base F true)
    apply ball_mono F (base F false) (show 1 ≤ 3 by decide)
    exact (mem_ball_one F _ _).mpr (Or.inl
      ⟨Bool.false_ne_true, Subgroup.CosetGeometry.incident_base F false true⟩)
  · obtain ⟨p, hp⟩ := (connected F D.generates).exists_walk_length_eq_dist (base F true) v
    cases p with
    | nil => exact (he rfl).elim
    | @cons _ w _ hw p =>
      have hwt : w.type = false := by
        have hn := hw.1
        change true ≠ w.type at hn
        cases hw' : w.type with
        | false => rfl
        | true => exact (hn hw'.symm).elim
      have hfix := CriticalPairs.firstModule_le_ballKernel F D.seed
        D.seed_normalized hseed3 hwt (hZseed w hw hz)
      apply hfix v
      rw [mem_ball_iff F D.generates]
      have hd := SimpleGraph.dist_le p
      simp only [SimpleGraph.Walk.length_cons] at hp
      omega

variable {G : Type*} [Group G] [Finite G]

/-- The original quintic source has critical distance at least three.
The abelian neighbor span excludes the even distance-two commutator. -/
theorem source_quintic_track_ge_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let L := X ⊔ H
    let F : Bool → Subgroup L := fun i => if i then H.subgroupOf L else X.subgroupOf L
    ∃ (D : Track.SourceSetup F) (hne : D.V ≠ ⊥),
      D.seed.map L.subtype = localModule T M ∧
      (D.sylow false : Subgroup (F false)).map
        (L.subtype.comp (F false).subtype) = (T : Subgroup G) ∧
      D.seed ≤ (F true).pCoreIn 2 ∧ 3 ≤ D.track hne := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L := X ⊔ H
  let F : Bool → Subgroup L := fun i => if i then H.subgroupOf L else X.subgroupOf L
  obtain ⟨D, hne, hseed, hsylow, hcore, hb⟩ := source_quintic_track_gt_one
    hG T hempty hM hu hmany hcard e H hH hi
  let U := conjugateSpanBy D.seed (F true)
  have hUmap : U.map L.subtype = conjugateSpanBy (localModule T M) H := by
    rw [map_conjugateSpanBy, hseed]
    change conjugateSpanBy (localModule T M) ((H.subgroupOf L).map L.subtype) = _
    rw [map_subgroupOf_eq_of_le (show H ≤ L from le_sup_right)]
  have hab := (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  let := hab
  have hUcomm : IsMulCommutative U := by
    apply commutator_self_eq_bot_iff.mp
    apply (map_eq_bot_iff_of_injective _ L.subtype_injective).mp
    rw [map_commutator, hUmap]
    exact commutator_self_eq_bot_iff.mpr inferInstance
  exact ⟨D, hne, hseed, hsylow, hcore,
    track_ge_three_of_abelian_span F D hne hb hUcomm⟩

/-- The original central involution survives in the radius-four kernel
of the quintic vertex. This supplies the geometric factor two in the
Sylow order bound. -/
theorem source_quintic_four_ball_kernel_ne_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    Geometry.ballKernel X H (Geometry.base X H true) 4 ≠ ⊥ := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L := X ⊔ H
  let F : Bool → Subgroup L := fun i => if i then H.subgroupOf L else X.subgroupOf L
  obtain ⟨D, hne, hseed, _, _, hb3⟩ := source_quintic_track_ge_three
    hG T hempty hM hu hmany hcard e H hH hi
  let Z := (centralInvolutions T).subgroupOf L
  have hZL : centralInvolutions T ≤ L :=
    (centralInvolutions_le_sylow T).trans (le_sup_right.trans le_sup_left)
  have hZseed : Z ≤ D.seed := by
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [hseed, map_subgroupOf_eq_of_le hZL]
    exact le_conjugateSpanBy _ _
  have hc : F true ≤ centralizer (Z : Set L) := by
    have hh := (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
    intro a ha
    rw [mem_centralizer_iff]
    intro z hz
    exact Subtype.ext (mem_centralizer_iff.mp (hh ha) z hz)
  have hfix := central_seed_le_next_ball F D hne hb3 Z hZseed hc
  have hZne : Z ≠ ⊥ := by
    intro he
    have hc := Nat.card_congr (subgroupOfEquivOfLe hZL).toEquiv
    change Nat.card Z = Nat.card (centralInvolutions T) at hc
    rw [he, card_bot, plane_centralInvolutions_card T M hM.1.2 hcard e] at hc
    omega
  have hk : ballKernel F (base F true) 4 ≠ ⊥ := fun he => hZne (bot_unique (hfix.trans he.le))
  have hf : F = Geometry.family X H := by funext i; cases i <;> rfl
  exact (congrArg (fun E : Bool → Subgroup L =>
    ballKernel E (base E true) 4 ≠ ⊥) hf).mp hk

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam

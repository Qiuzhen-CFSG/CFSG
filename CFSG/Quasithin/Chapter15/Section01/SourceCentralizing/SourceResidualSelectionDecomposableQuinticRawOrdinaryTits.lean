module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryAction
public import Theory.SpecificGroups.Tits.FiveSylowOvergroups
public import Theory.GroupAction.ComponentRankAction.OuterTwo

/-! The original quintic source excludes the actual Tits ordinary component.
Five-rank and the native outer automorphism group put the genuine quintic
actor inside the component. Native Sylow-overgroup coverage and the original
seed action place that actor in the marked intersection. Its literal residual
identity then centralizes the moving module, contradicting original movement.
No marked placement or component-data record is assumed. -/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem raw_tits_five_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {V Z1 L : Subgroup G} [IsElementaryAbelian 2 V]
    (hZ : Z1 ≤ V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G))
      (L.subgroupOf (centralizer (Z1 : Set G))))
    (e : L ≃* Tits.ParrottGroup) :
    L = (primeToResidual 5 (centralizer (Z1 : Set G))).map
      (centralizer (Z1 : Set G)).subtype := by
  let G1 := centralizer (Z1 : Set G)
  have hrG : primeRank 5 G1 ≤ 2 :=
    (caseI_centralizer_sqtk hG Z1 hZne
      ((IsElementaryAbelian.isPGroup 2 V).to_le hZ)).stronglyQuasithin 5 (by decide) (by decide)
  let K := L.subgroupOf G1
  let a : K ≃* Tits.ParrottGroup := (subgroupOfEquivOfLe hLG).trans e
  have hz := Tits.RelativeSylowMarking.center_eq_bot Tits.parrottFiniteImageEquiv
  have hc : center K = ⊥ := by
    apply bot_unique
    intro x hx
    have he := (centerCongr a ⟨x,hx⟩).property
    change a x ∈ center Tits.ParrottGroup at he
    rw [hz,mem_bot] at he
    exact mem_bot.mpr (a.map_eq_one_iff.mp he)
  let q : (K ⧸ center K) ≃* Tits.ParrottGroup :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans a
  have hrK : 2 ≤ primeRank 5 K := by
    rw [primeRank_equiv 5 a]
    exact Tits.FiveSylowOvergroups.five_rank_ge_two
  have he := (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual_of_outer_twoGroup
    hL (by rw [hc]; simp) hrK hrG q (by decide)
    Tits.OuterOddSubgroups.parrott_outer_isPGroup).2
  have hm := congrArg (map G1.subtype) he
  rwa [map_subgroupOf_eq_of_le hLG] at hm

private theorem raw_tits_sylow_center_le_partner
    (T : Sylow 2 G) {M Mc Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hnZ : centralInvolutions T ≤ normalizer (L : Set G))
    (hSyl : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (h115 : ∃ R : Sylow 2 (centralizer (Z1 : Set G)),
      (R : Subgroup (centralizer (Z1 : Set G))).map (centralizer (Z1 : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer (Z1 : Set G) ∧
      ∀ z ∈ centralInvolutions T, z ≠ 1 →
        Chapter1.Lemma115Hypotheses (centralizer (Z1 : Set G)) R Mc z)
    (e : L ≃* Tits.ParrottGroup) :
    ∃ P : Sylow 2 L,
      (P : Subgroup L).map L.subtype = ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L ∧
      (centralizer ((center P).map (P : Subgroup L).subtype : Set L)).map L.subtype ≤ Mc := by
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨R,hR,h115⟩ := h115
  obtain ⟨P,hP⟩ := hSyl
  let α := L.normalizerMonoidHom ⟨z,hnZ hz⟩
  have ha (x : L) : (α x : G) = z*x*z⁻¹ := rfl
  have hfix (x : L) (hx : x ∈ P) : α x = x := by
    apply Subtype.ext
    rw [ha]
    exact mul_inv_eq_iff_eq_mul.mpr
      ((h115 z hz hzne).central x (hR.symm ▸ (hP ▸ mem_map_of_mem L.subtype hx).1)).symm
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨t,ht,he⟩ := Tits.SylowPointwiseInner.parrott_fixing_sylow_inner Q
    (MulAut.congr e α) (by
      rintro _ ⟨x,hx,rfl⟩
      change e (α (e.symm (e x))) = e x
      rw [e.symm_apply_apply,hfix x hx])
  obtain ⟨u,huP,rfl⟩ := ht
  have hi : α = MulAut.conj u := by
    apply (MulAut.congr e).injective
    rw [MulAut.congr_conj]
    exact he
  have huZ : u ∈ (center P).map (P : Subgroup L).subtype := by
    refine ⟨⟨u,huP⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have hh := hfix x x.property
    rw [hi] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  refine ⟨P,hP,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  apply (h115 z hz hzne).centralizer_le
  apply mem_centralizer_singleton_iff.mpr
  have hfixed : α x = x := by
    rw [hi]
    exact mul_inv_eq_iff_eq_mul.mpr (hx u huZ)
  have hh := ha x
  rw [hfixed] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm

private theorem raw_tits_actor_contradiction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L Y : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M) (hn : M ≤ normalizer (V : Set G))
    (hZ : Z1 ≤ V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G))
      (L.subgroupOf (centralizer (Z1 : Set G))))
    (hSyl : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hnZ : centralInvolutions T ≤ normalizer (L : Set G))
    (h115 : ∃ P : Sylow 2 (centralizer (Z1 : Set G)),
      (P : Subgroup (centralizer (Z1 : Set G))).map (centralizer (Z1 : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer (Z1 : Set G) ∧
      ∀ z ∈ centralInvolutions T, z ≠ 1 →
        Chapter1.Lemma115Hypotheses (centralizer (Z1 : Set G)) P Mc z)
    (hI : (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype)
    (houtM : ¬L ≤ M)
    (hY : IsPGroup 5 Y) (hperfect : IsPPerfect 2 Y) (hYC : Y ≤ M ⊓ centralizer (Z1 : Set G))
    (hWY : let C := M ⊓ centralizer (Z1 : Set G); let R := (pResidual 2 C).map C.subtype
      ⁅⁅V,R⁆,Y⁆ = ⁅V,R⁆)
    (hmove : let C := M ⊓ centralizer (Z1 : Set G); let R := (pResidual 2 C).map C.subtype
      ⁅L,⁅V,R⁆⁆ ≠ ⊥)
    (e : L ≃* Tits.ParrottGroup) : False := by
  let G1 := centralizer (Z1 : Set G)
  let C := M ⊓ G1
  let R := (pResidual 2 C).map C.subtype
  let W := ⁅V,R⁆
  have hres := raw_tits_five_residual hG hZ hZne hLG hL e
  have hYL : Y ≤ L := by
    rw [hres]
    intro y hy
    obtain ⟨k,hk⟩ := hY ⟨y,hy⟩
    exact ⟨⟨y,(hYC hy).2⟩,mem_primeToResidual_of_pow (p := 5) (n := k)
      (Subtype.ext (congrArg (fun x : Y => (x : G)) hk)),rfl⟩
  obtain ⟨P,hP,hplace⟩ := raw_tits_sylow_center_le_partner T hM hnZ hSyl h115 e
  have hfive : Y.subgroupOf L ≤ centralizer
      ((center P).map (P : Subgroup L).subtype : Set L) := by
    apply Tits.FiveSylowOvergroups.five_subgroup_le_sylow_center_centralizer e P
      ((M ⊓ L).subgroupOf L) (Y.subgroupOf L)
    · intro he
      exact houtM ((subgroupOf_eq_top.mp he).trans inf_le_left)
    · intro x hx
      have hh := hP ▸ mem_map_of_mem L.subtype hx
      exact ⟨hM.1.2 hh.1.1,hh.2⟩
    · exact comap_mono (le_inf (hYC.trans inf_le_left) hYL)
    · exact hY.of_injective (subgroupOfEquivOfLe hYL).toMonoidHom
        (subgroupOfEquivOfLe hYL).injective
  have hYMc : Y ≤ Mc := by
    intro y hy
    exact hplace ⟨⟨y,hYL hy⟩,hfive hy,rfl⟩
  have hcentral : Y ≤ centralizer (V : Set G) := by
    have hh := embedded_pResidual_mono 2
      (le_inf (le_inf (hYC.trans inf_le_left) hYMc) (hYC.trans inf_le_right))
    rw [(pResidual_eq_top_iff 2 Y).mpr hperfect,←MonoidHom.range_eq_map,range_subtype,hI] at hh
    exact hh.trans ((map_subtype_le _).trans inf_le_right)
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp
    (((map_subtype_le _).trans inf_le_left).trans hn)
  have hzero : ⁅W,Y⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hcentral.trans (centralizer_le hWV))
  have hWzero : W = ⊥ := hWY.symm.trans hzero
  exact hmove (by change ⁅L,W⁆ = ⊥; rw [hWzero,commutator_bot_right])

/-- The original full quintic source excludes Tits on the same raw ordinary
component, deriving the marked centralizer placement from its actual seed action. -/
theorem PreparedChosenModule.decomposable_five_raw_ordinary_not_tits
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let S := (T : Subgroup G) ⊓ G1
      ∀ {L : Subgroup G}, L ≤ G1 → IsComponent G1 (L.subgroupOf G1) →
        Chapter1.IsSylowIn 2 (S ⊓ L) L →
        centralInvolutions T ≤ normalizer (L : Set G) →
        (∃ P : Sylow 2 G1, (P : Subgroup G1).map G1.subtype = S ∧
          ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses G1 P Mc z) →
        (pResidual 2 (M ⊓ Mc ⊓ G1 : Subgroup G)).map (M ⊓ Mc ⊓ G1).subtype =
          (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
            (M ⊓ centralizer (V : Set G)).subtype →
        ¬L ≤ M → ⁅L,⁅V,R⁆⁆ ≠ ⊥ → IsEmpty (L ≃* Tits.ParrottGroup) := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R S L hLG hLc hSyl hnZ h115 hI houtM hmove
  refine ⟨fun e => ?_⟩
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  obtain ⟨Y,hY,hperfect,hYA,_,_,_,_,hBY,_⟩ :=
    s.exists_permuting_quintic_actor hM.1.2 h.normalized h.le_selected c d π hp hs hJi hfive
  have hYC : Y ≤ C := hYA.trans (map_subtype_le _)
  have hWB := (s.full_residual_geometry hM.1.2 h.normalized c d π hp hs hJi).2.1
  have hWY : ⁅⁅localModule T M,R⁆,Y⁆ = ⁅localModule T M,R⁆ := by
    rw [hWB]
    exact hBY
  have hZne : Z1 ≠ ⊥ := (one_lt_card_iff_ne_bot Z1).mp (by
    rw [show Nat.card Z1 = 4 from s.thompson_card s.first]
    decide)
  exact raw_tits_actor_contradiction hG T hM h.normalized
    (inf_le_left.trans (plane_le _)) hZne hLG hLc hSyl hnZ h115 hI houtM
    hY hperfect hYC hWY hmove e

end CFSG.Quasithin.Chapter15.Section01

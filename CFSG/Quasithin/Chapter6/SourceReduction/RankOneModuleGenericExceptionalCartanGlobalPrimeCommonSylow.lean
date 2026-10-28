module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeOriginalComponent

/-!
# Common-component orbits at the changed Sylow

Write X = ⟨N_G(T₀),H⟩, and let I be the actual common C-component over R.
Source 1.2.1 makes its span under either ambient Sylow normal in X, so
both spans equal the same Kplus. This perfect span normalizes I.

If T moves I, its normalizer in T is exactly T₀: it contains T₀, which
has index two. Therefore T ∩ Kplus lies in T₀. Sylow maximality then
identifies U ∩ Kplus with T ∩ Kplus, and equal Sylow orders give
N_U(I) = T₀ as well. The final application selects I on the original
changed-Sylow witness and keeps its uniqueness and relative normality.
A moved common component forces the original R to be an actual A₅
H-component with p = 5 and n ≠ 2. The only remaining containing quotients
are J₁ and odd-prime PSL₂; the Bender rows cannot properly contain R.

This proves the common-orbit and moved-component Sylow comparisons used
on printed p.648. The selected R may still be a parabolic; equality of
its changed orbit with the original residual, and the comparison with
the original S in the remaining cases, are not asserted here.
Source: Aschbacher–Smith 1.2.1(3), p.504, and 5.2.2, pp.648–649,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

private theorem component_sylow_spans
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    {I : Subgroup G} (hI : I.IsCComponent) (T U : Sylow 2 G) :
    conjugateSpanBy I (U : Subgroup G) = conjugateSpanBy I (T : Subgroup G) ∧
      conjugateSpanBy I (T : Subgroup G) ≤ normalizer (I : Set G) := by
  let J := conjugateSpanBy I (T : Subgroup G)
  let J₁ := conjugateSpanBy I (U : Subgroup G)
  have ho := Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hI
  let : J.Normal := conjugateSpanBy_sylow_normal I T ho
  let : J₁.Normal := conjugateSpanBy_sylow_normal I U ho
  have he : J₁ = J := le_antisymm
    (conjugateSpanBy_le (le_conjugateSpanBy I _) le_normalizer_of_normal)
    (conjugateSpanBy_le (le_conjugateSpanBy I _) le_normalizer_of_normal)
  let : Group.IsPerfect I := hI.perfect
  let : Group.IsPerfect J := conjugateSpanBy_isPerfect I (T : Subgroup G)
  have hp : IsPPerfect 2 J := by
    intro N hN htwo
    let : N.Normal := hN
    by_contra hn
    let : Nontrivial (J ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
    let : Group.IsPerfect (J ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (J ⧸ N) := htwo.isNilpotent
    exact Group.IsPerfect.not_isSolvable (J ⧸ N) inferInstance
  exact ⟨he,Chapter1.Section02.twoPerfect_normalizes_cComponent_source hQ hI hp⟩

omit [Finite G] in
private theorem index_two_intermediate
    {A N T : Subgroup G} (hAT : A ≤ T) (hi : A.relIndex T = 2)
    (hAN : A ≤ N) (hn : ¬ T ≤ N) : T ⊓ N = A := by
  have hle : A ≤ T ⊓ N := le_inf hAT hAN
  have hh := relIndex_mul_relIndex A (T ⊓ N) T hle inf_le_left
  rw [hi] at hh
  have hprime : (A.relIndex (T ⊓ N) * (T ⊓ N).relIndex T).Prime := hh ▸ Nat.prime_two
  rcases (Nat.prime_mul_iff.mp hprime) with ⟨_,he⟩ | ⟨_,he⟩
  · exact (hn ((relIndex_eq_one.mp he).trans inf_le_right)).elim
  · exact le_antisymm (relIndex_eq_one.mp he) hle

/-- The two ambient Sylows have the same orbit on the actual common
component. Its orbit normalizes that component, retaining relative normality. -/
theorem LocalData.changedSylow_common_orbit_eq
    {T U : Sylow 2 G} {L W H A B D R I : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hTU : normalizingSylow T R ≤ (U : Subgroup G))
    (hIX : I ≤ normalizer (normalizingSylow T R : Set G) ⊔ H)
    (hI : (I.subgroupOf (normalizer (normalizingSylow T R : Set G) ⊔ H)).IsCComponent) :
    conjugateSpanBy I (U : Subgroup G) = conjugateSpanBy I (T : Subgroup G) ∧
      conjugateSpanBy I (T : Subgroup G) ≤ normalizer (I : Set G) := by
  let X := normalizer (normalizingSylow T R : Set G) ⊔ H
  have hTX : (T : Subgroup G) ≤ X :=
    (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right
  have hUX : (U : Subgroup G) ≤ X :=
    (d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz U.isPGroup' hTU).trans le_sup_left
  have hQ := Chapter3.sqtk_of_mem_H h.qtke (d.common_normal_overgroup h hH c hd hz).1
  have hQbar : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
    refine ⟨?_,hQ.isKGroup.quotient _⟩
    intro q hq ho
    let : Fact q.Prime := ⟨hq⟩
    exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 X) pCore_isPGroup).trans
      (hQ.stronglyQuasithin q hq ho)
  obtain ⟨he,hn⟩ := component_sylow_spans hQbar hI (T.subtype hTX) (U.subtype hUX)
  have hmap (S : Sylow 2 G) (hSX : (S : Subgroup G) ≤ X) :
      (conjugateSpanBy (I.subgroupOf X) (S.subtype hSX : Subgroup X)).map X.subtype =
        conjugateSpanBy I (S : Subgroup G) := by
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hIX]
    change conjugateSpanBy I (((S : Subgroup G).subgroupOf X).map X.subtype) = _
    rw [map_subgroupOf_eq_of_le hSX]
  constructor
  · have hh := congrArg (map X.subtype) he
    change (conjugateSpanBy (I.subgroupOf X) (U.subtype hUX : Subgroup X)).map X.subtype =
      (conjugateSpanBy (I.subgroupOf X) (T.subtype hTX : Subgroup X)).map X.subtype at hh
    rw [hmap U hUX,hmap T hTX] at hh
    exact hh
  · rw [←hmap T hTX]
    rw [←subgroupOf_normalizer_eq hIX] at hn
    exact (map_mono (f := X.subtype) hn).trans (map_comap_le _ _)

/-- When the common component is moved, its whole common orbit has the
same intersection with T, T₀ and the changed ambient Sylow. -/
theorem LocalData.changedSylow_moved_common_intersections
    {T U : Sylow 2 G} {L W H A B D R I : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hTU : normalizingSylow T R ≤ (U : Subgroup G))
    (hIX : I ≤ normalizer (normalizingSylow T R : Set G) ⊔ H)
    (hI : (I.subgroupOf (normalizer (normalizingSylow T R : Set G) ⊔ H)).IsCComponent)
    (hTI : normalizingSylow T R ≤ normalizer (I : Set G))
    (hm : ¬ (T : Subgroup G) ≤ normalizer (I : Set G)) :
    (T : Subgroup G) ⊓ normalizer (I : Set G) = normalizingSylow T R ∧
      let Kplus := conjugateSpanBy I (T : Subgroup G)
      (T : Subgroup G) ⊓ Kplus = normalizingSylow T R ⊓ Kplus ∧
      (U : Subgroup G) ⊓ Kplus = (T : Subgroup G) ⊓ Kplus ∧
      ¬ (U : Subgroup G) ≤ normalizer (I : Set G) ∧
      (U : Subgroup G) ⊓ normalizer (I : Set G) = normalizingSylow T R := by
  obtain ⟨he,hKN⟩ := d.changedSylow_common_orbit_eq h hH c hd hz hTU hIX hI
  have hN : (T : Subgroup G) ⊓ normalizer (I : Set G) = normalizingSylow T R :=
    index_two_intermediate inf_le_left (d.normalizingSylow_index hH.1.1.2 c hd hz) hTI hm
  let Kplus := conjugateSpanBy I (T : Subgroup G)
  have hKT0 : (T : Subgroup G) ⊓ Kplus ≤ normalizingSylow T R := by
    rw [←hN]
    exact inf_le_inf_left _ hKN
  have hT0 : (T : Subgroup G) ⊓ Kplus = normalizingSylow T R ⊓ Kplus :=
    le_antisymm (le_inf hKT0 inf_le_right) (inf_le_inf_right _ inf_le_left)
  obtain ⟨Q,hQ⟩ := NormalSylowQuotientAction.intersection_sylow T Kplus
    (le_normalizer_conjugateSpanBy I _)
  have hQU : (Q : Subgroup Kplus) ≤ (U : Subgroup G).subgroupOf Kplus := by
    rw [hQ]
    intro x hx
    exact hTU (hKT0 ⟨hx,x.property⟩)
  have hUQ := Q.is_maximal' (U.isPGroup'.comap_subtype) hQU
  have hinter : (U : Subgroup G) ⊓ Kplus = (T : Subgroup G) ⊓ Kplus := by
    have hh := congrArg (map Kplus.subtype) hUQ
    change ((U : Subgroup G).subgroupOf Kplus).map Kplus.subtype =
      (Q : Subgroup Kplus).map Kplus.subtype at hh
    simpa only [hQ,subgroupOf_map_subtype] using hh
  have hUm : ¬ (U : Subgroup G) ≤ normalizer (I : Set G) := by
    intro hUI
    have hUI' : conjugateSpanBy I (U : Subgroup G) = I :=
      le_antisymm (conjugateSpanBy_le le_rfl hUI) (le_conjugateSpanBy I _)
    have hKI : Kplus = I := he.symm.trans hUI'
    exact hm (hKI ▸ le_normalizer_conjugateSpanBy I (T : Subgroup G))
  have hiU : (normalizingSylow T R).relIndex (U : Subgroup G) = 2 := by
    have hhT := relIndex_mul_relIndex (⊥ : Subgroup G) (normalizingSylow T R)
      (T : Subgroup G) bot_le inf_le_left
    have hhU := relIndex_mul_relIndex (⊥ : Subgroup G) (normalizingSylow T R)
      (U : Subgroup G) bot_le hTU
    simp only [relIndex_bot_left,d.normalizingSylow_index hH.1.1.2 c hd hz] at hhT hhU
    have hc : Nat.card (T : Subgroup G) = Nat.card (U : Subgroup G) :=
      T.card_eq_multiplicity.trans U.card_eq_multiplicity.symm
    nlinarith [Nat.card_pos (α := normalizingSylow T R)]
  exact ⟨hN,hT0,hinter,hUm,index_two_intermediate hTU hiU hTI hUm⟩

/-- Select the actual common overcomponent and retain its common Sylow
orbit and the moved-case intersections on the original changed Sylow. -/
theorem LocalData.changedSylow_common_orbit_geometry
    {T U : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (hU : (U : Subgroup G) =
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
    let X := normalizer (normalizingSylow T R : Set G) ⊔ H
    ∃ I : Subgroup G, R < I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
      normalizingSylow T R ≤ normalizer (I : Set G) ∧
      (∀ J : Subgroup G, J ≤ X → (J.subgroupOf X).IsCComponent → R ≤ J → J = I) ∧
      let Kplus := conjugateSpanBy I (T : Subgroup G)
      residual H ≤ Kplus ∧ Kplus ≤ X ∧ (Kplus.subgroupOf X).Normal ∧
        T₁ ≤ normalizer (Kplus : Set G) ∧ conjugateSpanBy R T₁ < Kplus ∧
        conjugateSpanBy I T₁ = Kplus ∧ Kplus ≤ normalizer (I : Set G) ∧
        (¬ (T : Subgroup G) ≤ normalizer (I : Set G) →
          (T : Subgroup G) ⊓ normalizer (I : Set G) = normalizingSylow T R ∧
          (T : Subgroup G) ⊓ Kplus = normalizingSylow T R ⊓ Kplus ∧
          T₁ ⊓ Kplus = (T : Subgroup G) ⊓ Kplus ∧
          ¬ T₁ ≤ normalizer (I : Set G) ∧
          T₁ ⊓ normalizer (I : Set G) = normalizingSylow T R) := by
  obtain ⟨I,hRI,hIX,hI,hTI,hu,hKJ,hJX,hJn,hUJ,hK0J⟩ :=
    d.changedSylow_common_orbit_strict h hH c hd hz P hTP hU
  obtain ⟨he,hN⟩ := d.changedSylow_common_orbit_eq h hH c hd hz
    (hTP.trans_eq hU.symm) hIX hI
  rw [hU] at hUJ hK0J he
  refine ⟨I,hRI,hIX,hI,hTI,hu,hKJ,hJX,hJn,hUJ,hK0J,he,hN,?_⟩
  intro hm
  have hh := d.changedSylow_moved_common_intersections h hH c hd hz
    (hTP.trans_eq hU.symm) hIX hI hTI hm
  simpa only [hU] using hh

/-- A moved common overcomponent comes from the original A₅ component
branch, and its quotient is J₁ or odd-prime PSL₂. The diagram residual
would instead make that same containing component normal in X. -/
theorem LocalData.moved_common_component_models
    {T : Sylow 2 G} {L W H A B D R I : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hs : SelectedSourceModels H R) (hRI : R < I)
    (hIX : I ≤ normalizer (normalizingSylow T R : Set G) ⊔ H)
    (hI : (I.subgroupOf (normalizer (normalizingSylow T R : Set G) ⊔ H)).IsCComponent)
    (hu : ∀ J : Subgroup G, J ≤ normalizer (normalizingSylow T R : Set G) ⊔ H →
      (J.subgroupOf (normalizer (normalizingSylow T R : Set G) ⊔ H)).IsCComponent →
      R ≤ J → J = I)
    (hm : ¬ (T : Subgroup G) ≤ normalizer (I : Set G)) :
    (R.subgroupOf H).IsCComponent ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
      p = 5 ∧ n ≠ 2 ∧
      (Nonempty ((I ⧸ pCore 2 I) ≃* Janko1.Model) ∨
        ∃ q : ℕ, q.Prime ∧ Odd q ∧ ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 q) := by
  let X := normalizer (normalizingSylow T R : Set G) ⊔ H
  have hTX : (T : Subgroup G) ≤ X :=
    (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right
  have hRX : R ≤ X := hRI.le.trans hIX
  have hC : (R.subgroupOf H).IsCComponent := by
    by_contra hn
    have hIn := (d.common_component_original_residual h hH c hd hz
      (hs.residual_component_of_not_right hn) hu).2
    exact hm (hTX.trans ((normal_subgroupOf_iff_le_normalizer hIX).mp hIn))
  have hRlocal := d.right_mem_original_local_family hH.1.1 hC
  have hIlocal : I ∈ Chapter1.L G (T : Subgroup G) :=
    Chapter1.mem_L_of_cComponent (d.common_normal_overgroup h hH c hd hz).1
      ⟨T.subtype hTX,map_subgroupOf_eq_of_le hTX⟩ hIX hI
  have hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 := by
    by_contra hn
    have hmax := d.right_mem_LStar_of_nonA5 h hH c hd hz hRlocal hn
    exact hRI.ne (hmax.2 I hIlocal hRI.le).symm
  have hp5 := d.selected_A5_actor_prime h hH hgen c hd hz hs hthree hA5
  have hn2 : n ≠ 2 := by
    intro hn
    have hc := card_dvd_of_le hd.le_cartan
    rw [hd.card,c.left_card h.linear h.sylow_normalizes,hp5,hn] at hc
    norm_num at hc
  refine ⟨hC,hA5,hp5,hn2,?_⟩
  have hmove : I < conjugateSpanBy I (T : Subgroup G) :=
    lt_of_le_of_ne (le_conjugateSpanBy I _) (by
      intro he
      exact hm (he.symm ▸ le_normalizer_conjugateSpanBy I (T : Subgroup G)))
  have hmodel := Chapter1.Section02.MovedMaximality.moved_local_model h.qtke T hIlocal hmove
  have hb : R.subgroupOf X ∈ ChapterA.Section03.localCComponents (T.subtype hTX) :=
    ((Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,hRlocal⟩).1
  have hnotb : ¬ ClassificationModels.IsBenderModel (I ⧸ pCore 2 I) := by
    intro hbender
    let e := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hIX)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hIX))
    have he := Chapter1.Section02.MovedMaximality.eq_of_bender_quotient
      (T.subtype hTX) hb hI (subgroupOf_mono X hRI.le) (hbender.of_mulEquiv e)
    have he' := congrArg (map X.subtype) he
    rw [map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hIX] at he'
    exact hRI.ne he'
  cases hmodel with
  | linear_even f hf iso => exact (hnotb (.linear f hf iso)).elim
  | suzuki m hm iso => exact (hnotb (.suzuki m hm iso)).elim
  | linear_prime q hq ho iso => exact .inr ⟨q,hq,ho,iso⟩
  | janko iso => exact .inl iso

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

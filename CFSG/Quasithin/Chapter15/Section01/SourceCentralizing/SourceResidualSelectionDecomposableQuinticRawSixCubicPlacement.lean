module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCubicAction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawClassicalCore
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.Alternating.PrimeRank
public import Theory.GroupTheory.Commutator.NormalizesSupplement

/-!
# The original Sylow closure in the central A6 row

The actual central quotient A6 forces odd rank at least two in the full core:
rank at most one would make its Sylow three-subgroup cyclic, and its actual
quotient Sylow would then be cyclic. This uses no general rank comparison
through a cubic kernel. Original odd-rank control therefore makes the full
marked Sylow S normalize L; in particular the whole chosen module V does.

The original moving support W is S-normal. Its now-proved core-trivial action
makes O₂(L)W a normal two-subgroup of LS, placing W in the actual O₂(LS).
Original T-normality of Q₁ also makes V preserve the literal group LQ₁.
No claim that Q₁ is Sylow, that W centralizes L, or that the source distance
equals two is made.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem central_six_three_rank
    {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ center A) ≃* alternatingGroup (Fin 6)) : 2 ≤ primeRank 3 A := by
  by_contra! hr
  let P : Sylow 3 A := Classical.choice inferInstance
  have hh := P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega))
    (e.toMonoidHom.comp (QuotientGroup.mk' (center A)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 (by decide) (by decide)] at hh
  omega

omit [Finite G] in
private theorem prepared_module_le_sylow
    (T : Sylow 2 G) {M V : Subgroup G} (h : PreparedChosenModule T M V)
    (hTM : (T : Subgroup G) ≤ M) : V ≤ (T : Subgroup G) := by
  let := h.elementary
  let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
  let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
  have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal (T.subtype hTM)
  simpa only [map_subgroupOf_eq_of_le h.le_selected,Sylow.coe_subtype,
    map_subgroupOf_eq_of_le hTM] using map_mono (f := M.subtype) hh

/-- The actual full marked Sylow and the entire original chosen module
normalize the same local component, retaining either core center. -/
theorem PreparedChosenModule.raw_six_central_sylow_module_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hTM : (T : Subgroup G) ≤ M)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hLq : IsQuasisimple (L ⧸ pCore 2 L))
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃*
      alternatingGroup (Fin 6)) :
    ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (L : Set G) ∧
      V ≤ normalizer (L : Set G) := by
  let := h.elementary
  have hn := h.raw_local_normalizes_of_oddRank hG T hZ hZne hL hLq
    Nat.prime_three (by decide) (central_six_three_rank e)
  exact ⟨hn,(le_inf (prepared_module_le_sylow T h hTM)
    (V.le_centralizer.trans (centralizer_le (hZ.trans inf_le_left)))).trans hn⟩

private theorem normal_core_actor
    {A : Type*} [Group A] [Finite A] (L S W : Subgroup A) [L.Normal]
    (hgen : L ⊔ S = ⊤) (hW : IsPGroup 2 W)
    (hSW : S ≤ normalizer (W : Set A)) (hc : ⁅W,L⁆ ≤ L.pCoreIn 2) :
    W ≤ pCore 2 A := by
  let Q := L.pCoreIn 2
  let : Q.Normal := inferInstanceAs (((pCore 2 L).map L.subtype).Normal)
  have hLp : L ≤ normalizer ((W ⊔ Q : Subgroup A) : Set A) :=
    le_normalizer_sup_of_commutator_le W L W Q le_rfl hc
  have hSp : S ≤ normalizer ((W ⊔ Q : Subgroup A) : Set A) :=
    (le_inf hSW le_normalizer_of_normal).trans (normalizer_inf_normalizer_le_normalizer_sup W Q)
  have hp : (W ⊔ Q).Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hLp hSp))
  exact le_sup_left.trans (le_sSup ⟨hp,hW.to_sup_of_normal_right (isPGroup_pCoreIn 2 L)⟩)

private theorem core_actor_in_sylow_closure
    {L S W : Subgroup G} (hW : IsPGroup 2 W) (hWS : W ≤ S)
    (hSL : S ≤ normalizer (L : Set G)) (hSW : S ≤ normalizer (W : Set G))
    (hc : ⁅W,L⁆ ≤ L.pCoreIn 2) : W ≤ (L ⊔ S).pCoreIn 2 := by
  let J := L ⊔ S
  let L0 := L.subgroupOf J
  let S0 := S.subgroupOf J
  let W0 := W.subgroupOf J
  have hWJ : W ≤ J := hWS.trans le_sup_right
  let : L0.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hSL)
  have hgen : L0 ⊔ S0 = ⊤ := by
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left) (show S ≤ J from le_sup_right),
      subgroupOf_self]
  have hn : S0 ≤ normalizer (W0 : Set J) := by
    rw [←subgroupOf_normalizer_eq hWJ]
    exact fun _ hx => hSW hx
  have hcomm : ⁅W0,L0⁆ ≤ L0.pCoreIn 2 := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hWJ,
      map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left),
      map_pCoreIn_of_injective 2 _ _ J.subtype_injective,
      map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left)]
    exact hc
  have hh := map_mono (f := J.subtype)
    (normal_core_actor L0 S0 W0 hgen hW.comap_subtype hn hcomm)
  rwa [map_subgroupOf_eq_of_le hWJ] at hh

/-- In the original quintic source, the moving sixteen lies in the core of
the full Sylow closure LS, and the whole chosen module preserves LQ₁. -/
theorem PreparedChosenModule.decomposable_five_raw_six_cubic_placement
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
      let Q1 := (G1 ⊓ Mc).pCoreIn 2
      Z1 ≤ thompsonFixed T V → Z1 ≠ ⊥ →
      (T : Subgroup G) ≤ normalizer (Q1 : Set G) →
      ∀ {L : Subgroup G}, L ∈ Chapter1.LIn G1 S →
        R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G) →
        IsQuasisimple (L ⧸ pCore 2 L) →
        ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃* alternatingGroup (Fin 6) →
        ⁅V,R⁆ ≤ (L ⊔ S).pCoreIn 2 ∧ V ≤ normalizer ((L ⊔ Q1 : Subgroup G) : Set G) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive Z1 G1 C R S Q1 hZ hZne hTQ L hL hnL hLq e
  obtain ⟨hSL,hVL⟩ := h.raw_six_central_sylow_module_normalizes hG T hM.1.2 hZ hZne hL hLq e
  have hVT := prepared_module_le_sylow T h hM.1.2
  have hVS : V ≤ S := le_inf hVT
    (V.le_centralizer.trans (centralizer_le (hZ.trans inf_le_left)))
  have hWV : ⁅V,R⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp
    (((map_subtype_le _).trans inf_le_left).trans h.normalized)
  have hSR : S ≤ normalizer (R : Set G) :=
    (le_inf (inf_le_left.trans hM.1.2) inf_le_right).trans
      (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C)))
  have hSW : S ≤ normalizer ((⁅V,R⁆ : Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (h.normalized (hM.1.2 ht.1)),
      mem_normalizer_iff_map_conj_eq.mp (hSR ht)]
  have hc := h.decomposable_five_raw_six_moving_support_core hG T hempty hM hmany hJ hfull
    c d hd s π hp hs hdec hq hfive hnL hLq e
  exact ⟨core_actor_in_sylow_closure ((IsElementaryAbelian.isPGroup 2 V).to_le hWV)
      (hWV.trans hVS) hSL hSW hc,
    (le_inf hVL (hVT.trans hTQ)).trans (normalizer_inf_normalizer_le_normalizer_sup L Q1)⟩

end CFSG.Quasithin.Chapter15.Section01

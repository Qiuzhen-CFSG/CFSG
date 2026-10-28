module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictTransvections
public import CFSG.Quasithin.ChapterG.Section02.Binary.FourAction
public import Theory.GroupTheory.PResidual.FiniteLocalPair
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# The genuine binary local setup in the strict branch

The residual of the source-plane normalizer, the original point and plane,
and H = C_G(z) satisfy G.2.1. The natural layer action and the residual
centralization in LocalAnalysis make C_L(z) a two-group; consequently the
point stabilizer in LT is the original Sylow group T. This identifies the
kernel of the action on the four-group with the intrinsic two-core.

The source cubic and nonabelian closure supply automorphisms of orders
three and two. They give the full six-element action and the natural binary
coordinates required by G.2.3, without an additional module premise.
The G.2 closure is identified with the literal sourceClosure.

Source: Aschbacher--Smith, 6.2.17, printed pp.689--690, using G.2.1--3.
The crossing-module consumer is StrictBinaryModule. LocalAnalysis remains
with qt-d-1222-rankone-recognition-identification; the strict contradiction
remains with qt-d-1222-recognition-strict-elimination.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise TensorProduct
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

@[expose] def strictBinarySetup (T L R : Subgroup G) (z : G) : ChapterG.Section02.Setup G where
  V := ZS T L R
  V₁ := zpowers z
  L := strictCrossingResidual T L R
  T := T
  H := centralizer ({z} : Set G)

theorem strict_sourceClosure_eq_span
    (h611 : Hypothesis611 κ T L M R n) (hz : z ∈ ZS (T : Subgroup G) L R) :
    sourceClosure (T : Subgroup G) L R z =
      conjugateSpanBy (ZS (T : Subgroup G) L R) (centralizer ({z} : Set G)) := by
  have hSH : ZS (T : Subgroup G) L R ≤ centralizer ({z} : Set G) :=
    inf_le_left.trans (layer_le_involution_centralizer h611 hz)
  change (normalClosure ((ZS (T : Subgroup G) L R).subgroupOf (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G)))).map _ = _
  rw [normalClosure_subgroupOf_eq_conjugateSpanBy _ _ hSH,
    map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hSH)]

/-- The residual-centralization clause and faithful natural action make
C_L(z) a two-group. -/
theorem LocalAnalysis.strict_layer_point_centralizer_two
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n) :
    IsPGroup 2 (L ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  let J := L ⊓ centralizer ({z} : Set G)
  let Y := (pResidual 2 J).map J.subtype
  have hYQ : Y ≤ L.pCoreIn 2 := by
    rw [← natural_centralizer_eq_core hnatural.2.1]
    exact le_inf ((map_subtype_le _).trans inf_le_left)
      ((embedded_pResidual_mono 2 (show J ≤ centralizer ({z} : Set G) ⊓ M from
        le_inf inf_le_right (inf_le_left.trans h611.L_le))).trans A.residual_centralizes)
  have hpY : IsPGroup 2 Y := (L.isPGroup_pCoreIn 2).to_le hYQ
  have hperfect : IsPPerfect 2 Y := isPPerfect_embedded_pResidual 2 J
  have hb : (⊥ : Subgroup Y) = ⊤ := hperfect _ inferInstance
    (hpY.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective _))
  have hYbot : Y = ⊥ := by
    apply eq_bot_iff.mpr
    intro y hy
    exact congrArg Subtype.val (mem_bot.mp
      (show (⟨y,hy⟩ : Y) ∈ (⊥ : Subgroup Y) from hb.symm ▸ mem_top _))
  have hres : pResidual 2 J = ⊥ :=
    (map_eq_bot_iff_of_injective _ J.subtype_injective).mp hYbot
  exact (isPGroup_quotient_pResidual (G := J) 2).of_injective
    (QuotientGroup.mk' (pResidual 2 J)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk', hres])

/-- In LT the original point stabilizer is exactly the original Sylow group. -/
theorem LocalAnalysis.strict_point_stabilizer_in_join
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer ({z} : Set G) = T := by
  let H := centralizer ({z} : Set G)
  have hn : (T : Subgroup G) ≤ normalizer (L ⊓ H : Set G) :=
    (le_inf h611.sylow_normalizes_L (hTH.trans H.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hp : IsPGroup 2 ((L ⊓ H) ⊔ (T : Subgroup G) : Subgroup G) :=
    (A.strict_layer_point_centralizer_two h611 hnatural).to_sup_of_normal_left' T.isPGroup' hn
  have he : (L ⊓ H) ⊔ (T : Subgroup G) = T := T.is_maximal' hp le_sup_right
  apply le_antisymm ?_ (le_inf le_sup_right hTH)
  intro x hx
  have hm : x ∈ (L : Set G) * ((T : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L T h611.sylow_normalizes_L]
    exact hx.1
  obtain ⟨l, hl, t, ht, rfl⟩ := hm
  have hlH : l ∈ H := (H.mul_mem_cancel_right (hTH ht)).mp hx.2
  rw [← he]
  exact mul_mem (mem_sup_left ⟨hl, hlH⟩) (mem_sup_right ht)

/-- Genuine G.2.1 data for the residual of the source-plane normalizer. -/
theorem LocalAnalysis.strict_binary_hypothesis
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    (strictBinarySetup (T : Subgroup G) L R z).Hypothesis := by
  let S := ZS (T : Subgroup G) L R
  let N := L ⊓ normalizer (S : Set G)
  let D := strictBinarySetup (T : Subgroup G) L R z
  have hcardZ : Nat.card (zpowers z) = 2 := (Nat.card_zpowers z).trans horder
  have hG₁ : D.G₁ = centralizer ({z} : Set G) := by
    apply le_antisymm
    · exact (normalizer_le_centralizer_of_card_two _ hcardZ).trans (by
        intro x hx
        exact mem_centralizer_singleton_iff.mpr (hx z (mem_zpowers z)).symm)
    · exact (show centralizer ({z} : Set G) ≤ centralizer (zpowers z : Set G) from by
        apply le_centralizer_iff.mp
        apply zpowers_le.mpr
        intro x hx
        exact mem_centralizer_singleton_iff.mp hx).trans (Subgroup.centralizer_le_normalizer _)
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) :=
    (le_inf h611.sylow_normalizes_L
      (h611.sylow_normalizes_ZS.trans (normalizer (S : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hTL : D.T ≤ normalizer (D.L : Set G) := hTN.trans
    (normalizer_le_normalizer_characteristic_image N (pResidual 2 N))
  have hLN : D.L ≤ normalizer (S : Set G) := (map_subtype_le _).trans inf_le_right
  have hTlocal : D.T ≤ normalizer (D.V : Set G) := h611.sylow_normalizes_ZS
  have hpoint : D.V₁ ≤ D.V := zpowers_le.mpr hz
  have hi : (zpowers z).relIndex S = 2 := by
    have hc := ((zpowers z).subgroupOf S).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show zpowers z ≤ S from hpoint)).toEquiv, hcardZ,
      (h611.natural_ZS_geometry hnatural).2.1] at hc
    change 2 * (zpowers z).relIndex S = 4 at hc
    omega
  refine {
    elementary := h611.ZS_elementary
    point_ne_bot := by
      intro he
      change zpowers z = ⊥ at he
      rw [he, card_bot] at hcardZ
      omega
    point_le := hpoint
    residual := (pResidual_eq_top_iff 2 _).mpr (isPPerfect_embedded_pResidual 2 N)
    V_le_T := h611.ZS_le_T
    T_normalizes_point := by rw [hG₁]; exact hTH
    T_normalizes_V := hTlocal
    T_normalizes_L := hTL
    sylow_LT := ⟨T.subtype (show (T : Subgroup G) ≤ D.LT from le_sup_right), by
      change ((T.subtype (show (T : Subgroup G) ≤ D.LT from le_sup_right) : Sylow 2 D.LT) : Subgroup D.LT).map D.LT.subtype = (T : Subgroup G)
      rw [Sylow.coe_subtype]
      exact map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ D.LT from le_sup_right)⟩
    H_le := hG₁.symm.le
    local_le := sup_le ?_ hTH
    sylow_H := ⟨T.subtype hTH, by
      change ((T.subtype hTH : Sylow 2 (centralizer ({z} : Set G))) : Subgroup (centralizer ({z} : Set G))).map _ = (T : Subgroup G)
      simpa only [Sylow.coe_subtype, strictBinarySetup] using (map_subgroupOf_eq_of_le hTH)⟩
    characteristic_two := A.fitting_core
    local_normalizes_V := sup_le ?_ hTlocal
    quotient_nonzero := by
      intro he
      have hc := congrArg (fun K : Subgroup G => Nat.card K) he
      change Nat.card (zpowers z) = Nat.card S at hc
      rw [hcardZ, (h611.natural_ZS_geometry hnatural).2.1] at hc
      omega
    irreducible := ?_ }
  · exact ((map_subtype_le _).trans inf_le_right).trans hG₁.le
  · exact ((map_subtype_le _).trans inf_le_left).trans hLN
  · intro B hZB hBS _
    have hm := relIndex_mul_relIndex (zpowers z) B S hZB hBS
    rw [hi] at hm
    have hd : (zpowers z).relIndex B ∣ 2 := ⟨B.relIndex S, hm.symm⟩
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h | h
    · exact Or.inl (le_antisymm (relIndex_eq_one.mp h) hZB)
    · rw [h] at hm
      have hb : B.relIndex S = 1 := by omega
      exact Or.inr (le_antisymm hBS (relIndex_eq_one.mp hb))

/-- The actual residual orbit of the point is the original source plane. -/
theorem strict_binary_point_span
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2) :
    let D := strictBinarySetup (T : Subgroup G) L R z
    D.V = D.VL := by
  let D := strictBinarySetup (T : Subgroup G) L R z
  obtain ⟨d, hdres, _, _, hdZ, _, hdH⟩ := strict_exists_crossing_cubic h611 hnatural hz horder
  have hn : D.L ≤ normalizer (D.V : Set G) := (map_subtype_le _).trans inf_le_right
  apply le_antisymm ?_ (conjugateSpanBy_le (zpowers_le.mpr hz) hn)
  rw [strict_plane_eq_sup_crossing_lines h611 hnatural hz horder hdZ hdH]
  apply sup_le (le_conjugateSpanBy _ _)
  rintro x ⟨w, hw, rfl⟩
  exact subset_closure ⟨d⁻¹, D.L.inv_mem hdres, w, hw, rfl⟩

/-- The G.2 closure and its containment retain the original subgroup U. -/
theorem LocalAnalysis.strict_binary_closure
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let D := strictBinarySetup (T : Subgroup G) L R z
    D.U = sourceClosure (T : Subgroup G) L R z ∧ D.U ≤ D.T := by
  have he := strict_sourceClosure_eq_span h611 hz
  refine ⟨he.symm, ?_⟩
  change conjugateSpanBy (ZS (T : Subgroup G) L R) (centralizer ({z} : Set G)) ≤ (T : Subgroup G)
  rw [← he]
  have hh := pCoreIn_le_sylow (centralizer ({z} : Set G)) (T.subtype hTH)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at hh
  exact A.closure_le_core.trans hh

/-- The full action on the four-group has exactly the intrinsic two-core
as kernel; the original source cubic and Sylow group supply all six automorphisms. -/
theorem LocalAnalysis.strict_binary_action
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    let D := strictBinarySetup (T : Subgroup G) L R z
    ∃ hn : D.LT ≤ normalizer (D.V : Set G),
      Function.Surjective (D.V.normalizerMonoidHom.comp (inclusion hn)) ∧
      (D.V.normalizerMonoidHom.comp (inclusion hn)).ker = pCore 2 D.LT := by
  let D := strictBinarySetup (T : Subgroup G) L R z
  let S := D.V
  let J := D.LT
  have hs := A.strict_binary_hypothesis h611 hnatural hz horder hTH
  have hLN : D.L ≤ normalizer (S : Set G) := (map_subtype_le _).trans inf_le_right
  have hn : J ≤ normalizer (S : Set G) := sup_le hLN hs.T_normalizes_V
  let f : J →* MulAut S := S.normalizerMonoidHom.comp (inclusion hn)
  have hS : Nat.card S = 4 := (h611.natural_ZS_geometry hnatural).2.1
  let : IsElementaryAbelian 2 S := hs.elementary
  let : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hS]; decide)
  let : IsKleinFour S := ⟨hS, IsElementaryAbelian.exponent_eq_prime⟩
  have hk : f.ker = (centralizer (S : Set G)).subgroupOf J := by
    rw [← MonoidHom.comap_ker, normalizerMonoidHom_ker]
    rfl
  have hJL : J ≤ L ⊔ (T : Subgroup G) :=
    sup_le (((map_subtype_le _).trans inf_le_left).trans le_sup_left) le_sup_right
  have hJH : J ⊓ centralizer ({z} : Set G) ≤ (T : Subgroup G) :=
    (inf_le_inf_right _ hJL).trans (A.strict_point_stabilizer_in_join h611 hnatural hTH).le
  have hkerT : f.ker.map J.subtype ≤ (T : Subgroup G) := by
    rw [hk, subgroupOf_map_subtype]
    intro x hx
    exact hJH ⟨hx.2, mem_centralizer_singleton_iff.mpr (hx.1 z hz).symm⟩
  have hkerQ : f.ker ≤ pCore 2 J := by
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    exact (T.isPGroup'.to_le hkerT).of_equiv
      (f.ker.equivMapOfInjective J.subtype J.subtype_injective).symm
  have hQker : pCore 2 J ≤ f.ker := by
    let Q := J.pCoreIn 2
    have hQT : Q ≤ (T : Subgroup G) := by
      have hh := pCoreIn_le_sylow J (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
      rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] at hh
    have hQC : Q ≤ centralizer (zpowers z : Set G) := by
      apply le_centralizer_iff.mp
      apply zpowers_le.mpr
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hTH (hQT hx))
    have hLQ : D.L ≤ normalizer (Q : Set G) := le_sup_left.trans
      (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
    have hQS : Q ≤ centralizer (S : Set G) := by
      have hspan : S = D.VL := strict_binary_point_span h611 hnatural hz horder
      rw [hspan]
      exact le_centralizer_conjugateSpanBy_of_normalizes _ _ _ hLQ hQC
    rw [hk]
    intro q hq
    exact hQS (mem_map_of_mem J.subtype hq)
  have honto : Function.Surjective f := by
    obtain ⟨heU, hUT⟩ := A.strict_binary_closure h611 hz hTH
    have hnot : ¬ D.U ≤ centralizer (S : Set G) := by
      intro hc
      apply A.strict_closure_noncommutative h611 hnatural hz horder hstrict
      rw [← heU]
      exact (conjugateSpanBy_commutative_iff D.V D.H).mpr (le_centralizer_iff.mp hc)
    obtain ⟨u, hu, huc⟩ := SetLike.not_le_iff_exists.mp hnot
    let uj : J := ⟨u, mem_sup_right (hUT hu)⟩
    have hfu : f uj ≠ 1 := by
      intro hh
      have : uj ∈ f.ker := hh
      rw [hk] at this
      exact huc this
    have hu2 : f uj ^ 2 = 1 := by
      rw [← map_pow]
      apply (show uj ^ 2 ∈ f.ker ↔ f (uj ^ 2) = 1 from Iff.rfl).mp
      rw [hk]
      have hpU : IsPGroup 2 (sourceClosure (T : Subgroup G) L R z) :=
        ((centralizer ({z} : Set G)).isPGroup_pCoreIn 2).to_le A.closure_le_core
      let : Fact (IsPGroup 2 (sourceClosure (T : Subgroup G) L R z)) := ⟨hpU⟩
      have hc : u ^ 2 ∈ zpowers z :=
        (A.strict_closure_frattini_eq_line h611 hnatural hz horder hstrict).1.le
          (mem_map_of_mem _ (pth_power_mem_frattini_of_isPGroup (p := 2)
            (⟨u, heU.le hu⟩ : sourceClosure (T : Subgroup G) L R z)))
      exact (le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative S))
        (zpowers_le.mpr hz hc)
    let a : f.range := ⟨f uj, ⟨uj, rfl⟩⟩
    have ha : orderOf a = 2 := orderOf_eq_prime
      (Subtype.ext hu2) (fun hh => hfu (congrArg Subtype.val hh))
    obtain ⟨d, hdres, _, _, _, hd3, hdH⟩ := strict_exists_crossing_cubic h611 hnatural hz horder
    let dj : J := ⟨d, mem_sup_left hdres⟩
    let b : f.range := ⟨f dj, ⟨dj, rfl⟩⟩
    have hb : orderOf b = 3 := orderOf_eq_prime (by
        apply Subtype.ext
        change f dj ^ 3 = 1
        rw [← map_pow, show dj ^ 3 = 1 from Subtype.ext (hd3 ▸ pow_orderOf_eq_one d), map_one]) (by
      intro hh
      have hdk : dj ∈ f.ker := congrArg Subtype.val hh
      rw [hk] at hdk
      exact hdH (mem_centralizer_singleton_iff.mpr (hdk z hz).symm))
    have h2 : 2 ∣ Nat.card f.range := ha ▸ orderOf_dvd_natCard a
    have h3 : 3 ∣ Nat.card f.range := hb ▸ orderOf_dvd_natCard b
    have h6 : 6 ∣ Nat.card f.range := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3
    have hle : Nat.card f.range ≤ 6 := by
      simpa only [IsKleinFour.card_mulAut] using Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
    have heq : Nat.card f.range = 6 := le_antisymm hle (Nat.le_of_dvd Nat.card_pos h6)
    apply MonoidHom.range_eq_top.mp
    exact eq_top_of_card_eq _ (heq.trans (IsKleinFour.card_mulAut S).symm)
  exact ⟨hn, honto, le_antisymm hkerQ hQker⟩


/-- The natural C₃ coordinates required by G.2.3, with no extra action premise. -/
def LocalAnalysis.strict_binary_natural
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    (strictBinarySetup (T : Subgroup G) L R z).BinaryNaturalData := by
  apply Classical.choice
  let D := strictBinarySetup (T : Subgroup G) L R z
  have h := A.strict_binary_hypothesis h611 hnatural hz horder hTH
  have hLN : D.L ≤ normalizer (D.V : Set G) := (map_subtype_le _).trans inf_le_right
  obtain ⟨hn, hfull, hker⟩ := A.strict_binary_action h611 hnatural hz horder hTH hstrict
  have hres : (D.V.normalizerMonoidHom.comp (inclusion hLN)).range =
      pResidual 2 (MulAut D.V) := by
    let f := D.V.normalizerMonoidHom.comp (inclusion (sup_le hLN h.T_normalizes_V))
    have he : (pResidual 2 D.LT).map D.LT.subtype = D.L :=
      embedded_pResidual_join_pGroup D.L D.T
        ((pResidual_eq_top_iff 2 D.L).mp h.residual) T.isPGroup' h.T_normalizes_L
    have hr : pResidual 2 D.LT = D.L.subgroupOf D.LT := by
      apply map_injective D.LT.subtype_injective
      rw [he, map_subgroupOf_eq_of_le (show D.L ≤ D.LT from le_sup_left)]
    have hf : (D.L.subgroupOf D.LT).map f =
        (D.V.normalizerMonoidHom.comp (inclusion hLN)).range := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨⟨x, mem_sup_left x.property⟩, x.property, rfl⟩
    rw [← hf, ← hr]
    exact map_pResidual_of_surjective 2 f hfull
  obtain ⟨heU, hUT⟩ := A.strict_binary_closure h611 hz hTH
  have hnstar : D.star D.U ≠ ⊥ := by
    intro hb
    have hUL : D.U ≤ D.LT := hUT.trans le_sup_right
    have hk : D.U.subgroupOf D.LT ≤ pCore 2 D.LT := by
      have hm := (Subgroup.map_eq_bot_iff _).mp hb
      simpa only [QuotientGroup.ker_mk'] using hm
    have hUC : D.U ≤ centralizer (D.V : Set G) := by
      intro u hu
      have huQ := hk (show (⟨u, hUL hu⟩ : D.LT) ∈ D.U.subgroupOf D.LT from hu)
      rw [← hker, ← MonoidHom.comap_ker, normalizerMonoidHom_ker] at huQ
      exact huQ
    apply A.strict_closure_noncommutative h611 hnatural hz horder hstrict
    rw [← heU]
    exact (conjugateSpanBy_commutative_iff D.V D.H).mpr (le_centralizer_iff.mp hUC)
  exact ⟨ChapterG.Section02.Setup.binaryNaturalData_of_four_action h hLN
    (h611.natural_ZS_geometry hnatural).2.1 (strict_binary_point_span h611 hnatural hz horder)
    hfull hker hres ((Nat.card_zpowers z).trans horder) hnstar⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

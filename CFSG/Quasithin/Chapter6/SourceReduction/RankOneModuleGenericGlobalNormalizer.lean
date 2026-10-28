module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalCompletion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalCharacteristic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeNormalizer
public import CFSG.Quasithin.Chapter3.Section01.HStarResidualNormalizer
public import Theory.GroupTheory.SylowNormalizerFrattini
public import CFSG.Quasithin.Chapter5.Section03GreenExtension

/-!
# The actual normalizer geometry before generic completion recognition

For K = O²(H), source 5.2.7 supplies a common Sylow
R = T ∩ L = T ∩ K and the equalities O₂(GᵢT) = O₂(Lᵢ).
The nonexceptional branch of 5.2.8 supplies K ∈ L*. From these inputs,
we prove N_G(R) = N_G(L) ∩ N_G(K), both actual product decompositions,
and the corresponding normalizer-core equalities. The original uniqueness
over L kills the two-core of the join of the full normalizers.

The left containment uses the proved original rank-one normalizer bound.
For the right containment, the genuine common-normal theorem 3.1.1 gives
a common maximal local overgroup; source 1.2.7 identifies it with N_G(K).
Frattini's argument gives the products, and the original rank-one Borel
maximality gives the exact intersection. Characteristic two then completes
the intrinsic local conditions needed in 5.3.2.

The degree-two unitary case is retained: R need not be the original
S = O₂(N_G(L) ∩ H), and the core hypotheses concern GᵢT, not H or KS.
The common-Sylow and core identities, right maximality, exhaustive F.1.12
comparison, and ambient completion recognition remain source obligations.
This module proves neither DGS Theorem A nor GlobalExit.
Source: Aschbacher–Smith 5.2.7–8 and 5.3.1–2, printed pp.651–653,658–659
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizer_core_eq_of_sylow_overgroup {T : Sylow 2 G} {J Y : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) (hYN : Y ≤ normalizer (J : Set G))
    (hc : Y.pCoreIn 2 = J.pCoreIn 2) :
    (normalizer (J : Set G)).pCoreIn 2 = J.pCoreIn 2 := by
  apply le_antisymm
  · exact hc ▸ Chapter3.twoCore_le_of_sylow_le T hTY hYN
  · exact pCoreIn_mono_of_normalizes J.le_normalizer le_rfl

private theorem normalizer_product_of_sylow {J R : Subgroup G}
    (P : Sylow 2 J) (hP : (P : Subgroup J).map J.subtype = R)
    (hN : normalizer (R : Set G) ≤ normalizer (J : Set G)) :
    ∀ x ∈ normalizer (J : Set G), ∃ l ∈ J, ∃ b ∈ normalizer (R : Set G), x = l * b := by
  have hf := le_normalizer_sylow_sup J (normalizer (J : Set G)) J.le_normalizer le_rfl P
  rw [hP, sup_comm] at hf
  intro x hx
  have hm : x ∈ (J : Set G) * (normalizer (R : Set G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left J _ hN]
    exact hf hx
  obtain ⟨l,hl,b,hb,he⟩ := hm
  exact ⟨l,hl,b,hb,he.symm⟩

/-- Source 5.3.1's intersection, core and product calculations for the actual
normalizers. The preceding common-Sylow, GᵢT-core and right-maximality
conclusions remain explicit; R need not equal the original sourceS. -/
theorem Preparation.normalizer_geometry
    {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hRL : R = (T : Subgroup G) ⊓ L)
    (hRK : R = (T : Subgroup G) ⊓ residual H)
    (hc : ∀ i : Fin 2,
      (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊔ (T : Subgroup G)).pCoreIn 2 =
        (![L,residual H] i).pCoreIn 2) :
    normalizer (L : Set G) ≠ normalizer (residual H : Set G) ∧
    normalizer (R : Set G) = normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
    (normalizer (L : Set G)).pCoreIn 2 = L.pCoreIn 2 ∧
    (normalizer (residual H : Set G)).pCoreIn 2 = (residual H).pCoreIn 2 ∧
    (∀ x ∈ normalizer (L : Set G), ∃ l ∈ L, ∃ b ∈ normalizer (R : Set G), x = l * b) ∧
    (∀ x ∈ normalizer (residual H : Set G), ∃ k ∈ residual H,
      ∃ b ∈ normalizer (R : Set G), x = k * b) ∧
    pCore 2 (normalizer (L : Set G) ⊔ normalizer (residual H : Set G) : Subgroup G) = ⊥ := by
  have hTK := hH.1.1.2.trans (le_normalizer_residual H)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    rw [hRL]
    exact (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
      inf_normalizer_le_normalizer_inf
  have hNL : normalizer (R : Set G) ≤ normalizer (L : Set G) :=
    h.normalizer_le_of_sylow_normalizes (hRL ▸ inf_le_left) hRL.ge hTR
  obtain ⟨P,hP⟩ := exists_sylow_component h.sylow_normalizes
  have hPR : (P : Subgroup L).map L.subtype = R := hP.trans hRL.symm
  obtain ⟨Q,hQ⟩ := exists_sylow_component hTK
  have hQR : (Q : Subgroup (residual H)).map (residual H).subtype = R := hQ.trans hRK.symm
  have hRne : R ≠ ⊥ := by
    intro he
    have hp := ((d.hypothesisF11 h hH.1.1.2).rankOneBorelFacts 0).proper
    change ChapterF.Source.borel L (sourceS L H) < L at hp
    rw [d.left_borel_eq,localBorel,← hRL,he,normalizer_eq_top,inf_top_eq] at hp
    exact hp.false
  have ho : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTK)
      (le_componentOrbit _ _)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK
  have hmax := hu.normalizer_maximal
  have huniq := hu.normalizer_unique
  rw [ho] at hmax huniq
  have hNK : normalizer (R : Set G) ≤ normalizer (residual H : Set G) := by
    have hs : Chapter1.IsSylowIn 2 R (residual H ⊔ R) := by
      rw [sup_eq_left.mpr (hRK ▸ inf_le_right)]
      exact ⟨Q,hQR⟩
    obtain ⟨M,hM,hNM⟩ := Chapter3.HStar.normalizer_residual_sylow_common_overgroup h.qtke T
      h.sylow_normalizes hH R hRne (hRL ▸ inf_le_left) hTR hs
    have he := huniq M hM (by rw [residual_sup_sylow T H hH.1.1.2]; exact le_sup_right.trans hNM)
    exact he ▸ le_sup_left.trans hNM
  have hdiff : normalizer (L : Set G) ≠ normalizer (residual H : Set G) := by
    intro he
    exact d.right_outside (he ▸ (residual H).le_normalizer)
  have hLout : ¬ L ≤ normalizer (residual H : Set G) := by
    intro he
    exact hdiff (d.unique_left _ hmax he).symm
  have hprodL := normalizer_product_of_sylow P hPR hNL
  have hprodK := normalizer_product_of_sylow Q hQR hNK
  have hIL : L ⊓ normalizer (residual H : Set G) < L :=
    lt_of_le_of_ne inf_le_left (fun he => hLout (he ▸ inf_le_right))
  have hIB : L ⊓ normalizer (residual H : Set G) ≤ localBorel T L := by
    rw [← d.left_borel_eq]
    apply ((d.hypothesisF11 h hH.1.1.2).rankOneBorelFacts 0).unique_maximal
    · change sourceS L H ⊓ L ≤ L ⊓ normalizer (residual H : Set G)
      rw [d.left_intersection]
      exact le_inf inf_le_right (inf_le_left.trans hTK)
    · exact hIL
  have hi : normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ≤
      normalizer (R : Set G) := by
    intro x hx
    obtain ⟨l,hl,b,hb,rfl⟩ := hprodL x hx.1
    have hlK : l ∈ normalizer (residual H : Set G) := by
      have hm := (normalizer (residual H : Set G)).mul_mem hx.2
        ((normalizer (residual H : Set G)).inv_mem (hNK hb))
      simpa only [mul_inv_cancel_right] using hm
    have hlR : l ∈ normalizer (R : Set G) := by
      rw [hRL]
      exact (hIB ⟨hl,hlK⟩).2
    exact (normalizer (R : Set G)).mul_mem hlR hb
  refine ⟨hdiff,le_antisymm (le_inf hNL hNK) hi,
    normalizer_core_eq_of_sylow_overgroup le_sup_right ?_ (hc 0),
    normalizer_core_eq_of_sylow_overgroup le_sup_right ?_ (hc 1),hprodL,hprodK,?_⟩
  · exact sup_le
      ((normal_subgroupOf_iff_le_normalizer
        (show L ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 from
          le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 0))
      h.sylow_normalizes
  · exact sup_le
      ((normal_subgroupOf_iff_le_normalizer
        (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
          le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1)) hTK
  · by_contra hc
    obtain ⟨X,hX,hgen⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot _ hc
    have he := d.unique_left X hX (L.le_normalizer.trans (le_sup_left.trans hgen))
    exact d.right_outside (he ▸ (residual H).le_normalizer.trans (le_sup_right.trans hgen))

/-- The whole ambient normalizers and their literal intersection. -/
@[expose] def normalizerAmalgam (L K : Subgroup G) :
    Chapter5.Section03GreenExtension.LocalAmalgam G where
  M₁ := normalizer (L : Set G)
  M₂ := normalizer (K : Set G)
  M₁₂ := normalizer (L : Set G) ⊓ normalizer (K : Set G)
  middle_left := inf_le_left
  middle_right := inf_le_right

/-- Discharge the intrinsic local conditions used in 5.3.2 on the actual
normalizer pair. This does not assert a DGS recognition theorem. -/
theorem Preparation.normalizer_local_conditions
    {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hRL : R = (T : Subgroup G) ⊓ L)
    (hRK : R = (T : Subgroup G) ⊓ residual H)
    (hc : ∀ i : Fin 2,
      (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊔ (T : Subgroup G)).pCoreIn 2 =
        (![L,residual H] i).pCoreIn 2) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L (residual H)) L (residual H) R := by
  obtain ⟨_,hm,hcL,hcK,hpL,hpK,hfree⟩ := d.normalizer_geometry h hH hK hRL hRK hc
  refine ⟨rfl,L.le_normalizer,(residual H).le_normalizer,hfree,?_,?_,hcL,hcK,?_,?_,hm⟩
  · exact characteristic_two_of_sourceS_left h hH.1.1.2 le_rfl
      ((sourceS_le_sylow h.sylow_normalizes hH.1.1.2).trans h.sylow_normalizes)
  · exact characteristic_two_of_sourceS_right h hH le_rfl
      ((sourceS_le_sylow h.sylow_normalizes hH.1.1.2).trans
        (hH.1.1.2.trans (le_normalizer_residual H)))
  · change ∀ x ∈ normalizer (L : Set G), ∃ l ∈ L,
      ∃ b ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G), x = l * b
    rw [← hm]
    exact hpL
  · change ∀ x ∈ normalizer (residual H : Set G), ∃ k ∈ residual H,
      ∃ b ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G), x = k * b
    rw [← hm]
    exact hpK

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.FullDisplacementDomain
public import Theory.SpecificGroups.Janko4.Model.TwentyThreeTwoSubgroups

/-!
# Closing the inner Mathieu pushing-up branches

Retain R = O₂(J), the full original J₄ covering component K, and the
intersection residual F. In the M₂₃/M₂₄ rows the literal central quotient
of F has order divisible by 23. Its image in K/Z(K) retains this divisor,
since the covering kernel is a two-group. That image normalizes both the
image of R intersect K and the original module image.

The native prime-23 calculation identifies these two images. Pulling back
through the same quotient and inclusion gives R intersect K = V Z(K),
including the full covering center. The previously proved full-domain
involution argument contradicts this identity once LT = L O₂(LT), which
is already proved in both inner Mathieu rows.

The literal Hall consumer consequently retains only the M₁₂/M₂₂ pushing-up
alternatives and the separate odd-normalizer branch. Those alternatives,
the M₂₄ fixed-line and odd-actor comparisons, and final Hall faithfulness
remain open; no placement or factorization premise is added to the consumer.

Source: Aschbacher--Smith 4.2.13, printed p.612, applied in 4.4.14,
printed pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- In the inner Mathieu rows the entire original component factor is
V times the embedded covering center, using the literal quotient maps. -/
theorem sourceOrbit_pushingUp_inner_mathieu_component_factor
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M23) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M24))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    J.pCoreIn 2 ⊓ K.map H.subtype = V ⊔ (center K).map (H.subtype.comp K.subtype) := by
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  let j := H.subtype.comp K.subtype
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hjr : j.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  let Fk := F.comap j
  let E := V.comap j
  let U := R.comap j
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hqker : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hc := hw.2.2.2.2.2.2.1
  let := hK.2
  have hZp : IsPGroup 2 (center K) := by
    rw [IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)]
    exact pCore_isPGroup
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK := hc.ordinary_component_contains_original K hK
  let a : Fk ≃* F := (subgroupOfEquivOfLe hFK).trans (subgroupOfEquivOfLe hFH)
  let b := QuotientGroup.congr (pCore 2 Fk) (pCore 2 F) a (pCore_map_iso 2 a)
  obtain ⟨ef,_⟩ := hw.2.2.2.2.2.2.2.2.2.2.2.1
  let em := (centerQuotientCongr (b.trans ef)).trans (D.orbitCentralQuotientEquiv h)
  let f := q.comp Fk.subtype
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.ker.subgroupOf Fk)
    rw [hqker]
    exact hZp.comap_subtype
  have h23q : 23 ∣ Nat.card ((Fk ⧸ pCore 2 Fk) ⧸ center (Fk ⧸ pCore 2 Fk)) := by
    rcases hm with e23 | e24
    · rw [Nat.card_congr (em.trans e23.some).toEquiv,Sporadic.Mathieu.m23_order]; decide
    · rw [Nat.card_congr (em.trans e24.some).toEquiv,Sporadic.Mathieu.m24_order]; decide
  have h23F : 23 ∣ Nat.card Fk := h23q.trans
    ((card_quotient_dvd_card _).trans (card_quotient_dvd_card _))
  have h23 : 23 ∣ Nat.card f.range := by
    have hcount : Nat.card f.ker * Nat.card f.range = Nat.card Fk := by
      rw [←index_ker]
      exact f.ker.card_mul_index
    obtain ⟨n,he⟩ := hk.exists_card_eq
    have hcop : Nat.Coprime 23 (Nat.card f.ker) := by
      rw [he]
      exact (by decide : Nat.Coprime 23 2).pow_right n
    exact hcop.dvd_of_dvd_mul_left (hcount.symm ▸ h23F)
  have hFR : F ≤ normalizer (R : Set G) :=
    (le_conjugateSpanBy F (H ⊓ normalizer (L : Set G))).trans hc.span_normalizes_radical
  have hFV : F ≤ normalizer (V : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans D.normalizes
  have hnU : f.range ≤ normalizer (U.map q : Set Janko4.Model) := by
    rw [MonoidHom.range_comp,range_subtype]
    exact (map_mono ((comap_mono hFR).trans (R.le_normalizer_comap j))).trans
      (U.le_normalizer_map q)
  have hnE : f.range ≤ normalizer (E.map q : Set Janko4.Model) := by
    rw [MonoidHom.range_comp,range_subtype]
    exact (map_mono ((comap_mono hFV).trans (V.le_normalizer_comap j))).trans
      (E.le_normalizer_map q)
  let := D.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
    (j.subgroupComap V) (fun x y hh => Subtype.ext (hj (congrArg (fun z : V => (z : G)) hh)))
  let : IsElementaryAbelian 2 (E.map q) := IsElementaryAbelian.map q
  have hv := D.sourceOrbit_pushingUp_module_disjoint_central_factor hfix hw K hK
  have hVK : V ≤ j.range := hv.1.trans inf_le_right |>.trans_eq hjr.symm
  have hne : E.map q ≠ ⊥ := by
    intro hb
    apply D.ne_bot
    apply bot_unique
    intro v hvm
    obtain ⟨k,rfl⟩ := hVK hvm
    have hkE : k ∈ E := hvm
    have hkc : k ∈ center K := by
      rw [←hqker]
      exact ((Subgroup.map_eq_bot_iff E).mp hb) hkE
    apply hv.2.le
    refine ⟨hvm,hv.1 hvm |>.1,?_⟩
    rintro y ⟨y,hy,rfl⟩
    exact congrArg j (mem_center_iff.mp hkc ⟨y,hy⟩)
  have he : E.map q = U.map q := Janko4.twentyThree_elementary_eq_normalized_twoGroup f.range
    (U.map q) (E.map q) h23 (((isPGroup_pCoreIn 2 J).comap_of_injective j hj).map q)
    hne (map_mono (comap_mono hw.2.2.2.2.2.1)) hnU hnE
  have hf := sourceOrbit_pushingUp_core_central_product hw K hK e
  have hZ : q.ker ≤ U := by
    rw [hqker]
    intro z hz
    exact (hf.2.2.symm.le.trans inf_le_left).trans inf_le_left (mem_map_of_mem j hz)
  have hp := congrArg (comap q) he
  rw [comap_map_eq,comap_map_eq,sup_eq_left.mpr hZ,hqker] at hp
  have hmap := congrArg (map j) hp
  rw [Subgroup.map_sup,map_comap_eq_self hVK,map_comap_eq,hjr] at hmap
  exact (inf_comm _ _).trans hmap.symm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The full-domain involution contradiction excludes both inner Mathieu
rows of the original pushing-up configuration. -/
theorem sourceOrbit_no_inner_mathieu_pushingUp_factor_gap
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M23) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M24))
    {A : Subgroup G} (hc : MathieuPushingUpFactorGap T L V A) : False := by
  obtain ⟨J,H,W,hw,K,hK,hn,hout,hFK,e,x,r,hx,hfull,hgap⟩ := hc
  have hf := D.sourceOrbit_pushingUp_inner_mathieu_component_factor h hfix hm hw K hK e
  have hj := D.sourceOrbit_mathieu_inner_localJoin h hm
  have hh := hgap ((show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right).trans_eq hj)
  rw [hf] at hh
  exact hh.false

/-- Every remaining pushing-up witness has M12 or M22 central quotient. -/
theorem sourceOrbit_pushingUp_factor_gap_small_mathieu
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    {A : Subgroup G} (hc : MathieuPushingUpFactorGap T L V A) :
    Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22) := by
  rcases hm with h12 | h22 | h23 | h24
  · exact .inl h12
  · exact .inr h22
  · exact (D.sourceOrbit_no_inner_mathieu_pushingUp_factor_gap h hfix (.inl h23) hc).elim
  · exact (D.sourceOrbit_no_inner_mathieu_pushingUp_factor_gap h hfix (.inr h24) hc).elim
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The M23 and M24 pushing-up alternatives are now excluded with their full
covering centers retained. Only the original M12/M22 pushing-up alternatives
and the separate odd-normalizer comparison remain. -/
theorem sourceOrbit_mathieu_hall_small_pushingUp
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (((Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
          Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22)) ∧
          MathieuPushingUpFactoredCase T L V A ∧ MathieuPushingUpFactorGap T L V A) ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_factor_gap G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.2.imp fun p hp => hp.imp fun A => ?_
  iterate 11 apply And.imp_right
  exact Or.imp (fun hc => ⟨D.sourceOrbit_pushingUp_factor_gap_small_mathieu
    h.toHypothesis1221 (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1 hm hc.2,hc⟩) id
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

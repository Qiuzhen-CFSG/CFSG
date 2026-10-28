module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SmallFinite
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.Mathieu.M23.Properties.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ThreeRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.GroupTheory.PrimeRankCoprimeIndex
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.SpecificGroups.SL2.BinaryOddRank

/-!
# Field-four embeddings in four sporadic quotient carriers

The order formulas for M₂₂, M₂₃ and HS restrict a nonbinary PSL₂ section
modulo its own two-core to degrees two and three. Degree three would give
that section index prime to three, hence cubic rank at least two, whereas
binary SL₂ has cyclic odd Sylow subgroups. For 3.M₂₂ the central quotient
preserves the perfect smaller group's simple two-core quotient, so the same
argument applies. In particular, the smaller two-core is never discarded.

The resulting actual model alternatives apply at both flag normalizers and
at every source subspace U ≤ V₁ with its original Sylow condition. The
preceding quotient markings belong to qt-d-1222-natural-flag-cartan, with
final discharge in qt-d-1222-natural-local-geometry. The relative-components
owner retains refinement and the remaining source-family assembly.

Source: Aschbacher--Smith A.3.12 and 11.1.1, printed pp.47--48,761,
combined manuscript of 1 March 2004. The imported concrete carriers retain
their existing source attribution and licenses.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

private theorem no_eight_section (B : Subgroup G)
    (h27 : ¬ 27 ∣ Nat.card G) (hr : 2 ≤ primeRank 3 G)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^3)) : False := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9B : 9 ∣ Nat.card B := by
    have hd := card_quotient_dvd_card (pCore 2 B)
    rw [binary_card hm] at hd
    exact (by decide : 9 ∣ 2^3 * ((2^3)^2-1)).trans hd
  have hi : ¬ 3 ∣ B.index := by
    intro h
    apply h27
    rw [←B.card_mul_index]
    exact Nat.mul_dvd_mul h9B h
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  let a := e.trans (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F).symm
  have hle : primeRank 3 B ≤ 1 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
      primeRank_congr 3 a]
    exact Matrix.SL2.binary_odd_primeRank_le_one (by decide)
  rw [B.primeRank_eq_of_not_dvd_index hi] at hle
  omega

private theorem small_sporadic_parameter (B : Subgroup G) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hc : Nat.card G = 443520 ∨ Nat.card G = 10200960 ∨ Nat.card G = 44352000)
    (hr : 2 ≤ primeRank 3 G) : n = 2 := by
  have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
  rw [binary_card hm] at hd
  have hp : 2^n ∣ Nat.card G := (dvd_mul_right _ _).trans hd
  have hb : n < 10 := by
    by_contra! h
    have h1024 : 1024 ∣ Nat.card G := (show 1024 ∣ 2^n from pow_dvd_pow 2 h).trans hp
    rcases hc with hc | hc | hc <;> rw [hc] at h1024 <;> norm_num at h1024
  have hn23 : n = 2 ∨ n = 3 := by
    interval_cases n <;> norm_num at hn ⊢ <;>
      rcases hc with hc | hc | hc <;> norm_num [hc] at hd
  rcases hn23 with h | rfl
  · exact h
  · exact (no_eight_section B (by rcases hc with hc | hc | hc <;> rw [hc] <;> decide) hr hm).elim

open Chapter1.Section02.LocalModels

private theorem mathieu_twenty_three_three_rank : 2 ≤ primeRank 3 Sporadic.Mathieu.M23 := by
  exact Sporadic.Mathieu.m22_primeRank_three.ge.trans
    ((primeRank_equiv 3 Sporadic.Mathieu.m23EquivM22PointStabilizer).le.trans
      (primeRank_subgroup_le 3 _))

@[expose] def SmallSporadicCarrier (A : Type*) [Group A] : Prop :=
  Nonempty (A ≃* Sporadic.Mathieu.M22) ∨ IsM22Cover A ∨
    Nonempty (A ≃* Sporadic.Mathieu.M23) ∨
    Nonempty (A ≃* Sporadic.LeechRelated.HS.Carrier)

private theorem small_sporadic_section (B : Subgroup G) [Group.IsPerfect B]
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hmodel : SmallSporadicCarrier G) : n = 2 := by
  rcases hmodel with h | h | h | h
  · obtain ⟨e⟩ := h
    exact small_sporadic_parameter B hn hm
      (.inl ((Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m22_order))
      (by rw [primeRank_congr 3 e,Sporadic.Mathieu.m22_primeRank_three])
  · obtain ⟨_,_,⟨e⟩⟩ := h
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
    have hker : q.ker = center G := by
      ext x
      change e (QuotientGroup.mk' (center G) x) = 1 ↔ x ∈ center G
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff x
    let : Group.IsSolvable q.ker := hker ▸ (inferInstance : Group.IsSolvable (center G))
    have hs : IsSimpleGroup (B ⧸ pCore 2 B) := by
      obtain ⟨F,_,_,hF,⟨d⟩⟩ := hm
      let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
        rw [hF]
        exact (show (4 : ℕ) = 2^2 from rfl).le.trans
          (Nat.pow_le_pow_right (by decide) hn))
      exact d.isSimpleGroup
    let := hs
    let f := q.subgroupMap B
    let : Group.IsSolvable f.ker := by
      change Group.IsSolvable (q.subgroupMap B).ker
      rw [ker_subgroupMap]
      exact Group.isSolvable_of_isSolvable_injective
        (f := B.subtype.subgroupComap q.ker) (fun a b he => Subtype.ext (Subtype.ext
          (congrArg (fun x : q.ker => (x : G)) he)))
    let d := PerfectCoreTwoExtension.solvableKernelQuotientEquiv f (q.subgroupMap_surjective B)
    exact small_sporadic_parameter (B.map q) hn (hm.of_mulEquiv d.symm)
      (.inl Sporadic.Mathieu.m22_order) Sporadic.Mathieu.m22_primeRank_three.ge
  · obtain ⟨e⟩ := h
    exact small_sporadic_parameter B hn hm
      (.inr (.inl ((Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m23_order)))
      (by rw [primeRank_congr 3 e]; exact mathieu_twenty_three_three_rank)
  · obtain ⟨e⟩ := h
    exact small_sporadic_parameter B hn hm
      (.inr (.inr ((Nat.card_congr e.toEquiv).trans
        Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier)))
      (by rw [primeRank_congr 3 e]; exact Sporadic.LeechRelated.HS.ThreeRank.two_le_primeRank)

/-- The original perfect binary section in these four quotient carriers
forces field four, preserving its smaller two-core. -/
theorem small_sporadic_parameters {B K : Subgroup G} [Group.IsPerfect B]
    (hBK : B ≤ K) {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : SmallSporadicCarrier (K ⧸ pCore 2 K)) : n = 2 := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let D := B.subgroupOf K
  let C := D.map q
  have hk : IsPGroup 2 (q.subgroupMap D).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let d := subgroupOfEquivOfLe hBK
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := d.symm.toMonoidHom) d.symm.surjective
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := q.subgroupMap D) (q.subgroupMap_surjective D)
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  let a := (q.subgroupMap D).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective D) hk
  exact small_sporadic_section C hn (hsmall.of_mulEquiv (a.symm.trans dq)) hmodel

/-- All four actual isomorphism alternatives of 11.1.1, including 3.M₂₂. -/
theorem component_alternative_of_small_sporadic {B K : Subgroup G} [Group.IsPerfect B]
    (hBK : B ≤ K) {n : ℕ} (hn : 1 < n)
    (hsmall : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hmodel : SmallSporadicCarrier (K ⧸ pCore 2 K)) : ComponentAlternative B K n := by
  apply ComponentAlternative.four (small_sporadic_parameters hBK hn hsmall hmodel)
  rcases hmodel with h | h | h | h
  · exact .m22 h
  · exact .m22Cover h
  · exact .m23 h
  · exact .hs h

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Both source flag-normalizer applications retain their literal residuals. -/
theorem flag_component_alternative_of_small_sporadic (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (_hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hmodel : SmallSporadicCarrier (K ⧸ pCore 2 K)) :
    ComponentAlternative (f.Li i) K S.field.degree := by
  let : Group.IsPerfect (f.Li i) := localResidual_perfect _
  exact component_alternative_of_small_sporadic hLK S.nonbinary hm hmodel

/-- The arbitrary-subspace source application keeps the original full Sylow
condition; the stronger section argument only needs the supplied containment. -/
theorem subspace_component_alternative_of_small_sporadic
    (U : Subgroup G) (_hU : U ≠ ⊥) (_hUV : U ≤ f.Vi 0)
    (_hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (_hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) (hmodel : SmallSporadicCarrier (K ⧸ pCore 2 K)) :
    ComponentAlternative (f.Li 0) K S.field.degree := by
  let : Group.IsPerfect (f.Li 0) := localResidual_perfect _
  exact component_alternative_of_small_sporadic hLK S.nonbinary hm hmodel
end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding

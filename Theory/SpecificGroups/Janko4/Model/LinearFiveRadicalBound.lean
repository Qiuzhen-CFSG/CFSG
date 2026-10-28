module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import Theory.GroupAction.SubgroupConjugation
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
/-!
# The binary size bound for a PSL₅(2) section in J₄

The section contributes a factor 2¹⁰ to the index of each normalized
binary subgroup. The original ATLAS carrier has two-part 2²¹, so such
a subgroup has order at most 2¹¹. Order 2¹¹ is impossible: the
section supplies an element of order 31, and its fixed subgroup would
contain an involution, contradicting both actual involution-centralizer
orders. Hence the bound is 2¹⁰. The actual homomorphism and its
binary kernel remain explicit; no Sylow placement is assumed.

Source application: Aschbacher--Smith 4.2.13, printed p.612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4
attribute [local irreducible] modelGroup matrixA matrixB

private theorem five_two_part :
    2 ^ 10 ∣ Nat.card Representation.SL5TenDimensional.Group := by
  rw [Nat.card_congr Representation.SL5TenDimensional.projectiveEquiv.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
  have he : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
    calc
      _ = ∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ)) := by
        simpa only [Nat.card_zmod,Nat.reduceSub,Nat.gcd_one_right,mul_one] using hc
      _ = 9999360 := by decide
  rw [he]
  decide

/-- A binary subgroup normalized by an actual PSL₅(2) section has order
at most 2048 in J₄. The homomorphism retains its binary covering kernel. -/
theorem linearFive_normalized_twoGroup_card_le
    {F : Type*} [Group F] [Finite F]
    (f : F →* Model) (hk : IsPGroup 2 f.ker)
    (e : (F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group)
    (U : Subgroup Model) (hU : IsPGroup 2 U)
    (hn : f.range ≤ normalizer (U : Set Model)) : Nat.card U ≤ 2048 := by
  let B := U.comap f
  have hBn : B.Normal := by
    refine ⟨?_⟩
    intro b hb a
    change f (a*b*a⁻¹) ∈ U
    simpa only [map_mul,map_inv] using
      (mem_normalizer_iff.mp (hn (show f a ∈ f.range from ⟨a,rfl⟩)) (f b)).mp hb
  let := hBn
  have hBP : B ≤ pCore 2 F := le_sSup ⟨hBn,hU.comap_of_ker_isPGroup f hk⟩
  have hi : 2 ^ 10 ∣ U.relIndex f.range := by
    rw [←index_comap]
    have hd : 2 ^ 10 ∣ (pCore 2 F).index := by
      change 2 ^ 10 ∣ Nat.card (F ⧸ pCore 2 F)
      rw [Nat.card_congr e.toEquiv]
      exact five_two_part
    exact hd.trans (index_dvd_of_le hBP)
  have hjoin : U.relIndex (f.range ⊔ U) = U.relIndex f.range := by
    let N := f.range ⊔ U
    let : (U.subgroupOf N).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le hn U.le_normalizer)
    have hh := relIndex_sup_right (f.range.subgroupOf N) (U.subgroupOf N)
    rw [←subgroupOf_sup le_sup_left le_sup_right,
      relIndex_subgroupOf le_rfl,relIndex_subgroupOf le_sup_left] at hh
    exact hh
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup Model) U (f.range ⊔ U) bot_le le_sup_right
  simp only [relIndex_bot_left,hjoin] at hcount
  have hd : Nat.card U * 2 ^ 10 ∣ Nat.card Model := by
    apply (show Nat.card U * 2^10 ∣ Nat.card (f.range ⊔ U : Subgroup Model) from ?_).trans
      (card_subgroup_dvd_card _)
    rw [←hcount]
    exact Nat.mul_dvd_mul_left _ hi
  obtain ⟨n,hnc⟩ := hU.exists_card_eq
  rw [hnc,←pow_add] at hd
  have hb : n ≤ 11 := by
    by_contra hh
    have h22 : 2 ^ 22 ∣ Nat.card Model :=
      (pow_dvd_pow 2 (by omega : 22 ≤ n + 10)).trans hd
    rw [Cardinality.model_card] at h22
    norm_num at h22
  rw [hnc]
  exact (Nat.pow_le_pow_right (by decide) hb).trans_eq (by decide : 2^11 = 2048)

private theorem involution_centralizer_not_thirtyOne (z : Model) (hz : orderOf z = 2) :
    ¬31 ∣ Nat.card (centralizer ({z} : Set Model)) := by
  rcases InvolutionCentralizers.centralizer_equiv_first_or_second z hz with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv,OuterReduction.OddIndex.modelCentralizer_card]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv,InvolutionCentralizers.Second.ambient_card]
    decide

/-- The factor 31 in the literal section rules out a normalized binary
subgroup of order 2048, because its fixed subgroup would contain an involution. -/
theorem normalized_twoGroup_card_ne_2048 (B U : Subgroup Model)
    (hB : 31 ∣ Nat.card B) (hU : IsPGroup 2 U)
    (hn : B ≤ normalizer (U : Set Model)) : Nat.card U ≠ 2048 := by
  intro hcard
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 31 hB
  let X := zpowers (b : Model)
  have hX : IsPGroup 31 X := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,Subgroup.orderOf_coe,hb,pow_one])
  have hXU : X ≤ normalizer (U : Set Model) := zpowers_le.mpr (hn b.property)
  let _ := conjMulDistribMulActionOfLeNormalizer X U hXU
  let C := FixedPoints.subgroup X U
  have hm := hX.card_modEq_card_fixedPoints U
  change Nat.card U % 31 = Nat.card C % 31 at hm
  have hne : Nat.card C ≠ 1 := by
    intro he
    rw [hcard,he] at hm
    norm_num at hm
  have hd : 2 ∣ Nat.card C := (hU.to_subgroup C).card_eq_or_dvd.resolve_left hne
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hd
  have hz' : orderOf ((z : U) : Model) = 2 :=
    (orderOf_coe (z : U)).trans ((orderOf_coe z).trans hz)
  have hbC : (b : Model) ∈ centralizer ({((z : U) : Model)} : Set Model) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg U.subtype (z.property (⟨b,mem_zpowers (b : Model)⟩ : X))
    change (b : Model) * z.val.val * (b : Model)⁻¹ = z.val.val at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  apply involution_centralizer_not_thirtyOne z.val.val hz'
  have ho : orderOf (⟨b,hbC⟩ : centralizer ({z.val.val} : Set Model)) = 31 :=
    (orderOf_coe _).symm.trans ((orderOf_coe b).trans hb)
  exact ho ▸ orderOf_dvd_natCard (⟨b,hbC⟩ : centralizer ({z.val.val} : Set Model))

/-- The actual PSL₅(2) section bounds the normalized binary subgroup by
1024: the only larger possible order is excluded by its element of order 31. -/
theorem linearFive_normalized_twoGroup_card_le_1024
    {F : Type*} [Group F] [Finite F]
    (f : F →* Model) (hk : IsPGroup 2 f.ker)
    (e : (F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group)
    (U : Subgroup Model) (hU : IsPGroup 2 U)
    (hn : f.range ≤ normalizer (U : Set Model)) : Nat.card U ≤ 1024 := by
  have hb := linearFive_normalized_twoGroup_card_le f hk e U hU hn
  have hdF : 31 ∣ Nat.card F := by
    apply (show 31 ∣ Nat.card (F ⧸ pCore 2 F) from ?_).trans (card_quotient_dvd_card _)
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr Representation.SL5TenDimensional.projectiveEquiv.toEquiv]
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
    have he : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
      calc
        _ = ∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ)) := by
          simpa only [Nat.card_zmod,Nat.reduceSub,Nat.gcd_one_right,mul_one] using hc
        _ = 9999360 := by decide
    rw [he]
    decide
  have hd : 31 ∣ Nat.card f.range := by
    have hcount : Nat.card f.ker * Nat.card f.range = Nat.card F := by
      rw [←index_ker]
      exact f.ker.card_mul_index
    obtain ⟨n,he⟩ := hk.exists_card_eq
    have hc : Nat.Coprime 31 (Nat.card f.ker) := by
      rw [he]
      exact (by decide : Nat.Coprime 31 2).pow_right n
    exact hc.dvd_of_dvd_mul_left (hcount.symm ▸ hdF)
  have hne := normalized_twoGroup_card_ne_2048 f.range U hd hU hn
  obtain ⟨n,he⟩ := hU.exists_card_eq
  have hn11 : n ≤ 11 := by
    rw [he] at hb
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  have hn10 : n ≤ 10 := by
    have hne11 : n ≠ 11 := fun hh => hne (by rw [he,hh]; decide)
    omega
  rw [he]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hn10

end Janko4

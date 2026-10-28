module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.SmallModels.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.CoreThree
public import Theory.GroupTheory.PCoreRestriction
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The PSL₃(3) Sylow-complement action obstruction

A permutable pair of a Sylow two-subgroup S and a complement R of order nine
or 27 generates a subgroup H of order 144 or 432. The concrete subgroup cover
places H in a full parabolic of order 432, whose three-core has order nine.

When R is elementary of order nine, H meets the parabolic three-core
nontrivially, so O₃(H) is nontrivial. It lies in the Sylow three-subgroup R.
If the pair is not reducible, invariance forces O₃(H) = R and hence S
normalizes R. Every involution centralizer is GL₂(3), of order 48, so no
involution centralizes R. Thus C_S(R) = 1, and the actual induced automizer
has order |S| = 16.

When R is extraspecial of order 27, H is a full parabolic. Its three-core
has order nine and lies in R. It is proper in R and is not contained in
Φ(R) ≤ Z(R), giving a nonzero proper invariant subgroup of R/Φ(R).
All cores and normality statements are relative to H; the action in the
second alternative is induced by N_S(R).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Proposition 1.3.4, printed pp.509–511, and the small-model exclusions
in the proof of 15.4.20, printed p.1164. The concrete parabolic cover
and core computations are proved in `Theory.SpecificGroups.PSL3Three`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.SmallModels
open Chapter1 Chapter1.XiEmbedding Chapter1.XiEmbedding.InvariantThree
open Matrix.PSL3Three

private theorem sylow_card (S : Sylow 2 PSL) : Nat.card S = 16 := by
  rw [S.card_eq_multiplicity, card_PSL, show 5616 = 2 ^ 4 * 351 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 351)]
  norm_num

private theorem pair_card (S : Sylow 2 PSL) (R : Subgroup PSL)
    (hR : XiOddQuotient 3 R)
    (hp : (R : Set PSL) * (S : Set PSL) = (S : Set PSL) * (R : Set PSL)) :
    Nat.card ↥(R ⊔ (S : Subgroup PSL)) = Nat.card R * 16 := by
  have hd : Disjoint R (S : Subgroup PSL) :=
    hR.isPGroup.disjoint_of_coprime S.isPGroup' (by decide)
  have hc := card_set_mul_mul_card_inf R (S : Subgroup PSL)
  rwa [← coe_sup_of_set_mul_comm R (S : Subgroup PSL) hp,
    hd.eq_bot, card_bot, mul_one, sylow_card] at hc

private theorem core_card_congr {G K : Type*} [Group G] [Group K] (e : G ≃* K) :
    Nat.card (pCore 3 G) = Nat.card (pCore 3 K) := by
  rw [← pCore_map_iso 3 e, card_map_of_injective e.injective]

private theorem parabolic_overgroup (H : Subgroup PSL) (hH : Nat.card H = 144) :
    ∃ M : Subgroup PSL, H ≤ M ∧ Nat.card M = 432 ∧ Nat.card (pCore 3 M) = 9 := by
  have hproper : H ≠ ⊤ := by
    intro he
    rw [he, card_top, card_PSL] at hH
    norm_num at hH
  obtain ⟨g, hg⟩ := proper_subgroup_le_conjugate_PSL H hproper
  have close (K : Subgroup PSL) (hK : Nat.card K = 432)
      (hc : Nat.card (pCore 3 K) = 9)
      (hle : H ≤ K.map (MulAut.conj g).toMonoidHom) :
      ∃ M : Subgroup PSL, H ≤ M ∧ Nat.card M = 432 ∧ Nat.card (pCore 3 M) = 9 := by
    refine ⟨K.map (MulAut.conj g).toMonoidHom, hle, ?_, ?_⟩
    · rwa [card_map_of_injective (MulAut.conj g).injective]
    · exact (core_card_congr ((MulAut.conj g).subgroupMap K)).symm.trans hc
  rcases hg with hh | hh | hh | hh
  · exact close _ card_lineStabilizer
      (card_threeCore_lineStabilizer card_lineStabilizer) hh
  · exact close _ card_planeStabilizer
      (card_threeCore_planeStabilizer card_planeStabilizer) hh
  · have hd := card_dvd_of_le hh
    rw [hH, card_map_of_injective (MulAut.conj g).injective, card_monomial] at hd
    norm_num at hd
  · have hd := card_dvd_of_le hh
    rw [hH, card_map_of_injective (MulAut.conj g).injective, card_singerNormalizer] at hd
    norm_num at hd

private theorem local_core_ne_bot (H : Subgroup PSL) (hH : Nat.card H = 144) :
    H.pCoreIn 3 ≠ ⊥ := by
  obtain ⟨M, hHM, hM, hMc⟩ := parabolic_overgroup H hH
  let U := M.pCoreIn 3
  have hU : Nat.card U = 9 :=
    (card_map_of_injective M.subtype_injective).trans hMc
  intro hc
  have hi : H ⊓ U = ⊥ := bot_unique (hc ▸ inf_pCoreIn_le_of_le 3 hHM)
  have hprod := card_set_mul_mul_card_inf H U
  rw [hi, card_bot, mul_one, hH, hU] at hprod
  have hle : (H : Set PSL) * (U : Set PSL) ⊆ (M : Set PSL) := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact M.mul_mem (hHM hx) (M.pCoreIn_le 3 hy)
  have hb := Nat.card_le_card_of_injective (Set.inclusion hle) (Set.inclusion_injective hle)
  change Nat.card ((H : Set PSL) * (U : Set PSL)) ≤ Nat.card M at hb
  rw [hprod, hM] at hb
  omega

private theorem normalizes_of_nine_of_not_reducible
    (S : Sylow 2 PSL) (R : Subgroup PSL) [IsElementaryAbelian 3 R]
    (hR : Nat.card R = 9)
    (hH : Nat.card ↥(R ⊔ (S : Subgroup PSL)) = 144)
    (hn : ¬ PairReducible (S : Subgroup PSL) R) : (S : Subgroup PSL) ≤ normalizer R := by
  let H := R ⊔ (S : Subgroup PSL)
  have hRH : R ≤ H := le_sup_left
  have hRc : Nat.card (R.subgroupOf H) = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv).trans hR
  let P : Sylow 3 H := Sylow.ofCard (R.subgroupOf H) (by
    rw [hRc, show Nat.card H = 144 from hH, show 144 = 3 ^ 2 * 16 by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 16)]
    norm_num)
  have hle : H.pCoreIn 3 ≤ R := by
    simpa only [P, Sylow.coe_ofCard, map_subgroupOf_eq_of_le hRH] using H.pCoreIn_le_sylow P
  have hne := local_core_ne_bot H hH
  have hi : ¬ (H.pCoreIn 3).subgroupOf R ≤ frattini R := by
    let _ : Fact (IsPGroup 3 R) := ⟨IsPGroup.of_card (p := 3) (n := 2) hR⟩
    rw [frattini_eq_bot_of_isElementaryAbelian (R := R) (p := 3), le_bot_iff]
    intro he
    have hh := congrArg (fun A : Subgroup R => A.map R.subtype) he
    rw [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at hh
    exact hne hh
  have ht : (H.pCoreIn 3).subgroupOf R = ⊤ := by
    by_contra hh
    exact hn (OddClassical.reducible_of_local_core_intersection _ _ 3 hi hh)
  have he : H.pCoreIn 3 = R := by
    have hh := congrArg (fun A : Subgroup R => A.map R.subtype) ht
    simpa only [map_subgroupOf_eq_of_le hle, ← MonoidHom.range_eq_map, range_subtype] using hh
  rw [← he]
  exact (le_sup_right.trans H.le_normalizer).trans
    (normalizer_le_normalizer_characteristic_image H (pCore 3 H))

private theorem centralizer_intersection_eq_bot (S : Sylow 2 PSL) (R : Subgroup PSL)
    (hR : Nat.card R = 9) : (S : Subgroup PSL) ⊓ centralizer (R : Set PSL) = ⊥ := by
  let C := (S : Subgroup PSL) ⊓ centralizer (R : Set PSL)
  have hC : IsPGroup 2 C := S.isPGroup'.to_le inf_le_left
  rcases hC.card_eq_or_dvd with hc | hc
  · exact card_eq_one.mp hc
  · obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hc
    let z' : SL := equiv.symm (z : PSL)
    have hz' : orderOf z' = 2 :=
      (orderOf_injective equiv.symm.toMonoidHom equiv.symm.injective (z : PSL)).trans
        ((orderOf_injective C.subtype C.subtype_injective z).trans hz)
    let Z := centralizer ({z'} : Set SL)
    have hZ : Nat.card Z = 48 := by
      rw [Nat.card_congr (Matrix.SL3.involutionCentralizerEquiv
        (ZMod 3) z' hz' (by decide)).toEquiv, Matrix.card_GL_field]
      norm_num [Fin.prod_univ_two]
    let f : R →* Z := (equiv.symm.toMonoidHom.comp R.subtype).codRestrict Z (by
      intro r
      apply mem_centralizer_singleton_iff.mpr
      change equiv.symm (r : PSL) * equiv.symm (z : PSL) =
        equiv.symm (z : PSL) * equiv.symm (r : PSL)
      rw [← map_mul, ← map_mul]
      exact congrArg equiv.symm (mem_centralizer_iff.mp z.property.2 r r.property))
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact equiv.symm.injective (congrArg Subtype.val hxy)
    have hd := card_dvd_of_injective f hf
    rw [hR, hZ] at hd
    norm_num at hd

private theorem automizer_card_of_normalizes (S : Sylow 2 PSL) (R : Subgroup PSL)
    (hR : Nat.card R = 9) (hn : (S : Subgroup PSL) ≤ normalizer R) :
    Nat.card (automizer (S : Subgroup PSL) R) = 16 := by
  let f := R.normalizerMonoidHom.comp
    (inclusion (show (S : Subgroup PSL) ⊓ normalizer R ≤ normalizer R from inf_le_right))
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hc : (x : PSL) ∈ centralizer (R : Set PSL) := by
      have hk : inclusion (show (S : Subgroup PSL) ⊓ normalizer R ≤ normalizer R
          from inf_le_right) x ∈ R.normalizerMonoidHom.ker := hx
      rw [normalizerMonoidHom_ker] at hk
      exact hk
    have he : (x : PSL) ∈ (⊥ : Subgroup PSL) :=
      centralizer_intersection_eq_bot S R hR ▸ ⟨x.property.1, hc⟩
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp he))
  change Nat.card f.range = 16
  rw [show Nat.card f.range = Nat.card ((S : Subgroup PSL) ⊓ normalizer R : Subgroup PSL)
      from Nat.card_range_of_injective hf,
    inf_eq_left.mpr hn]
  exact sylow_card S

private theorem extraspecial_reducible (S : Sylow 2 PSL) (R : Subgroup PSL)
    (he : IsExtraspecial 3 R) (hR : Nat.card R = 27)
    (hH : Nat.card ↥(R ⊔ (S : Subgroup PSL)) = 432) :
    PairReducible (S : Subgroup PSL) R := by
  have hA : Nat.card (((R ⊔ (S : Subgroup PSL)).pCoreIn 3).subgroupOf R) = 9 := by
    rw [OddClassical.LinearThree.CoreThree.local_core_intersection_card hR hH]
    exact threeCore_card_of_card_eq_432_of_parabolic_calculations
      card_lineStabilizer card_planeStabilizer card_monomial card_singerNormalizer
      (card_threeCore_lineStabilizer card_lineStabilizer)
      (card_threeCore_planeStabilizer card_planeStabilizer) _ hH
  let _ := he
  let _ := IsExtraspecial.quotient_elementary_abelian 3 R
  let _ : Fact (IsPGroup 3 (R ⧸ center R)) :=
    ⟨(IsPGroup.of_card (p := 3) (n := 3) hR).to_quotient _⟩
  have hphi : frattini R ≤ center R := by
    have hh := frattini_le_comap_frattini_of_surjective
      (QuotientGroup.mk'_surjective (center R))
    rw [frattini_eq_bot_of_isElementaryAbelian (R := R ⧸ center R) (p := 3)] at hh
    simpa using hh
  apply OddClassical.reducible_of_local_core_intersection (S : Subgroup PSL) R 3
  · intro ha
    have hd := card_dvd_of_le (ha.trans hphi)
    rw [hA, IsExtraspecial.center_order_p 3 R] at hd
    norm_num at hd
  · intro ha
    rw [ha, Nat.card_congr (Subgroup.topEquiv).toEquiv, hR] at hA
    omega

/-- Every permutable PSL₃(3) Sylow pair is reducible or has a Sylow-induced
automizer of order divisible by sixteen. Both odd-complement cases are retained. -/
theorem linearThree_restriction : Restriction Matrix.PSL3Three.PSL := by
  classical
  intro S R hR hp
  have hH := pair_card S R hR hp
  rcases hR with ⟨he, hc⟩ | ⟨he, hc, _⟩
  · let _ := he
    change Nat.card R = 9 at hc
    by_cases hr : PairReducible (S : Subgroup PSL) R
    · exact Or.inl hr
    · right
      have hH' : Nat.card ↥(R ⊔ (S : Subgroup PSL)) = 144 := by simpa only [hc] using hH
      rw [automizer_card_of_normalizes S R hc
        (normalizes_of_nine_of_not_reducible S R hc hH' hr)]
  · left
    change Nat.card R = 27 at hc
    exact extraspecial_reducible S R he hc (by simpa only [hc] using hH)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.SmallModels

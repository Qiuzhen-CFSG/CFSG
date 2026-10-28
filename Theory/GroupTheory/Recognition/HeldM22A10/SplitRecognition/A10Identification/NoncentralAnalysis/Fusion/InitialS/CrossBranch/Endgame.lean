module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.Tables
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.WeakClosureOvergroups

/-!
# The centralizer enlargement at the end of Held 2.9

If S is weakly closed in the displayed Sylow subgroup and its normalizer is a
two-group, mu cannot be conjugate to tau*lambda. The latter involution has a
local centralizer of order 32, whereas the local mu-centralizer has order 64.
Fusion would supply an order-64 subgroup of its ambient centralizer containing
S. Weak closure puts this subgroup in N_G(S), and Sylow maximality then puts
it in the displayed Sylow, contradicting the local order 32.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240, Lemma 2.9,
printed p.230, DOI 10.1215/ijm/1256053756.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

private theorem tauLambda_isConj_lambda : IsConj lam (tau * lam) := by
  have h := elementaryWord_isConj 3 (0, 0, 1, 0)
  have hl : localRepresentative (elementaryClass 3 (0, 0, 1, 0)) = lam := by decide +kernel
  have hw : elementaryWord 3 (0, 0, 1, 0) = tau * lam := by decide +kernel
  rwa [hl, hw] at h

private theorem tauLambda_centralizer_card :
    Nat.card (centralizer ({tau * lam} : Set H)) = 32 := by
  rw [← card_centralizer_eq_of_isConj _ _ tauLambda_isConj_lambda]
  exact involution_centralizer_cards.2.2.2.1

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

omit [Finite G] in
private theorem local_centralizer_map (x : H) :
    (centralizer ({x} : Set H)).map (D.a10ModelEmbedding e) =
      D.centralizer ⊓ centralizer ({D.a10ModelEmbedding e x} : Set G) := by
  let f := D.a10ModelEmbedding e
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(e.symm a).property, mem_centralizer_singleton_iff.mpr ?_⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp ha)
  · rintro ⟨hy, hc⟩
    have hyr : y ∈ f.range := by rwa [D.a10ModelEmbedding_range e]
    obtain ⟨a, rfl⟩ := hyr
    refine ⟨a, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using mem_centralizer_singleton_iff.mp hc

/-- The first alternative forced by the order-five action on L2 is impossible
once the contrary S-fusion hypotheses have made S weakly closed with a
two-group normalizer. -/
public theorem mu_tauLambda_nonfusion_of_weak_closure
    (htwo : IsPGroup 2 (normalizer (ambientElementary D e 1 : Set G)))
    (hweak : ∀ g : G,
      (ambientElementary D e 1).map (MulAut.conj g).toMonoidHom ≤ ambientSylow D e →
      (ambientElementary D e 1).map (MulAut.conj g).toMonoidHom = ambientElementary D e 1) :
    ¬ IsConj (D.a10NoncentralInvolution e) (D.a10ModelEmbedding e (tau * lam)) := by
  intro hfusion
  let C := centralizer ({D.a10ModelEmbedding e (tau * lam)} : Set G)
  let S := ambientElementary D e 1
  have hSC : S ≤ C := by
    have hm : tau * lam ∈ modelS :=
      mul_mem (elementaryGenerators_mem 1 2) (elementaryGenerators_mem 1 3)
    rintro y ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    let := elementary_isElementaryAbelian 1
    simpa only [map_mul] using
      congrArg (D.a10ModelEmbedding e) (setLike_mul_comm hx hm)
  have hd : 2 ^ 6 ∣ Nat.card C := by
    change 2 ^ 6 ∣ Nat.card (centralizer ({D.a10ModelEmbedding e (tau * lam)} : Set G))
    rw [← card_centralizer_eq_of_isConj _ _ hfusion]
    have h := card_dvd_of_le
      (show D.centralizer ⊓ centralizer ({D.a10NoncentralInvolution e} : Set G) ≤
        centralizer ({D.a10NoncentralInvolution e} : Set G) from inf_le_right)
    rw [ambient_intersection_card D e] at h
    exact h
  have hS : Nat.card (S.subgroupOf C) = 2 ^ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSC).toEquiv, ambientElementary_card]
    decide
  obtain ⟨P, hP, hSP⟩ := Sylow.exists_subgroup_card_pow_prime_le 2 hd
    (S.subgroupOf C) hS (show 4 ≤ 6 by decide)
  let R := P.map C.subtype
  have hR : Nat.card R = 64 := by
    rw [card_map_of_injective C.subtype_injective, hP]
    norm_num
  have hSR : S ≤ R := by
    rw [← map_subgroupOf_eq_of_le hSC]
    exact map_mono hSP
  have hRC : R ≤ C := map_subtype_le _
  have hRN : R ≤ normalizer (S : Set G) :=
    le_normalizer_of_isPGroup_of_weakly_closed (ambientSylow D e) S R hweak
      (IsPGroup.of_card (n := 6) hR) hSR
  have hND : normalizer (S : Set G) = ambientD D e :=
    (ambientSylow D e).is_maximal' htwo (ambientSylow_le_normalizer_S D e)
  have hRH : R ≤ D.centralizer := by
    have hRD : R ≤ ambientD D e := hND ▸ hRN
    refine hRD.trans ?_
    rw [← D.a10ModelEmbedding_range e]
    exact map_le_range _ _
  have hlocal := card_le_of_le (le_inf hRH hRC)
  rw [← local_centralizer_map, card_map_of_injective (D.a10ModelEmbedding_injective e),
    tauLambda_centralizer_card, hR] at hlocal
  omega

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion

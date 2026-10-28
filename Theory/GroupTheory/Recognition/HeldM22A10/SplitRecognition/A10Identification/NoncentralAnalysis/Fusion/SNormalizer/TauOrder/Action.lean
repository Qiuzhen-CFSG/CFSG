module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.SNormalizer.TauOrder.Geometry
public import Theory.ElementaryAbelian.AutomorphismLinearModelEight
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups

/-!
# The faithful action in Held's tau case

The S-normalizer acts on U=<pi,mu,tau> with kernel S. Its action image
therefore has order eight times the pi orbit size. The order-eight elementary
group is linearized over F2, giving an actual inclusion of the action image
in PSL3(2). A proper subgroup containing a Sylow two-subgroup lies in one of
the two order-24 parabolics. This is the small linear-group step used in
Held, Illinois J. Math. 13 (1969), Lemma 2.6, p.228.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- Restriction of actual conjugation to the invariant eight-group. -/
@[expose] public noncomputable def tauNormalizerAction
    (h : normalizer (ambientElementary D e 1 : Set G) ≤ normalizer (tauFusionSpace D e : Set G)) :
    LambdaSeparation.sNormalizer D e →* MulAut (tauFusionSpace D e) :=
  (tauFusionSpace D e).normalizerMonoidHom.comp (Subgroup.inclusion h)

/-- The kernel is S relative to its normalizer. -/
public theorem tauNormalizerAction_ker
    (h : normalizer (ambientElementary D e 1 : Set G) ≤ normalizer (tauFusionSpace D e : Set G)) :
    (tauNormalizerAction D e h).ker =
      (ambientElementary D e 1).subgroupOf (LambdaSeparation.sNormalizer D e) := by
  ext g
  change (tauFusionSpace D e).normalizerMonoidHom (Subgroup.inclusion h g) = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker, tauFusionSpace_centralizer]
  rfl

/-- The quotient by S is its faithful conjugation image on U. -/
public noncomputable def tauNormalizerQuotientEquivAction
    (h : normalizer (ambientElementary D e 1 : Set G) ≤ normalizer (tauFusionSpace D e : Set G)) :
    LambdaSeparation.sNormalizerQuotient D e ≃* (tauNormalizerAction D e h).range :=
  (QuotientGroup.quotientMulEquivOfEq (tauNormalizerAction_ker D e h).symm).trans
    (QuotientGroup.quotientKerEquivRange _)

public theorem tauNormalizerAction_card
    (h : normalizer (ambientElementary D e 1 : Set G) ≤ normalizer (tauFusionSpace D e : Set G)) :
    Nat.card (tauNormalizerAction D e h).range =
      8 * (MulAction.orbit (LambdaSeparation.sNormalizer D e) (LambdaSeparation.piPoint D e)).ncard := by
  rw [← Nat.card_congr (tauNormalizerQuotientEquivAction D e h).toEquiv]
  exact LambdaSeparation.quotient_card D e

private theorem psl_sylow_overgroup_card_dvd (K : Subgroup Matrix.PSL3Two.PSL)
    (h8 : 8 ∣ Nat.card K) (hproper : K ≠ ⊤) : Nat.card K ∣ 24 := by
  obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime (G := K) 2 (n := 3) h8
  let P := T.map K.subtype
  have hP : Nat.card P = 8 := by
    rw [card_map_of_injective K.subtype_injective, hT]
    norm_num
  let S : Sylow 2 Matrix.PSL3Two.PSL := Sylow.ofCard P (by
    rw [hP, Matrix.PSL3Two.card_PSL]
    decide +kernel)
  have hSK : (S : Subgroup Matrix.PSL3Two.PSL) ≤ K := map_subtype_le _
  obtain ⟨J, hJ, hKJ⟩ := (eq_top_or_exists_le_coatom K).resolve_left hproper
  obtain ⟨A, B, _, _, _, _, hA, hB, hmax⟩ := Matrix.PSL3Two.sylow_parabolics S
  rcases (hmax J hJ).mp (hSK.trans hKJ) with rfl | rfl
  · exact hA ▸ card_dvd_of_le hKJ
  · exact hB ▸ card_dvd_of_le hKJ

/-- An action on U, with the pi orbit bounded by seven, has order dividing 24. -/
public theorem tauNormalizerAction_card_dvd
    (h : normalizer (ambientElementary D e 1 : Set G) ≤ normalizer (tauFusionSpace D e : Set G))
    (horbit : (MulAction.orbit (LambdaSeparation.sNormalizer D e)
      (LambdaSeparation.piPoint D e)).ncard ≤ 7) :
    Nat.card (tauNormalizerAction D e h).range ∣ 24 := by
  let := tauFusionSpace_isElementaryAbelian D e
  obtain ⟨a⟩ := elementaryEight_mulAut_equiv_GL (tauFusionSpace D e) (tauFusionSpace_card D e)
  let b := a.trans (Matrix.PSL3Two.equivGL.symm.trans Matrix.PSL3Two.equiv)
  let K := (tauNormalizerAction D e h).range.map b.toMonoidHom
  have hc : Nat.card K = Nat.card (tauNormalizerAction D e h).range :=
    card_map_of_injective b.injective
  have h8 : 8 ∣ Nat.card K := by rw [hc, tauNormalizerAction_card]; exact dvd_mul_right _ _
  have hproper : K ≠ ⊤ := by
    intro htop
    have hh : Nat.card (tauNormalizerAction D e h).range ≤ 56 := by
      rw [tauNormalizerAction_card]
      omega
    rw [← hc, htop, card_top, Matrix.PSL3Two.card_PSL] at hh
    omega
  rw [← hc]
  exact psl_sylow_overgroup_card_dvd K h8 hproper

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion

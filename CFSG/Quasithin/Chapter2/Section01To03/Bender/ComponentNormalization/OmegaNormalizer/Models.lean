module
public import Theory.GroupTheory.SylowCenterAction
public import CFSG.Quasithin.ClassificationModels.Families
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction.Center
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.LinearAction.Geometry
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.SpecificGroups.Suzuki.InvolutionFusion
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.InnerAction.Models

/-!
# The complete Bender-model omega normalizer action

For binary PSL₂, PSU₃ and Suzuki groups, the first omega of a Sylow
subgroup is its elementary abelian center, of order at least four.
Concrete involution fusion gives the linear and Suzuki normalizer orbits;
inverse-norm torus scalars give the unitary orbit. The unique proper Sylow
overgroup theorem identifies N(Ω₁(P)) with N(P). Cyclic complements cover
the linear and Suzuki actions, while the existing unitary center-action
equivalence retains the full norm-one kernel and has image of order q−1.
Actual model equivalences, Hermitian basis changes and Sylow conjugacy are
used throughout. Component perfectness and concrete simplicity give a
trivial center without an additional recognition premise.

Source: Aschbacher--Smith, Proposition 2.2.2, printed pp.519--520,
using the rank-one facts of F.1.3(1), pp.259--260, and E.6.8(1), pp.247--248.
-/

public section
open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter2.BenderFusion.OmegaNormalizerModels
open SylowCenterAction
open ChapterF.Source
open ChapterE.Section06.Components.LieSieve.RankOne
variable {K : Type*} [Group K] [Finite K]

private theorem four_le {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  (by norm_num : 4 = 2 ^ 2) ▸ Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn

omit [Finite K] in
private theorem simple (hmodel : ClassificationModels.IsBenderModel K) : IsSimpleGroup K := by
  cases hmodel with
  | linear n hn h =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) (hF ▸ four_le hn)
    exact e.isSimpleGroup
  | unitary n hn h =>
    obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := h
    have hf := Unitary.fixed_card J n (by omega) hF hconj
    let := BenderSuzuki.External.huppert_II_10_13 J (2 ^ n)
      (by have := four_le hn; omega) hF hf
    exact e.isSimpleGroup
  | suzuki m hm h =>
    obtain ⟨e⟩ := h
    let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
    exact e.isSimpleGroup

omit [Finite K] in
private theorem rankOne (hmodel : ClassificationModels.IsBenderModel K) : IsRankOneModel K := by
  cases hmodel with
  | linear n hn h => exact .linear n (by omega) h
  | unitary n hn h => exact .projective_unitary n (by omega) h
  | suzuki m _ h => exact .suzuki m h

omit [Finite K] in
private theorem omega_centralizes (P : Sylow 2 K)
    (hc : omegaOneAmbient (P : Subgroup K) = (center P).map (P : Subgroup K).subtype) :
    omegaOneAmbient (P : Subgroup K) ≤ centralizer (P : Set K) := by
  rw [hc]
  rintro _ ⟨z, hz, rfl⟩
  exact mem_centralizer_iff.mpr fun x hx =>
    congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩)

omit [Finite K] in
private theorem normalizer_omega [IsSimpleGroup K] (hmodel : IsRankOneModel K)
    (P : Sylow 2 K)
    (hc : omegaOneAmbient (P : Subgroup K) = (center P).map (P : Subgroup K).subtype)
    (hsize : 2 < Nat.card (omegaOneAmbient (P : Subgroup K))) :
    normalizer (omegaOneAmbient (P : Subgroup K) : Set K) = normalizer (P : Set K) := by
  have hQ : omegaOneAmbient (P : Subgroup K) ≠ ⊥ := by
    intro he
    rw [he, Nat.card_eq_fintype_card] at hsize
    simp at hsize
  have hn : normalizer (P : Set K) ≤ normalizer (omegaOneAmbient (P : Subgroup K) : Set K) := by
    rw [hc]
    exact normalizer_le_normalizer_characteristic_image (P : Subgroup K) (center P)
  have hr := hmodel.rankOneSylowFacts P
  exact normalizer_eq_of_unique_maximal P _ hQ (omegaOneAmbient_le _) hn hr.proper hr.unique_maximal

omit [Finite K] in
private theorem order_of_omega_elementary (Q : Subgroup K) [IsElementaryAbelian 2 Q]
    (x : K) (hx : x ∈ Q) (hne : x ≠ 1) : orderOf x = 2 := by
  exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hne

private theorem linear [IsSimpleGroup K] (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (e : K ≃* PSL(2,F)) (P : Sylow 2 K)
    (hrank : IsRankOneModel K) : Facts (omegaOneAmbient (P : Subgroup K)) := by
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let a : Multiplicative F ≃* P := (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive R).trans
    (e.subgroupMap (P : Subgroup K)).symm
  have hp2 (x : P) : x ^ 2 = 1 := by
    apply a.symm.injective
    rw [map_pow, map_one]
    change 2 • (a.symm x).toAdd = 0
    exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)
  let : IsMulCommutative P := ⟨⟨fun x y => a.symm.injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩
  have hOmega : omegaOneAmbient (P : Subgroup K) = P := by
    apply le_antisymm (omegaOneAmbient_le _)
    intro x hx
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl x hx (congrArg Subtype.val (hp2 ⟨x, hx⟩))
  have hcenter : omegaOneAmbient (P : Subgroup K) = (center P).map (P : Subgroup K).subtype := by
    rw [center_eq_top, ← MonoidHom.range_eq_map, (P : Subgroup K).range_subtype, hOmega]
  have hsize : 2 < Nat.card (omegaOneAmbient (P : Subgroup K)) := by
    rw [hOmega, ← Nat.card_congr a.toEquiv, Nat.card_congr Multiplicative.toAdd]
    omega
  have hN := normalizer_omega hrank P hcenter hsize
  obtain ⟨D, hDcyc, hDcard, _, hsup⟩ := (LinearAction.sylow_geometry e hF P).complement
  have hDodd : Odd (Nat.card D) := by
    rw [hDcard]
    have heven : Even (Nat.card F) := by
      let := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card]
      exact Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))
    exact Nat.Even.sub_odd (by omega) heven odd_one
  have hDNP : D ≤ normalizer (P : Set K) := hsup ▸ le_sup_right
  obtain ⟨hcyc, hodd⟩ := cyclic_odd_of_complement _ (P : Subgroup K) D hDNP
    (hN.trans hsup.symm) (le_centralizer_iff.mp (omega_centralizes P hcenter)) hDcyc hDodd
  refine ⟨hsize, hcyc, hodd, ?_⟩
  apply transitive_of_involution_fusion P _ (omega_centralizes P hcenter) hN.symm.le
  · intro x hx hne
    exact orderOf_eq_prime (congrArg Subtype.val (hp2 ⟨x, show x ∈ (P : Subgroup K) from hOmega ▸ hx⟩)) hne
  · intro x y hx hy
    have he := Theory.PSL2.involutions_isConj (e x) (e y)
      (by simpa only [e.orderOf_eq] using hx) (by simpa only [e.orderOf_eq] using hy)
    have hm := e.symm.toMonoidHom.map_isConj he
    change IsConj (e.symm (e x)) (e.symm (e y)) at hm
    simpa only [e.symm_apply_apply] using hm

private theorem suzuki [IsSimpleGroup K] {m : ℕ} (hm : 1 ≤ m)
    (e : K ≃* SuzukiMatrixGroup m) (P : Sylow 2 K) :
    Facts (omegaOneAmbient (P : Subgroup K)) := by
  have hc := suzukiSylow_omega_eq_center (by omega : 0 < m) e P
  have hcard := suzukiSylow_omega_card (by omega : 0 < m) e P
  have hs : 2 < Nat.card (omegaOneAmbient (P : Subgroup K)) := by
    rw [hcard]
    have := four_le (by omega : 2 ≤ 2 * m + 1)
    omega
  have hN := normalizer_omega (.suzuki m ⟨e⟩) P hc hs
  obtain ⟨_, _, D, ⟨eD⟩, hsup, _⟩ := suzukiSylow_borel_structure (by omega) e P
  have hd : Nat.card D = 2 ^ (2 * m + 1) - 1 := by
    rw [Nat.card_congr eD.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hod : Odd (Nat.card D) := by
    rw [hd]
    exact Nat.Even.sub_odd (by have := pow_pos (by decide : 0 < (2 : ℕ)) (2 * m + 1); omega) (even_two.pow_of_ne_zero (by omega)) odd_one
  have hcyD : IsCyclic D := eD.isCyclic.mpr inferInstance
  have hDN : D ≤ normalizer (P : Set K) := hsup ▸ le_sup_right
  obtain ⟨hcyc, hodd⟩ := cyclic_odd_of_complement _ (P : Subgroup K) D hDN
    (hN.trans hsup.symm) (le_centralizer_iff.mp (omega_centralizes P hc)) hcyD hod
  let := suzukiSylow_omega_elementary (by omega : 0 < m) e P
  refine ⟨hs, hcyc, hodd, ?_⟩
  apply transitive_of_involution_fusion P _ (omega_centralizes P hc) hN.symm.le
    (order_of_omega_elementary _)
  intro x y hx hy
  have he := suzuki_involutions_isConj m (by omega) (e x) (e y)
    (by simpa only [e.orderOf_eq] using hx) (by simpa only [e.orderOf_eq] using hy)
  have hh := e.symm.toMonoidHom.map_isConj he
  change IsConj (e.symm (e x)) (e.symm (e y)) at hh
  simpa only [e.symm_apply_apply] using hh

private theorem unitary_transitive {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : K ≃* ProjectiveSpecialUnitaryMatrixGroup J) (P : Sylow 2 K) :
    ∀ a ∈ omegaOneAmbient (P : Subgroup K), a ≠ 1 →
      ∀ b ∈ omegaOneAmbient (P : Subgroup K), b ≠ 1 →
      ∃ t ∈ normalizer (omegaOneAmbient (P : Subgroup K) : Set K), t * a * t⁻¹ = b := by
  obtain ⟨C, hC⟩ := Unitary.FormTransport.exists_standard_basis J n (by omega) hcard hconj
  let J0 := Unitary.FormTransport.standardForm J
  let e0 := e.trans (Unitary.FormTransport.projectiveEquiv J C hC)
  have hfixed := Unitary.fixed_card J0 n (by omega) hcard hconj
  let : CharP E 2 := Unitary.charP_two n (by omega) hcard
  let R := HermitianForm.EvenTwoRank.rootSylow J0 rfl (by omega : 0 < n) hcard hfixed
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J0) := Finite.of_injective e0.symm e0.symm.injective
  let P0 := P.mapSurjective (f := e0.toMonoidHom) e0.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J0) R P0
  let f := (MulAut.conj g).trans e0.symm
  have hP : (R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J0)).map f.toMonoidHom = P := by
    rw [show f.toMonoidHom = e0.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom from rfl,
      ← map_map, show (R : Subgroup _).map (MulAut.conj g).toMonoidHom =
        (P : Subgroup K).map e0.toMonoidHom from congrArg Sylow.toSubgroup hg]
    rw [map_map, show e0.symm.toMonoidHom.comp e0.toMonoidHom = MonoidHom.id K from by
      ext x
      exact e0.symm_apply_apply x, Subgroup.map_id]
  have hQ : (HermitianForm.BorelTorus.EvenCenterAction.centralImage J0 rfl).map
      f.toMonoidHom = omegaOneAmbient (P : Subgroup K) := by
    rw [← hP, ← map_omegaOneAmbient_injective f.toMonoidHom f.injective,
      (HermitianForm.SylowOmega.projective_sylow_omega J0 hn hcard hfixed rfl R).1]
    congr 1
    exact (HermitianForm.NormalizedRootCentralizers.root_center J0 (by omega) hcard hfixed rfl).symm
  intro a ha hane b hb hbne
  obtain ⟨a0, ⟨a1, rfl⟩, rfl⟩ := show a ∈ (HermitianForm.BorelTorus.EvenCenterAction.centralImage
    J0 rfl).map f.toMonoidHom from hQ.symm ▸ ha
  obtain ⟨b0, ⟨b1, rfl⟩, rfl⟩ := show b ∈ (HermitianForm.BorelTorus.EvenCenterAction.centralImage
    J0 rfl).map f.toMonoidHom from hQ.symm ▸ hb
  have ha1 : a1.toAdd ≠ 0 := by
    intro he
    exact hane (by rw [show a1 = 1 from he, map_one, map_one])
  have hb1 : b1.toAdd ≠ 0 := by
    intro he
    exact hbne (by rw [show b1 = 1 from he, map_one, map_one])
  obtain ⟨k, hk⟩ := HermitianForm.BorelTorus.EvenCenterAction.central_transitive
    J0 rfl hcard hfixed a1.toAdd b1.toAdd ha1 hb1
  refine ⟨f (BenderSuzuki.External.hermitianTorusPSU J0 rfl k), ?_, ?_⟩
  · rw [← hQ]
    exact le_normalizer_map f.toMonoidHom ⟨_,
      HermitianForm.BorelTorus.EvenCenterAction.torus_normalizes J0 rfl ⟨k, rfl⟩, rfl⟩
  · change f (BenderSuzuki.External.hermitianTorusPSU J0 rfl k) *
        f (HermitianForm.BorelTorus.EvenCenterAction.centralMap J0 rfl a1) *
          (f (BenderSuzuki.External.hermitianTorusPSU J0 rfl k))⁻¹ =
        f (HermitianForm.BorelTorus.EvenCenterAction.centralMap J0 rfl b1)
    have hk' : BenderSuzuki.External.hermitianTorusPSU J0 rfl k *
        HermitianForm.BorelTorus.EvenCenterAction.centralMap J0 rfl a1 *
          (BenderSuzuki.External.hermitianTorusPSU J0 rfl k)⁻¹ =
        HermitianForm.BorelTorus.EvenCenterAction.centralMap J0 rfl b1 := hk
    simpa only [map_mul, map_inv] using congrArg f hk'

private theorem unitary [IsSimpleGroup K] {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU K 3 (2 ^ n)) (P : Sylow 2 K) :
    Facts (omegaOneAmbient (P : Subgroup K)) := by
  obtain ⟨E, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
  have hm : ClassicalGroup.IsPSU K 3 (2 ^ n) := ⟨E, inferInstance, inferInstance,
    J, hcard, hconj, ⟨e⟩⟩
  obtain ⟨C, hC⟩ := Unitary.FormTransport.exists_standard_basis J n (by omega) hcard hconj
  let J0 := Unitary.FormTransport.standardForm J
  have hfixed := Unitary.fixed_card J0 n (by omega) hcard hconj
  obtain ⟨hc, _, hsize⟩ := HermitianForm.SylowOmega.omega_of_projective_equiv
    J0 hn hcard hfixed rfl (e.trans (Unitary.FormTransport.projectiveEquiv J C hC)) P
  have hs : 2 < Nat.card (omegaOneAmbient (P : Subgroup K)) := by
    rw [hsize]
    have := four_le hn
    omega
  have hN := normalizer_omega (.projective_unitary n (by omega) hm) P hc hs
  obtain ⟨a⟩ := (UnitaryAction.centerAction_of_isPSU hn hm P).cyclic_image
  have ht : ChapterE.inducedAutomizer (omegaOneAmbient (P : Subgroup K))
      (normalizer (P : Set K)) = ⊤ := by
    rw [← hN]
    simp only [ChapterE.inducedAutomizer, subgroupOf_self, Subgroup.map_top_of_surjective _ (omegaOneAmbient (P : Subgroup K)).normalizerMonoidHom.rangeRestrict_surjective]
  have ha : Nonempty ((omegaOneAmbient (P : Subgroup K)).normalizerMonoidHom.range ≃*
      Multiplicative (ZMod (2 ^ n - 1))) := by
    have hc' : UnitaryAction.sylowCenter P = omegaOneAmbient (P : Subgroup K) := hc.symm
    rw [hc', ht] at a
    exact ⟨(Subgroup.topEquiv).symm.trans a⟩
  obtain ⟨a⟩ := ha
  refine ⟨hs, a.isCyclic.mpr inferInstance, ?_, unitary_transitive J hn hcard hconj e P⟩
  rw [Nat.card_congr a.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact Nat.Even.sub_odd (by have := pow_pos (by decide : 0 < (2 : ℕ)) n; omega) (even_two.pow_of_ne_zero (by omega)) odd_one

/-- The exact Bender models supply all four full-normalizer action inputs. -/
theorem of_bender_model (hm : ClassificationModels.IsBenderModel K) (P : Sylow 2 K) :
    Facts (omegaOneAmbient (P : Subgroup K)) := by
  let : IsSimpleGroup K := simple hm
  have hr := rankOne hm
  cases hm with
  | linear n hn h =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [← Nat.card_eq_fintype_card] using hF)
    exact linear F (hF ▸ four_le hn) e P hr
  | unitary n hn h => exact unitary hn h P
  | suzuki m hm h => exact suzuki hm h.some P

omit [Finite K] in
/-- Component perfectness and concrete-model simplicity remove the whole center. -/
theorem centerless_of_bender_model [Group.IsPerfect K] [Nontrivial K]
    (hm : ClassificationModels.IsBenderModel K) : center K = ⊥ := by
  let : IsSimpleGroup K := simple hm
  rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h)).elim
end CFSG.Quasithin.Chapter2.BenderFusion.OmegaNormalizerModels

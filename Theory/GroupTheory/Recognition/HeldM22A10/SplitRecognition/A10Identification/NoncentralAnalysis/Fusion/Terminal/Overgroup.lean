module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Terminal.MuSylow
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.SylowActor.LocalGeometry
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Mathlib.GroupTheory.IndexNormal
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.Tables
public import Theory.GroupTheory.WeakClosureOvergroups

/-!
# The terminal join in Held's Lemma 2.6

Let Q be the common centralizer of pi and mu, and let P be a Sylow
2-subgroup of C_G(mu) containing Q. The join of the displayed Sylow D and
P has order 384 and normalizes the actual elementary subgroup S.

The index-two subgroup Q is normal in both Sylows, so the join normalizes
its center, the four-group <pi,mu>. The action on this four-group has kernel
Q of order 64 and image of order dividing six. Since the join strictly
contains D of order 128, its order is 384.

For normalization, the complete elementary-sixteen catalogue and its local
fusion tables distinguish S as the unique entry with three elements in the
ambient pi class. Thus S is weakly closed in D. Sylow conjugacy then makes
every 2-subgroup containing S normalize it, in particular the chosen P.
All fusion premises are the ones available at this point in the source;
the order calculation needs only pi--mu fusion.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.6, printed p.229.
Source conjugation is g^-1*x*g; the action here uses g*x*g^-1.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private theorem four_eq_plane : terminalFour D e = muPlane D e := by
  apply le_antisymm
  · rw [terminalFour, closure_le]
    rintro x (rfl | rfl)
    · exact (muPlane_mem D e _).mpr (Or.inr (Or.inl rfl))
    · exact (muPlane_mem D e _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  · intro x hx
    have hp : D.z ∈ terminalFour D e := subset_closure (by simp)
    have hm : D.a10NoncentralInvolution e ∈ terminalFour D e := subset_closure (by simp)
    rcases (muPlane_mem D e x).mp hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hp
    · exact hm
    · exact mul_mem hp hm

/-- The four-group is the ambient image of the intrinsic center of the common core. -/
public theorem terminalFour_eq_center : terminalFour D e =
    terminalMuCore D e ⊓ centralizer (terminalMuCore D e : Set G) :=
  four_eq_plane D e

public theorem terminalFour_card : Nat.card (terminalFour D e) = 4 := by
  rw [four_eq_plane, muPlane_card]

public theorem terminalMuCore_le_ambientD : terminalMuCore D e ≤ ambientD D e :=
  muIntersection_le_sylow D e

omit [Finite G] in
private theorem index_two_normalizes (Q R : Subgroup G) (hQR : Q ≤ R)
    (hQ : Nat.card Q = 64) (hR : Nat.card R = 128) : R ≤ normalizer (Q : Set G) := by
  have hi : (Q.subgroupOf R).index = 2 := by
    have hc := (Q.subgroupOf R).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hQR).toEquiv, hQ, hR] at hc
    omega
  exact (normal_subgroupOf_iff_le_normalizer hQR).mp (normal_of_index_eq_two hi)

/-- The index-two core is normal in each generating Sylow subgroup, hence in their join. -/
public theorem terminalJoin_le_normalizer_core
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (P : Sylow 2 (terminalMuCentralizer D e))
    (hP : terminalMuCore D e ≤ terminalMuSylowImage D e P) :
    terminalJoin D e P ≤ normalizer (terminalMuCore D e : Set G) := by
  apply sup_le
  · exact index_two_normalizes _ _ (terminalMuCore_le_ambientD D e)
      (terminalMuCore_card D e) (ambientD_card D e)
  · exact index_two_normalizes _ _ hP (terminalMuCore_card D e)
      (terminalMuSylowImage_card D e hmu P)

/-- The join acts by automorphisms on the actual four-group <pi,mu>. -/
public theorem terminalJoin_le_normalizer_four
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (P : Sylow 2 (terminalMuCentralizer D e))
    (hP : terminalMuCore D e ≤ terminalMuSylowImage D e P) :
    terminalJoin D e P ≤ normalizer (terminalFour D e : Set G) := by
  rw [four_eq_plane]
  exact (terminalJoin_le_normalizer_core D e hmu P hP).trans (muPlane_normalizer D e)

private theorem four_isKleinFour : IsKleinFour (terminalFour D e) := by
  let V := terminalFour D e
  have hc : Nat.card V = 4 := terminalFour_card D e
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsElementaryAbelian 2 (ambientElementary D e 1) := ambientElementary_isElementaryAbelian D e 1
  have hs (x : V) : x ^ 2 = 1 := by
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) (terminalFour_le_S D e x.property)
  let : IsElementaryAbelian 2 V :=
    { is_comm := ⟨fun x y => (Commute.of_orderOf_dvd_two
        (fun x => orderOf_dvd_of_pow_eq_one (hs x)) x y).eq⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  exact ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩

private noncomputable def fourAction (K : Subgroup G)
    (hKV : K ≤ normalizer (terminalFour D e : Set G)) : K →* MulAut (terminalFour D e) :=
  (terminalFour D e).normalizerMonoidHom.comp (inclusion hKV)

omit [Finite G] in
private theorem fourAction_ker (K : Subgroup G)
    (hKV : K ≤ normalizer (terminalFour D e : Set G)) :
    (fourAction D e K hKV).ker = (terminalMuCore D e).subgroupOf K := by
  ext g
  change fourAction D e K hKV g = 1 ↔ (g : G) ∈ terminalMuCore D e
  rw [← terminalFour_centralizer]
  constructor
  · intro hg x hx
    have he := congrArg (fun σ : MulAut (terminalFour D e) => (σ ⟨x, hx⟩ : G)) hg
    change (g : G) * x * (g : G)⁻¹ = x at he
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  · intro hg
    ext x
    change (g : G) * (x : G) * (g : G)⁻¹ = (x : G)
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hg _ x.property).symm

private theorem order_arithmetic (n : ℕ) (hn : n ∣ 6)
    (h128 : 128 ∣ 64 * n) (hne : 64 * n ≠ 128) : 64 * n = 384 := by
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hn
  interval_cases n <;> norm_num at *

/-- The faithful quotient action on <pi,mu> has order six, so Held's join has order 384. -/
public theorem terminalJoin_card
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (P : Sylow 2 (terminalMuCentralizer D e))
    (hP : terminalMuCore D e ≤ terminalMuSylowImage D e P) :
    Nat.card (terminalJoin D e P) = 384 := by
  let K := terminalJoin D e P
  let a := fourAction D e K (terminalJoin_le_normalizer_four D e hmu P hP)
  have hQK : terminalMuCore D e ≤ K := (terminalMuCore_le_ambientD D e).trans le_sup_left
  have hker : Nat.card a.ker = 64 := by
    rw [fourAction_ker, Nat.card_congr (subgroupOfEquivOfLe hQK).toEquiv, terminalMuCore_card]
  have hind : a.ker.index ∣ 6 := by
    let := four_isKleinFour D e
    rw [index_ker]
    have h := card_subgroup_dvd_card a.range
    rwa [IsKleinFour.card_mulAut] at h
  have hc : Nat.card K = 64 * a.ker.index := by
    rw [← a.ker.card_mul_index, hker]
  have h128 : 128 ∣ Nat.card K := by
    rw [← ambientD_card D e]
    exact card_dvd_of_le le_sup_left
  have hne : Nat.card K ≠ 128 := by
    intro he
    have heq : ambientD D e = K := eq_of_le_of_card_ge le_sup_left (by rw [he, ambientD_card])
    exact (ne_of_lt (terminal_ambientD_lt_join D e hmu P)) heq
  rw [hc] at h128 hne ⊢
  exact order_arithmetic _ hind h128 hne

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem code_count_separates : ∀ b : Fin 9 → Bool,
    b 0 = false → b 1 = true → b 2 = true →
    b 3 = false → b 4 = false → b 5 = false →
    (b 6 = true ∨ b 7 = true ∨ b 8 = true) →
    ∀ k : Fin 4,
      (Fintype.card {a : BaseCode // b (elementaryClass k a) = true} = 3 ↔ k = 1) := by
  decide +kernel

/-- Under the terminal fusion assumptions, exactly S has three pi-fused elements
among the four elementary-sixteen catalogue entries. -/
public theorem terminal_fused_card_eq_three_iff
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (htau : ¬ IsConj D.z (D.a10ModelEmbedding e tau))
    (hpilam : ¬ IsConj D.z (D.a10ModelEmbedding e (pi * lam)))
    (hxi : IsConj D.z (D.a10ModelEmbedding e xi) ∨
      IsConj D.z (D.a10ModelEmbedding e (pi * xi)) ∨
      IsConj D.z (D.a10ModelEmbedding e (tau * lam * xi))) (k : Fin 4) :
    (fusedElements (ambientElementary D e k) D.z).ncard = 3 ↔ k = 1 := by
  classical
  let b : Fin 9 → Bool := fun i => decide (IsConj D.z (D.a10ModelEmbedding e (localRepresentative i)))
  have h0 : b 0 = false := by simp [b, localRepresentative, D.z_ne_one]
  have h1 : b 1 = true := by
    change decide (IsConj D.z (D.a10ModelEmbedding e pi)) = true
    rw [D.a10ModelEmbedding_central e]
    exact decide_eq_true (IsConj.refl _)
  have h2 : b 2 = true := by
    change decide (IsConj D.z (D.a10NoncentralInvolution e)) = true
    exact decide_eq_true hmu
  have h3 : b 3 = false := by
    change decide (IsConj D.z (D.a10ModelEmbedding e tau)) = false
    exact decide_eq_false_iff_not.mpr htau
  have h4 : b 4 = false := by
    change decide (IsConj D.z (D.a10ModelEmbedding e lam)) = false
    exact decide_eq_false_iff_not.mpr hlam
  have h5 : b 5 = false := by
    change decide (IsConj D.z (D.a10ModelEmbedding e (pi * lam))) = false
    exact decide_eq_false_iff_not.mpr hpilam
  have h678 : b 6 = true ∨ b 7 = true ∨ b 8 = true := by
    rcases hxi with h | h | h
    · left
      change decide (IsConj D.z (D.a10ModelEmbedding e xi)) = true
      exact decide_eq_true h
    · right; left
      change decide (IsConj D.z (D.a10ModelEmbedding e (pi * xi))) = true
      exact decide_eq_true h
    · right; right
      change decide (IsConj D.z (D.a10ModelEmbedding e (tau * lam * xi))) = true
      exact decide_eq_true h
  have he (a : BaseCode) : b (elementaryClass k a) = true ↔
      IsConj D.z (D.a10ModelEmbedding e (elementaryWord k a)) := by
    simp only [b, decide_eq_true_eq]
    have hc := (D.a10ModelEmbedding e).map_isConj (elementaryWord_isConj k a)
    exact ⟨fun h => h.trans hc, fun h => h.trans hc.symm⟩
  let w := Equiv.ofBijective _ (elementaryWord_bijective k)
  let f := (elementary k).equivMapOfInjective (D.a10ModelEmbedding e)
    (D.a10ModelEmbedding_injective e)
  have hc : Nat.card {a : BaseCode // b (elementaryClass k a) = true} =
      (fusedElements (ambientElementary D e k) D.z).ncard := by
    exact Nat.card_congr (Equiv.subtypeEquiv (w.trans f.toEquiv) he)
  rw [← hc, Nat.card_eq_fintype_card]
  exact code_count_separates b h0 h1 h2 h3 h4 h5 h678 k

/-- Fusion counts distinguish S from all other entries, so every conjugate of S
contained in the displayed Sylow subgroup is S itself. -/
public theorem terminal_S_weakly_closed
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (htau : ¬ IsConj D.z (D.a10ModelEmbedding e tau))
    (hpilam : ¬ IsConj D.z (D.a10ModelEmbedding e (pi * lam)))
    (hxi : IsConj D.z (D.a10ModelEmbedding e xi) ∨
      IsConj D.z (D.a10ModelEmbedding e (pi * xi)) ∨
      IsConj D.z (D.a10ModelEmbedding e (tau * lam * xi)))
    (g : G)
    (hg : (ambientElementary D e 1).map (MulAut.conj g).toMonoidHom ≤ ambientSylow D e) :
    (ambientElementary D e 1).map (MulAut.conj g).toMonoidHom = ambientElementary D e 1 := by
  have hA : IsElementaryAbelian 2 ((ambientElementary D e 1).map (MulAut.conj g).toMonoidHom) := by
    let := ambientElementary_isElementaryAbelian D e 1
    exact IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hcard : Nat.card ((ambientElementary D e 1).map (MulAut.conj g).toMonoidHom) = 16 := by
    rw [card_map_of_injective (MulAut.conj g).injective, ambientElementary_card]
  obtain ⟨k, hk⟩ := ambient_elementary_sixteen D e _ hg hA hcard
  have hc := fusedElements_map_conj_card (ambientElementary D e 1) D.z g
  rw [hk] at hc
  have hs := (terminal_fused_card_eq_three_iff D e hmu hlam htau hpilam hxi 1).mpr rfl
  have hk1 := (terminal_fused_card_eq_three_iff D e hmu hlam htau hpilam hxi k).mp (hc.trans hs)
  simpa only [hk1] using hk

/-- Sylow transport of the weakly closed S makes the mu-Sylow normalize S;
the displayed Sylow already normalizes it, hence so does their join. -/
public theorem terminalJoin_le_normalizer_S
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (htau : ¬ IsConj D.z (D.a10ModelEmbedding e tau))
    (hpilam : ¬ IsConj D.z (D.a10ModelEmbedding e (pi * lam)))
    (hxi : IsConj D.z (D.a10ModelEmbedding e xi) ∨
      IsConj D.z (D.a10ModelEmbedding e (pi * xi)) ∨
      IsConj D.z (D.a10ModelEmbedding e (tau * lam * xi)))
    (P : Sylow 2 (terminalMuCentralizer D e))
    (hP : terminalMuCore D e ≤ terminalMuSylowImage D e P) :
    terminalJoin D e P ≤ normalizer (ambientElementary D e 1 : Set G) := by
  apply sup_le (ambientSylow_le_normalizer_S D e)
  apply le_normalizer_of_isPGroup_of_weakly_closed (ambientSylow D e) _ _
    (terminal_S_weakly_closed D e hmu hlam htau hpilam hxi)
    (P.isPGroup'.map (terminalMuCentralizer D e).subtype)
  apply le_trans ?_ hP
  rw [terminalMuCore_eq]
  exact le_sup_left.trans le_sup_left

/-- The two properties of Held's terminal join, with the original fusion premises. -/
public theorem terminalJoin_card_and_normalizes
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (htau : ¬ IsConj D.z (D.a10ModelEmbedding e tau))
    (hpilam : ¬ IsConj D.z (D.a10ModelEmbedding e (pi * lam)))
    (hxi : IsConj D.z (D.a10ModelEmbedding e xi) ∨
      IsConj D.z (D.a10ModelEmbedding e (pi * xi)) ∨
      IsConj D.z (D.a10ModelEmbedding e (tau * lam * xi)))
    (P : Sylow 2 (terminalMuCentralizer D e))
    (hP : terminalMuCore D e ≤ terminalMuSylowImage D e P) :
    Nat.card (terminalJoin D e P) = 384 ∧
      terminalJoin D e P ≤ normalizer (ambientElementary D e 1 : Set G) :=
  ⟨terminalJoin_card D e hmu P hP,
    terminalJoin_le_normalizer_S D e hmu hlam htau hpilam hxi P hP⟩

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion

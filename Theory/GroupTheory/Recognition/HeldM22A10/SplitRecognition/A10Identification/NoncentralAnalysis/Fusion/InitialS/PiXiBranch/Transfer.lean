module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.InitialS.PiXiBranch
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Normalization
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.Tables
public import Theory.GroupTheory.InvolutionTransfer

/-!
# Transfer in the initial pi--xi branch

The fixed subgroup of the lambda twist cuts the displayed Sylow group in
an index-two subgroup M<tau,tau'>. Thompson transfer sends pi*lambda to
an involution in this subgroup. Its local classes are 1, pi, mu, tau, xi
and pi*xi. The cubic actor in the pi--xi branch identifies the two xi
classes with mu and pi; hence nonfusion with pi leaves precisely mu or tau.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.9, printed pp.229--230.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS
open Coordinates CentralizerStructure.FaithfulExclusion

private def fixedLambda : Subgroup H where
  carrier := {x | lambdaTwist x = x}
  one_mem' := map_one _
  mul_mem' {x y} hx hy := by change lambdaTwist (x * y) = x * y; rw [map_mul, hx, hy]
  inv_mem' {x} hx := by change lambdaTwist x⁻¹ = x⁻¹; rw [map_inv, hx]

private def transferModel : Subgroup H := modelD ⊓ fixedLambda

private theorem lambdaTwist_word (a : Code) :
    lambdaTwist (word a) = baseWord a.1 *
      (tau ^ a.2.1.val * taup ^ a.2.2.1.val * rho ^ a.2.2.2.1.val *
        (Coordinates.pi * lam) ^ a.2.2.2.2.val) := by
  have hmup : lambdaTwist mup = mup := lambdaTwist_generators 2
  have htau : lambdaTwist tau = tau := lambdaTwist_generators 3
  have htaup : lambdaTwist taup = taup := lambdaTwist_generators 4
  have hrho : lambdaTwist rho = rho := lambdaTwist_generators 5
  have hxi : lambdaTwist xi = xi := lambdaTwist_generators 7
  simp only [word, baseWord, actorWord, map_mul, map_pow, lambdaTwist_pi,
    lambdaTwist_mu, hmup, htau, htaup, hrho, hxi, lambdaTwist_lam]

private theorem word_mem_transferModel (a : Code) :
    word a ∈ transferModel ↔ a.2.2.2.1 = 0 ∧ a.2.2.2.2 = 0 := by
  change word a ∈ modelD ∧ lambdaTwist (word a) = word a ↔ _
  rw [word_mem_modelD, lambdaTwist_word]
  have h : ∀ a : Code,
      baseWord a.1 * (tau ^ a.2.1.val * taup ^ a.2.2.1.val * rho ^ a.2.2.2.1.val *
        (Coordinates.pi * lam) ^ a.2.2.2.2.val) = word a ↔ a.2.2.2.2 = 0 := by
    decide +kernel
  rw [h]

private theorem transferModel_card : Nat.card transferModel = 64 := by
  rw [← Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective word word_bijective)
    (fun a => (word_mem_transferModel a).symm)), Nat.card_eq_fintype_card]
  decide +kernel

private def transferActorRow : Fin 64 → Code :=
  ![    ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,1,1)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,1,0)),
    ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)),
    ((0,0,0,0),(0,0,1,1)), ((0,0,0,1),(0,0,1,1)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)),
    ((0,0,0,0),(0,0,2,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)),
    ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,1),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)),
    ((0,0,0,0),(0,0,0,1)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)),
    ((0,0,0,0),(0,0,1,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,1),(0,0,1,0)),
    ((0,0,0,0),(1,1,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)),
    ((0,0,0,0),(0,0,0,0)), ((0,0,1,0),(0,0,1,1)), ((0,0,1,0),(0,0,0,0)), ((0,0,1,0),(0,0,1,0)),
    ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)),
    ((0,0,0,0),(0,1,1,1)), ((0,0,0,1),(0,1,1,1)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)),
    ((0,0,0,0),(0,0,2,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)),
    ((0,0,0,0),(0,1,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,1),(0,1,0,0)), ((0,0,0,0),(0,0,0,0)),
    ((0,0,0,0),(0,0,0,1)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)),
    ((0,0,0,0),(0,1,1,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,1),(0,1,1,0)),
    ((0,0,0,0),(1,1,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0)), ((0,0,0,0),(0,0,0,0))]

private def transferClassRow : Fin 64 → Fin 6 :=
  ![0, 3, 3, 3, 4, 0, 0, 0, 2, 3, 0, 0, 4, 0, 0, 0, 2, 0, 3, 0, 4, 0, 0, 0, 2, 0, 0, 3, 5, 0, 0, 0, 1, 3, 3, 3, 5, 0, 0, 0, 2, 3, 0, 0, 5, 0, 0, 0, 2, 0, 3, 0, 5, 0, 0, 0, 2, 0, 0, 3, 4, 0, 0, 0]

private def transferIndex (a : Code) : Fin 64 :=
  ⟨32 * a.1.1.val + 16 * a.1.2.1.val + 8 * a.1.2.2.1.val +
    4 * a.1.2.2.2.val + 2 * a.2.1.val + a.2.2.1.val, by omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem transferModel_certificate : ∀ a : Code,
    a.2.2.2.1 = 0 → a.2.2.2.2 = 0 → word a ^ 2 = 1 →
    word (transferActorRow (transferIndex a)) * word a *
      (word (transferActorRow (transferIndex a)))⁻¹ =
      (![1, Coordinates.pi, Coordinates.mu, tau, xi, Coordinates.pi * xi] : Fin 6 → H)
        (transferClassRow (transferIndex a)) := by
  decide +kernel

private theorem transferModel_table (a : Code)
    (hr : a.2.2.2.1 = 0) (hl : a.2.2.2.2 = 0) (h2 : word a ^ 2 = 1) :
    ∃ b : Code, ∃ i : Fin 6,
      word b * word a * (word b)⁻¹ =
        (![1, Coordinates.pi, Coordinates.mu, tau, xi, Coordinates.pi * xi] : Fin 6 → H) i :=
  ⟨_, _, transferModel_certificate a hr hl h2⟩

private theorem transferModel_classes {x : H} (hx : x ∈ transferModel) (hx2 : x ^ 2 = 1) :
    ∃ i : Fin 6, IsConj x
      ((![1, Coordinates.pi, Coordinates.mu, tau, xi, Coordinates.pi * xi] : Fin 6 → H) i) := by
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  obtain ⟨hr, hl⟩ := (word_mem_transferModel a).mp hx
  obtain ⟨b, i, hi⟩ := transferModel_table a hr hl hx2
  exact ⟨i, isConj_iff.mpr ⟨word b, hi⟩⟩

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private theorem piLambda_transfer_classes [IsSimpleGroup G] :
    ∃ i : Fin 6, IsConj (D.a10ModelEmbedding e (Coordinates.pi * lam))
      (D.a10ModelEmbedding e
        ((![1, Coordinates.pi, Coordinates.mu, tau, xi, Coordinates.pi * xi] : Fin 6 → H) i)) := by
  let f := D.a10ModelEmbedding e
  let E : Subgroup G := transferModel.map f
  have hE : E ≤ ambientSylow D e := map_mono inf_le_left
  let U : Subgroup (ambientSylow D e) := E.subgroupOf (ambientSylow D e)
  have hcard : Nat.card U = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hE).toEquiv,
      card_map_of_injective (D.a10ModelEmbedding_injective e), transferModel_card]
  have hindex : U.index = 2 := by
    have h := U.card_mul_index
    rw [hcard] at h
    have hs : Nat.card (ambientSylow D e) = 128 := ambientD_card D e
    rw [hs] at h
    omega
  have hxmem : f (Coordinates.pi * lam) ∈ ambientSylow D e := by
    apply mem_map_of_mem
    have hp : Coordinates.pi ∈ modelD := subset_closure ⟨0, rfl⟩
    have hl : lam ∈ modelD := subset_closure ⟨5, rfl⟩
    exact modelD.mul_mem hp hl
  let x : ambientSylow D e := ⟨f (Coordinates.pi * lam), hxmem⟩
  have hxorder : orderOf x = 2 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (f (Coordinates.pi * lam)) = 2
    rw [orderOf_injective f (D.a10ModelEmbedding_injective e)]
    apply orderOf_eq_prime
    · decide +kernel
    · decide +kernel
  obtain ⟨y, hxy, hy⟩ := (ambientSylow D e).exists_isConj_mem_of_index_two
    (fun K _ => D.no_index_two K) U hindex x hxorder
  change (y : G) ∈ E at hy
  obtain ⟨t, ht, he⟩ := hy
  change f t = (y : G) at he
  have ht2 : t ^ 2 = 1 := by
    apply D.a10ModelEmbedding_injective e
    rw [map_pow, map_one, he]
    have hyo : orderOf (y : G) = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hxy
      rw [← hg, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
        Subgroup.orderOf_coe, hxorder]
    simpa only [hyo] using pow_orderOf_eq_one (y : G)
  obtain ⟨i, hi⟩ := transferModel_classes ht ht2
  refine ⟨i, hxy.trans ?_⟩
  simpa only [he] using f.map_isConj hi

/-- The precise transfer conclusion after the cubic actor in Held 2.9:
pi*lambda fuses with mu or tau. -/
public theorem piLambda_isConj_mu_or_tau_of_piXi_fusion [IsSimpleGroup G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hpiLam : ¬ IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * lam)))
    (d : Bit) (hxi : ¬ IsConj D.z (D.a10ModelEmbedding e (normalizedXi d)))
    (hpiXi : IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedXi d))) :
    IsConj (D.a10ModelEmbedding e (Coordinates.pi * lam)) (D.a10NoncentralInvolution e) ∨
      IsConj (D.a10ModelEmbedding e (Coordinates.pi * lam)) (D.a10ModelEmbedding e tau) := by
  let f := D.a10ModelEmbedding e
  have hximu := xi_isConj_mu_of_piXi_fusion D e hfusion d hxi hpiXi
  have hclass (x : H) (hx : x = xi ∨ x = Coordinates.pi * xi) :
      IsConj (f (Coordinates.pi * lam)) (f x) →
        IsConj (f (Coordinates.pi * lam)) (D.a10NoncentralInvolution e) := by
    have hchoices : x = normalizedXi d ∨ x = Coordinates.pi * normalizedXi d := by
      have h : ∀ d : Bit, ∀ x : H, (x = xi ∨ x = Coordinates.pi * xi) →
          x = normalizedXi d ∨ x = Coordinates.pi * normalizedXi d := by
        intro d x hx
        rcases hx with rfl | rfl <;> fin_cases d <;> decide +kernel
      exact h d x hx
    intro hc
    rcases hchoices with rfl | rfl
    · exact hc.trans hximu
    · exact (hpiLam (hpiXi.trans hc.symm)).elim
  obtain ⟨i, hi⟩ := piLambda_transfer_classes D e
  fin_cases i
  · change IsConj (f (Coordinates.pi * lam)) (f 1) at hi
    have he : f (Coordinates.pi * lam) = f 1 :=
      (isConj_one_left.mp (by simpa only [map_one] using hi)).trans f.map_one.symm
    have hne : Coordinates.pi * lam ≠ (1 : H) := by decide +kernel
    exact (hne ((D.a10ModelEmbedding_injective e) he)).elim
  · change IsConj (f (Coordinates.pi * lam)) (D.a10ModelEmbedding e Coordinates.pi) at hi
    exact (hpiLam (by simpa only [D.a10ModelEmbedding_central e] using hi.symm)).elim
  · exact Or.inl hi
  · exact Or.inr hi
  · exact Or.inl (hclass xi (Or.inl rfl) hi)
  · exact Or.inl (hclass (Coordinates.pi * xi) (Or.inr rfl) hi)

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS

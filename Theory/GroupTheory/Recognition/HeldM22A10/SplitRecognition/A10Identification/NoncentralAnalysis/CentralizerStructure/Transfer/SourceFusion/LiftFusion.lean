module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.SourceFusion.QuotientCoordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.SourceFusion.Center

/-!
# Lifting and excluding quotient fusion

Conjugacy in C/<mu> lifts to conjugacy in C with either of the two lifts.
The involution lifts and central fusion theorem reduce the seven-word bound
to tau and zlt. The mu-prime pair is excluded directly by pi--mu nonfusion.
The tau step explicitly retains the needed ambient centralizer bound.

Source: Held, Illinois J. Math. 13 (1969), p.233.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.SourceFusion
open TransferModel (Model l z t m)
local notation "p₀" => TransferModel.p
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

public theorem lift_conjugacy (x : Model) (h : IsConj (p D e) (into D e x)) :
    ∃ c : Fin 2, IsConj (pi D e) (mu D e ^ c.val * lift D e x) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Z D e) g
  have hh : q D e (v * pi D e * v⁻¹) = q D e (lift D e x) := by
    change q D e v * q D e (pi D e) * (q D e v)⁻¹ = q D e (lift D e x) at hg
    simpa only [map_mul, map_inv] using hg
  rcases eq_or_mu_mul_of_q_eq D e _ _ hh with h0 | h1
  · refine ⟨0, isConj_iff.mpr ⟨v, ?_⟩⟩
    simpa using h0
  · refine ⟨1, isConj_iff.mpr ⟨v, ?_⟩⟩
    simpa using h1

public theorem lift_square (x : Model) (h : IsConj (p D e) (into D e x)) :
    Local.liftWord x ^ 2 = 1 := by
  obtain ⟨c, hc⟩ := lift_conjugacy D e x h
  have hpi : pi D e ^ 2 = 1 := by
    apply Subtype.ext
    exact (D.z_order ▸ pow_orderOf_eq_one D.z)
  have hs : (mu D e ^ c.val * lift D e x)^2 = 1 := by
    have hh := hc.pow 2
    rw [hpi] at hh
    exact isConj_one_right.mp hh
  have hlocal : (Coordinates.mu ^ c.val * Local.liftWord x)^2 = 1 := by
    apply D.a10ModelEmbedding_injective e
    simpa only [map_pow, map_mul, map_one, mu, lift, LocalData.a10NoncentralInvolution,
      Coordinates.mu, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one] using
      congrArg (fun v : C D e => (v : G)) hs
  fin_cases c
  · simpa using hlocal
  · simpa only [Fin.val_one, pow_one, Local.mu_lift_square] using hlocal

private theorem centralizer_card_conjugate {K : Type*} [Group K] {x y : K}
    (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set K)) = Nat.card (centralizer ({y} : Set K)) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  let f := MulAut.conj g
  apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
  intro a
  change a ∈ centralizer ({x} : Set K) ↔ f a ∈ centralizer ({f x} : Set K)
  simp only [mem_centralizer_singleton_iff, ← map_mul, f.injective.eq_iff]

omit [Finite G] in
private theorem centralizer_mu_mul (x : C D e) :
    centralizer ({mu D e * x} : Set (C D e)) = centralizer ({x} : Set (C D e)) := by
  ext a
  simp only [mem_centralizer_singleton_iff]
  have hm := mem_center_iff.mp (mu_mem_center D e) a
  rw [← mul_assoc a, hm, mul_assoc, mul_assoc, mul_left_cancel_iff]

public theorem not_conj_t
    (ht : Nat.card (centralizer ({lift D e t} : Set (C D e))) ≠ 64) :
    ¬ IsConj (p D e) (into D e t) := by
  intro h
  obtain ⟨c, hc⟩ := lift_conjugacy D e t h
  have hh := centralizer_card_conjugate hc
  change Nat.card (P D e) = _ at hh
  rw [P_card] at hh
  fin_cases c
  · simp only [pow_zero, one_mul] at hh
    exact ht hh.symm
  · simp only [pow_one, centralizer_mu_mul] at hh
    exact ht hh.symm

public theorem not_conj_m_shift
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) (b : Fin 2) :
    ¬ IsConj (p D e) (into D e (p₀ ^ b.val * m)) := by
  intro h
  obtain ⟨c, hc⟩ := lift_conjugacy D e _ h
  have hg := (C D e).subtype.map_isConj hc
  apply hfusion
  apply hg.trans
  let v := Coordinates.rho ^ (if c = 0 then 2 else 1) * Coordinates.tau ^ b.val
  refine isConj_iff.mpr ⟨D.a10ModelEmbedding e v, ?_⟩
  simpa only [v, map_pow, map_mul, map_inv, mu, lift, LocalData.a10NoncentralInvolution,
      Coordinates.mu, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.subtype_apply] using
    congrArg (D.a10ModelEmbedding e) (Local.mup_conjugator b c)

omit [Finite G] in
public theorem isConj_into (x y v : Model) (hv : v * x * v⁻¹ = y) :
    IsConj (into D e x) (into D e y) := by
  refine isConj_iff.mpr ⟨into D e v, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, hv]

public theorem class_bound_of_nonfusion
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (ht : ¬ IsConj (p D e) (into D e t))
    (hzlt : ¬ IsConj (p D e) (into D e (z*l*t))) :
    ∀ x : Model, IsConj (p D e) (into D e x) → Allowed x := by
  intro x hx
  rcases Local.lift_involution_cases x (lift_square D e x hx) with ha | hc | h1 | h2 | h3
  · exact ha
  · obtain ⟨T, hT⟩ := exists_quotient_sylow_eq_centralizer D e hfusion
    have he : (into D e).range = (T : Subgroup (Q D e)) :=
      (into_range D e hfusion).trans hT.symm
    have hh : IsConj (into D e p₀) (into D e x) := by rwa [into_p]
    have hh := central_model_isConj_eq T (into D e) (into_injective D e) he x hc hh
    exact Or.inl hh
  · obtain ⟨b, rfl⟩ := h1
    exact (ht (hx.trans (isConj_into D e _ _ _ (Local.m_shift_t b)))).elim
  · obtain ⟨b, rfl⟩ := h2
    exact (not_conj_m_shift D e hfusion b hx).elim
  · obtain ⟨b, rfl⟩ := h3
    exact (hzlt (hx.trans (isConj_into D e _ _ _ (Local.m_shift_zlt b)))).elim

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.SourceFusion

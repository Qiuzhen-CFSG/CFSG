module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.SourceFusion.QuotientCoordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.SourceFusion.LiftFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.Commutator


/-!
# Transporting Held's earlier actors into the central quotient

An alpha from Section 2.13 gives p conjugate to zm. An initial nu from
Section 4.1 gives p conjugate to lt and excludes t. The initial nu fixes
one of xi and pi*xi, which is sufficient to exclude zlt: its conjugate is
then a central element of the Sylow subgroup distinct from p.

Both possible markings give the same pairs {lt,plt}, {zm,pzm}, {zlt,pzlt}.
Consequently the quotient fusion statement does not require nu to preserve
the particular xi marking selected by alpha. The stronger compatibility
used later in the faithful-action argument remains a separate source result.
These are implications from actual ambient actors; their existence is not
asserted here, and no QuotientCore is assumed.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 2.13 and 4.1, proof of 4.2, p.233.
Source conjugation is x^g = g⁻¹*x*g.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.SourceFusion
open TransferModel (Model l z t m)
open FaithfulExclusion
local notation "p₀" => TransferModel.p
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

omit [Finite G] in
private theorem q_mu : q D e (mu D e) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (mem_zpowers _)

omit [Finite G] in
private theorem q_lift (x : Model) : q D e (lift D e x) = into D e x := rfl

private theorem q_pi : q D e (pi D e) = into D e p₀ := (into_p D e).symm

private theorem pi_val : (pi D e : G) = D.a10ModelEmbedding e Coordinates.pi :=
  (D.a10ModelEmbedding_central e).symm

private theorem local_shift_lt (b : Fin 2) :
    p₀ * (t * (p₀ ^ b.val * l)) = p₀ ^ (b.val + 1) * (l*t) := by
  fin_cases b <;> decide +kernel

private theorem nu_conj_p {b d : Bit} (n : NuRelations D e b d) :
    ∃ v : Q D e,
      v⁻¹ * into D e p₀ * v = into D e (p₀ ^ (b.val+1) * (l*t)) ∧
      v * into D e (p₀ ^ d.val * z) = into D e (p₀ ^ d.val * z) * v := by
  let v : C D e := ⟨n.nu, mem_centralizer_singleton_iff.mpr n.mu_commute.eq⟩
  have hn : v⁻¹ * (pi D e * mu D e) * v =
      (pi D e * mu D e) * (lift D e t * (pi D e ^ b.val * lift D e l)) := by
    apply Subtype.ext
    simpa only [v, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
      pi_val, mu, lift, Local.liftWord_t, Local.liftWord_l, corePi, coreTau,
      normalizedLam, map_mul, map_pow, LocalData.a10NoncentralInvolution, Coordinates.mu] using n.pi_nu
  have hc : v * (pi D e ^ d.val * lift D e z) = (pi D e ^ d.val * lift D e z) * v := by
    apply Subtype.ext
    simpa only [v, Subgroup.coe_mul, Subgroup.coe_pow, pi_val, lift, Local.liftWord_z,
      normalizedXi, map_mul, map_pow] using n.xi_commute.eq
  refine ⟨q D e v, ?_, ?_⟩
  · have hh := congrArg (q D e) hn
    simp only [map_mul, map_inv, map_pow, q_mu, mul_one, q_lift, q_pi] at hh
    exact hh.trans (by
      simpa only [map_mul, map_pow] using congrArg (into D e) (local_shift_lt b))
  · have hh := congrArg (q D e) hc
    simpa only [map_mul, map_pow, q_lift, q_pi] using hh

private theorem local_tauprime :
    Coordinates.taup * Coordinates.mu * Coordinates.taup = corePi := by decide +kernel
private theorem tauprime_square : Coordinates.taup * Coordinates.taup = 1 := by decide +kernel
private theorem local_beta_pi (d : Bit) :
    Coordinates.taup * (Coordinates.pi * normalizedXi d) * Coordinates.taup =
      Coordinates.pi ^ (d.val+1) * (Coordinates.xi * Coordinates.mup) := by
  fin_cases d <;> decide +kernel

private theorem alpha_conj_p {d : Bit} (a : AlphaRelations D e d) :
    IsConj (p D e) (into D e (p₀ ^ (d.val+1) * (z*m))) := by
  let f := D.a10ModelEmbedding e
  let s := f Coordinates.taup
  let beta := s * a.alpha * s
  have hs : s*s = 1 := by rw [← map_mul, tauprime_square, map_one]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs
  have hlocal : s * f Coordinates.mu * s = f corePi := by
    rw [← map_mul, ← map_mul, local_tauprime]
  have hbeta : beta * f Coordinates.mu = f Coordinates.mu * beta := by
    have ha := a.corePi_commute.eq
    change a.alpha * f corePi = f corePi * a.alpha at ha
    rw [← hlocal] at ha
    calc
      beta * f Coordinates.mu = s * (a.alpha * (s * f Coordinates.mu * s)) * s⁻¹ := by
        dsimp [beta]; group
      _ = s * ((s * f Coordinates.mu * s) * a.alpha) * s⁻¹ := by rw [ha]
      _ = f Coordinates.mu * beta := by
        rw [hsi]
        calc
          _ = (s*s) * f Coordinates.mu * beta := by dsimp [beta]; group
          _ = _ := by rw [hs, one_mul]

  let v : C D e := ⟨beta, mem_centralizer_singleton_iff.mpr hbeta⟩
  have hsp : s * f Coordinates.pi * s = f Coordinates.pi := by
    have h : Coordinates.taup * Coordinates.pi * Coordinates.taup = Coordinates.pi := by decide +kernel
    rw [← map_mul, ← map_mul, h]
  have hb : beta⁻¹ * f Coordinates.pi * beta =
      f (Coordinates.pi ^ (d.val+1) * (Coordinates.xi * Coordinates.mup)) := by
    calc
      _ = s * (a.alpha⁻¹ * (s * f Coordinates.pi * s) * a.alpha) * s := by
        simp only [beta, mul_inv_rev, hsi]; group
      _ = s * (a.alpha⁻¹ * f Coordinates.pi * a.alpha) * s := by rw [hsp]
      _ = s * f (Coordinates.pi * normalizedXi d) * s := by rw [a.pi_alpha]
      _ = _ := by rw [← map_mul, ← map_mul, local_beta_pi]
  have hv : v⁻¹ * pi D e * v = pi D e ^ (d.val+1) * (lift D e z * lift D e m) := by
    apply Subtype.ext
    simpa only [v, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, pi_val, lift,
      Local.liftWord_z, Local.liftWord_m, map_mul, map_pow, f] using hb
  have hh := congrArg (q D e) hv
  simp only [map_mul, map_inv, map_pow, q_lift, q_pi] at hh
  refine isConj_iff.mpr ⟨(q D e v)⁻¹, ?_⟩
  simpa only [inv_inv, map_mul, map_pow, into_p] using hh

public theorem conj_lt_of_nu {b d : Bit} (n : NuRelations D e b d) :
    IsConj (p D e) (into D e (l*t)) := by
  obtain ⟨v, hv, _⟩ := nu_conj_p D e n
  have h : IsConj (p D e) (into D e (p₀ ^ (b.val+1) * (l*t))) :=
    isConj_iff.mpr ⟨v⁻¹, by simpa only [inv_inv, into_p] using hv⟩
  exact h.trans (isConj_into D e _ _ _ (Local.m_shift_lt b))

public theorem conj_zm_of_alpha {d : Bit} (a : AlphaRelations D e d) :
    IsConj (p D e) (into D e (z*m)) :=
  (alpha_conj_p D e a).trans (isConj_into D e _ _ _ (Local.t_shift_zm d))

public theorem not_conj_zlt_of_nu
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    {b d : Bit} (n : NuRelations D e b d) :
    ¬ IsConj (p D e) (into D e (z*l*t)) := by
  obtain ⟨v, hv, hc⟩ := nu_conj_p D e n
  let x := p₀ ^ (d.val+1) * z
  let y := (p₀ ^ (b.val+1) * (l*t)) * (p₀ ^ d.val * z)
  have heq : x = p₀ * (p₀ ^ d.val * z) := by
    fin_cases d <;> decide +kernel
  have hfix : v⁻¹ * into D e (p₀ ^ d.val * z) * v = into D e (p₀ ^ d.val * z) := by
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have hn : IsConj (into D e x) (into D e y) := by
    refine isConj_iff.mpr ⟨v⁻¹, ?_⟩
    rw [inv_inv, heq, map_mul]
    calc
      _ = (v⁻¹ * into D e p₀ * v) * (v⁻¹ * into D e (p₀ ^ d.val * z) * v) := by group
      _ = _ := by rw [hv, hfix, ← map_mul]
  intro h
  have hx : IsConj (p D e) (into D e x) :=
    (h.trans (isConj_into D e _ _ _ (Local.m_shift_after b d))).trans hn.symm
  obtain ⟨T, hT⟩ := exists_quotient_sylow_eq_centralizer D e hfusion
  have hr : (into D e).range = (T : Subgroup (Q D e)) :=
    (into_range D e hfusion).trans hT.symm
  have hp : IsConj (into D e p₀) (into D e x) := by rwa [into_p]
  exact (Local.central_before d).2
    (central_model_isConj_eq T (into D e) (into_injective D e) hr x
      (Local.central_before d).1 hp)

/-- The initial actor excludes tau by conjugating it into the center of T. -/
public theorem not_conj_t_of_seed
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    {b : Bit} (n : NuSeedRelations D e b) :
    ¬ IsConj (p D e) (into D e t) := by
  let v : C D e := ⟨n.nu, mem_centralizer_singleton_iff.mpr n.mu_commute.eq⟩
  let x : Model := p₀ * (p₀ ^ b.val * l)
  have hv : v⁻¹ * lift D e t * v =
      pi D e * mu D e * (pi D e ^ b.val * lift D e l) := by
    apply Subtype.ext
    simpa only [v, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
      pi_val, mu, lift, Local.liftWord_t, Local.liftWord_l, normalizedLam,
      map_mul, map_pow, LocalData.a10NoncentralInvolution, Coordinates.mu] using n.tau_nu
  have hc : IsConj (into D e t) (into D e x) := by
    have hh := congrArg (q D e) hv
    simp only [map_mul, map_inv, map_pow, q_mu, mul_one, q_lift, q_pi] at hh
    exact isConj_iff.mpr ⟨(q D e v)⁻¹, by
      simpa only [inv_inv, x, map_mul, map_pow] using hh⟩
  have hx : (∀ y : Model, x*y = y*x) ∧ x ≠ p₀ := by
    dsimp [x]
    fin_cases b <;> decide +kernel
  intro h
  obtain ⟨T, hT⟩ := exists_quotient_sylow_eq_centralizer D e hfusion
  have hr : (into D e).range = (T : Subgroup (Q D e)) :=
    (into_range D e hfusion).trans hT.symm
  have hp : IsConj (into D e p₀) (into D e x) := by
    rw [into_p]
    exact h.trans hc
  exact hx.2 (central_model_isConj_eq T (into D e) (into_injective D e) hr x hx.1 hp)

variable {D e}

/-- A seed fixes one of the two xi markings. This does not prescribe the marking
selected by alpha, and so does not establish the final normalization in 4.1. -/
public theorem exists_nuRelations_of_seed {b : Bit} (n : NuSeedRelations D e b) :
    ∃ d : Bit, Nonempty (NuRelations D e b d) := by
  let f := D.a10ModelEmbedding e
  let A := MulAut.conj n.nu⁻¹
  have hfix : ∃ d : Bit, A (f (normalizedXi d)) = f (normalizedXi d) := by
    rcases n.xi_conjugation (d := 0) with h | h
    · exact ⟨0, h⟩
    · refine ⟨1, ?_⟩
      have he : normalizedXi 1 = Coordinates.pi * normalizedXi 0 := by decide +kernel
      have hl : (Coordinates.pi * Coordinates.tau * normalizedLam b) *
          (coreTau b * normalizedXi 0) = normalizedXi 1 := by
        fin_cases b <;> decide +kernel
      have hp : A (f Coordinates.pi) = f (Coordinates.pi * Coordinates.tau * normalizedLam b) := by
        simpa only [A, MulAut.conj_apply, inv_inv] using n.pi_nu
      change A (f (normalizedXi 0)) = f (coreTau b * normalizedXi 0) at h
      calc
        A (f (normalizedXi 1)) = A (f Coordinates.pi) * A (f (normalizedXi 0)) := by
          rw [he, map_mul, map_mul]
        _ = f (normalizedXi 1) := by rw [hp, h, ← map_mul, hl]
  obtain ⟨d, hd⟩ := hfix
  refine ⟨d, ⟨{
    nu := n.nu
    cube := n.cube
    mu_commute := n.mu_commute
    xi_commute := ?_
    pi_nu := n.corePi_conjugation
    tau_nu := n.coreTau_conjugation }⟩⟩
  change n.nu * f (normalizedXi d) = f (normalizedXi d) * n.nu
  have hd' : n.nu⁻¹ * f (normalizedXi d) * n.nu = f (normalizedXi d) := by
    simpa only [A, MulAut.conj_apply, inv_inv] using hd
  calc
    _ = n.nu * (n.nu⁻¹ * f (normalizedXi d) * n.nu) := by rw [hd']
    _ = _ := by group

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.SourceFusion

module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.Inputs

/-!
# Separate actors and Held's conjugate adjustment

The two records retain all the actions on printed pp.232--233, before
commutation is established. Conjugation by pi fixes every displayed local
mark, so replacing v by v^pi preserves its order, all three centralizing
actions, both nontrivial conjugation actions and inversion by mu-prime.
The final constructor uses either of these choices once commutation is proved.
No actor existence or commuting-choice assertion is assumed or proved here.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 4.1--4.2 and 5.1, pp.232--236.
Conjugation is x^g = g⁻¹*x*g. The starting proof was recovered from
Scratch/HeldCompatibleActors/Relations.lean in attempt db016a2d98d7460390ff3878cecf9c73.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The first actor after the normalization on printed p.233. -/
public structure UActor where
  u : G
  order : orderOf u = 3
  mu_u : u⁻¹ * mu D e * u = lam D e
  lam_u : u⁻¹ * lam D e * u = mu D e * lam D e
  tau'_commute : Commute u (tau' D e)
  mu'_inverts : mu' D e * u * mu' D e = u⁻¹

/-- The actor of 4.1, before the commuting choice in 5.1. -/
public structure VActor where
  v : G
  order : orderOf v = 3
  mu_commute : Commute v (mu D e)
  lam_commute : Commute v (lam D e)
  xi_commute : Commute v (xi D e)
  pi_v : v⁻¹ * pi D e * v = pi D e * tau D e * lam D e
  tau_v : v⁻¹ * tau D e * v = pi D e * mu D e * lam D e
  mu'_inverts : mu' D e * v * mu' D e = v⁻¹

private theorem pi_conj_element (i : Fin 8) :
    (MulAut.conj (pi D e)⁻¹) (element D e i) = element D e i := by
  simp only [MulAut.conj_apply, inv_inv]
  rw [mul_assoc, ← (commute_pi D e i).eq, inv_mul_cancel_left]

/-- Held's replacement v by v^pi preserves every relation in 4.1. -/
public noncomputable def VActor.conjugatePi (b : VActor D e) : VActor D e := by
  let f := MulAut.conj (pi D e)⁻¹
  have hp : f (pi D e) = pi D e := pi_conj_element D e 0
  have hm : f (mu D e) = mu D e := pi_conj_element D e 1
  have hmp : f (mu' D e) = mu' D e := pi_conj_element D e 2
  have ht : f (tau D e) = tau D e := pi_conj_element D e 3
  have hl : f (lam D e) = lam D e := pi_conj_element D e 6
  have hx : f (xi D e) = xi D e := pi_conj_element D e 7
  refine {
    v := f b.v
    order := (f.orderOf_eq b.v).trans b.order
    mu_commute := ?_
    lam_commute := ?_
    xi_commute := ?_
    pi_v := ?_
    tau_v := ?_
    mu'_inverts := ?_ }
  · simpa only [MulEquiv.coe_toMonoidHom, hm] using b.mu_commute.map f.toMonoidHom
  · simpa only [MulEquiv.coe_toMonoidHom, hl] using b.lam_commute.map f.toMonoidHom
  · simpa only [MulEquiv.coe_toMonoidHom, hx] using b.xi_commute.map f.toMonoidHom
  · simpa only [map_mul, map_inv, hp, ht, hl] using congrArg f b.pi_v
  · simpa only [map_mul, map_inv, hp, hm, ht, hl] using congrArg f b.tau_v
  · simpa only [map_mul, map_inv, hmp] using congrArg f b.mu'_inverts

public theorem VActor.conjugatePi_v (b : VActor D e) :
    (b.conjugatePi D e).v = (pi D e)⁻¹ * b.v * pi D e := by
  simp only [conjugatePi, MulAut.conj_apply, inv_inv]

/-- Assembly keeps both independently constructed actors and requires their
actual commutation. Existence is not asserted by this definition. -/
public def compatibleActorsOfCommute (a : UActor D e) (b : VActor D e)
    (h : Commute a.u b.v) : CompatibleActors D e where
  u := a.u
  v := b.v
  u_order := a.order
  v_order := b.order
  u_v_commute := h
  mu_u := a.mu_u
  lam_u := a.lam_u
  u_tau'_commute := a.tau'_commute
  mu'_u := a.mu'_inverts
  v_mu_commute := b.mu_commute
  v_lam_commute := b.lam_commute
  v_xi_commute := b.xi_commute
  pi_v := b.pi_v
  tau_v := b.tau_v
  mu'_v := b.mu'_inverts

/-- The two choices in Held 5.1 give the same required action record. This
implication leaves existence of the actors and of the commuting choice explicit. -/
public theorem compatibleActors_of_commuting_choice (a : UActor D e) (b : VActor D e)
    (h : Commute a.u b.v ∨ Commute a.u ((pi D e)⁻¹ * b.v * pi D e)) :
    Nonempty (CompatibleActors D e) := by
  rcases h with h | h
  · exact ⟨compatibleActorsOfCommute D e a b h⟩
  · exact ⟨compatibleActorsOfCommute D e a (b.conjugatePi D e)
      (by simpa only [VActor.conjugatePi_v] using h)⟩

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

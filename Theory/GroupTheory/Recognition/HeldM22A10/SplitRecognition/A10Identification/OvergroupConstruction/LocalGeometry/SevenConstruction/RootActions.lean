module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SourceContracts
import Mathlib.Tactic.Group

/-!
# Root actions and the ambient crossing-centralizer reduction

From the corrected six-point source data, `uv` has order three and both
`mu'` and `xi` invert it. The coordinate action then gives Held's three
identities in Lemma 5.8. Conjugation by `pi * mu * tau * lambda`, followed
by conjugation by `tau'`, identifies the full ambient crossing centralizer
with `C_G({uv, mu', xi})`. No subgroup of an assumed S7 is substituted for
an ambient centralizer, and no recognition theorem is used here.

Source: D. Held, *A Characterization of some multiply transitive permutation
groups, I*, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.8 and the start of 5.11, pp.238–239.
-/

open Subgroup Equiv
open Theory.GroupTheory.HeldM22A10
open Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction

noncomputable section

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer) (L : Source.SixLocalData D e)

public theorem root_cube : (L.u * L.v) ^ 3 = 1 := by
  rw [L.u_v_commute.mul_pow]
  rw [← L.u_order, pow_orderOf_eq_one, L.u_order, ← L.v_order, pow_orderOf_eq_one]
  exact one_mul 1

public theorem coordinate_inv (i : Fin 8) (hi : i ≠ 5) : (element D e i)⁻¹ = element D e i :=
  inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using element_square D e i hi)

public theorem mu'_root : mu' D e * (L.u * L.v) * mu' D e = (L.u * L.v)⁻¹ := by
  have hs : mu' D e * mu' D e = 1 := by
    simpa only [pow_two] using element_square D e 2 (by decide)
  calc
    _ = (mu' D e * L.u * mu' D e) * (mu' D e * L.v * mu' D e) := by
      simpa only [MulAut.conj_apply, inv_eq_of_mul_eq_one_left hs] using
        map_mul (MulAut.conj (mu' D e)) L.u L.v
    _ = L.u⁻¹ * L.v⁻¹ := by rw [L.mu'_u, L.mu'_v]
    _ = (L.u * L.v)⁻¹ := by rw [mul_inv_rev, L.u_v_commute.inv_inv.eq]

public theorem root_ne_one : L.u * L.v ≠ 1 := by
  intro h
  have hu : L.u = L.v⁻¹ := (inv_eq_of_mul_eq_one_left h).symm
  have hc : Commute L.u (mu D e) := hu ▸ L.v_mu_commute.inv_left
  have heq : lam D e = mu D e := by
    rw [← L.mu_u, hc.inv_left.eq, inv_mul_cancel_right]
  have hmodel := D.a10ModelEmbedding_injective e heq
  exact (by decide +kernel : modelElement 6 ≠ modelElement 1) hmodel

public theorem root_order : orderOf (L.u * L.v) = 3 :=
  orderOf_eq_prime (root_cube D e L) (root_ne_one D e L)

public theorem xi_root : xi D e * (L.u * L.v) * xi D e = (L.u * L.v)⁻¹ := by
  have hc := (L.root_centralizes _ L.mu'_xi_mem).symm
  have hfix : (mu' D e * xi D e) * (L.u * L.v) * (mu' D e * xi D e)⁻¹ =
      L.u * L.v := by rw [hc.eq, mul_inv_cancel_right]
  calc
    _ = (mu' D e)⁻¹ * ((mu' D e * xi D e) * (L.u * L.v) *
        (mu' D e * xi D e)⁻¹) * mu' D e := by
      calc
        _ = xi D e * (L.u * L.v) * (xi D e)⁻¹ := by
          rw [show (xi D e)⁻¹ = xi D e from coordinate_inv D e 7 (by decide)]
        _ = _ := by group
    _ = (mu' D e)⁻¹ * (L.u * L.v) * mu' D e := by rw [hfix]
    _ = (L.u * L.v)⁻¹ := by
      rw [coordinate_inv D e 2 (by decide), mu'_root D e L]

public theorem xi_u : xi D e * L.u * xi D e = L.u⁻¹ * L.v := by
  have hx := xi_root D e L
  have hm := map_mul (MulAut.conj (xi D e)) L.u L.v
  simp only [MulAut.conj_apply, coordinate_inv D e 7 (by decide)] at hm
  have hv : xi D e * L.v * xi D e = L.v := by
    simpa only [coordinate_inv D e 7 (by decide)] using
      (show xi D e * L.v * (xi D e)⁻¹ = L.v by
        rw [L.v_xi_commute.symm.eq, mul_inv_cancel_right])
  rw [hm, hv, mul_inv_rev] at hx
  have hpow : L.v⁻¹ * L.v⁻¹ = L.v := by
    have hv3 : L.v ^ 3 = 1 := by rw [← L.v_order, pow_orderOf_eq_one]
    calc
      _ = L.v ^ 3 * (L.v⁻¹ * L.v⁻¹) := by rw [hv3, one_mul]
      _ = L.v := by group
  calc
    _ = (L.v⁻¹ * L.u⁻¹) * L.v⁻¹ := (eq_mul_inv_iff_mul_eq.mpr hx)
    _ = L.u⁻¹ * (L.v⁻¹ * L.v⁻¹) := by rw [L.u_v_commute.inv_inv.eq.symm, mul_assoc]
    _ = _ := by rw [hpow]

public theorem tau'_xi : tau' D e * xi D e * tau' D e = mu' D e * xi D e := by
  have h : modelElement 4 * modelElement 7 * modelElement 4 =
      modelElement 2 * modelElement 7 := by decide +kernel
  simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) h

public theorem tau'_v : tau' D e * L.v * tau' D e = (L.u * L.v)⁻¹ := by
  let t := MulAut.conj (tau' D e)
  let x := MulAut.conj (xi D e)
  have htu : t L.u = L.u := by
    change tau' D e * L.u * (tau' D e)⁻¹ = L.u
    rw [L.u_tau'_commute.symm.eq, mul_inv_cancel_right]
  have htx : t (xi D e) = mu' D e * xi D e := by
    simpa only [t, MulAut.conj_apply, coordinate_inv D e 4 (by decide)] using tau'_xi D e
  have hxu : x L.u = L.u⁻¹ * L.v := by
    simpa only [x, MulAut.conj_apply, coordinate_inv D e 7 (by decide)] using xi_u D e L
  have h : L.u⁻¹ * t L.v = (L.u⁻¹ * L.v)⁻¹ := by
    calc
      _ = t (L.u⁻¹ * L.v) := by rw [map_mul, map_inv, htu]
      _ = t (x L.u) := by rw [hxu]
      _ = (mu' D e * xi D e) * L.u * (mu' D e * xi D e)⁻¹ := by
        change t (xi D e * L.u * (xi D e)⁻¹) = _
        rw [map_mul, map_mul, map_inv, htu, htx]
      _ = xi D e * (mu' D e * L.u * mu' D e) * (xi D e)⁻¹ := by
        rw [(mu'_commute_xi D e).eq, mul_inv_rev,
          coordinate_inv D e 2 (by decide)]
        group
      _ = x L.u⁻¹ := by rw [L.mu'_u]; rfl
      _ = (L.u⁻¹ * L.v)⁻¹ := by rw [map_inv, hxu]
  have hu : L.u * L.u = L.u⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [pow_succ, pow_zero, one_mul] using
      (show L.u ^ 3 = 1 by rw [← L.u_order, pow_orderOf_eq_one])
  have ht : t L.v = (L.u * L.v)⁻¹ := by
    calc
      _ = L.u * (L.u⁻¹ * t L.v) := by group
      _ = L.u * (L.u⁻¹ * L.v)⁻¹ := by rw [h]
      _ = (L.u * L.u) * L.v⁻¹ := by
        rw [mul_inv_rev, inv_inv, L.u_v_commute.inv_right.symm.eq, ← mul_assoc]
      _ = (L.u * L.v)⁻¹ := by rw [hu, mul_inv_rev, L.u_v_commute.inv_inv.eq]
  simpa only [t, MulAut.conj_apply, coordinate_inv D e 4 (by decide)] using ht

public theorem tau'_root : tau' D e * (L.u * L.v) * tau' D e = L.v⁻¹ := by
  have hm := map_mul (MulAut.conj (tau' D e)) L.u L.v
  simp only [MulAut.conj_apply, coordinate_inv D e 4 (by decide)] at hm
  have hu : tau' D e * L.u * tau' D e = L.u := by
    simpa only [coordinate_inv D e 4 (by decide)] using
      (show tau' D e * L.u * (tau' D e)⁻¹ = L.u by
        rw [L.u_tau'_commute.symm.eq, mul_inv_cancel_right])
  rw [hm, hu, tau'_v D e L, mul_inv_rev, L.u_v_commute.inv_inv.eq.symm,
    mul_inv_cancel_left]

public def crossingConjugator : G := pi D e * mu D e * tau D e * lam D e

public theorem crossingConjugator_inv : (crossingConjugator D e)⁻¹ = crossingConjugator D e := by
  have h : (modelElement 0 * modelElement 1 * modelElement 3 * modelElement 6)⁻¹ =
      modelElement 0 * modelElement 1 * modelElement 3 * modelElement 6 := by decide +kernel
  simpa only [crossingConjugator, element, map_mul, map_inv] using
    congrArg (D.a10ModelEmbedding e) h

public theorem crossingConjugator_mu' :
    (MulAut.conj (crossingConjugator D e)) (mu' D e) = pi D e * mu D e * mu' D e := by
  rw [MulAut.conj_apply]
  have h : (modelElement 0 * modelElement 1 * modelElement 3 * modelElement 6) *
      modelElement 2 * (modelElement 0 * modelElement 1 * modelElement 3 * modelElement 6)⁻¹ =
      modelElement 0 * modelElement 1 * modelElement 2 := by decide +kernel
  simpa only [crossingConjugator, element, map_mul, map_inv] using
    congrArg (D.a10ModelEmbedding e) h

public theorem crossingConjugator_middle :
    (MulAut.conj (crossingConjugator D e)) (pi D e * mu D e * mu' D e) = mu' D e := by
  rw [MulAut.conj_apply]
  have h : (modelElement 0 * modelElement 1 * modelElement 3 * modelElement 6) *
      (modelElement 0 * modelElement 1 * modelElement 2) *
      (modelElement 0 * modelElement 1 * modelElement 3 * modelElement 6)⁻¹ = modelElement 2 :=
    by decide +kernel
  simpa only [crossingConjugator, element, map_mul, map_inv] using
    congrArg (D.a10ModelEmbedding e) h

public theorem crossingConjugator_xi :
    (MulAut.conj (crossingConjugator D e)) (xi D e) = xi D e := by
  rw [MulAut.conj_apply]
  have h : (modelElement 0 * modelElement 1 * modelElement 3 * modelElement 6) *
      modelElement 7 * (modelElement 0 * modelElement 1 * modelElement 3 * modelElement 6)⁻¹ =
      modelElement 7 := by decide +kernel
  simpa only [crossingConjugator, element, map_mul, map_inv] using
    congrArg (D.a10ModelEmbedding e) h

public theorem crossingConjugator_v :
    (MulAut.conj (crossingConjugator D e)) L.v = L.v * (pi D e * mu D e) := by
  have hm : (MulAut.conj L.v⁻¹) (mu D e) = mu D e := by
    rw [MulAut.conj_apply, inv_inv]
    rw [L.v_mu_commute.inv_left.eq, inv_mul_cancel_right]
  have hl : (MulAut.conj L.v⁻¹) (lam D e) = lam D e := by
    rw [MulAut.conj_apply, inv_inv]
    rw [L.v_lam_commute.inv_left.eq, inv_mul_cancel_right]
  have hp : (MulAut.conj L.v⁻¹) (pi D e) = pi D e * tau D e * lam D e := by
    simpa only [MulAut.conj_apply, inv_inv] using L.pi_v
  have ht : (MulAut.conj L.v⁻¹) (tau D e) = pi D e * mu D e * lam D e := by
    simpa only [MulAut.conj_apply, inv_inv] using L.tau_v
  have h : (MulAut.conj L.v⁻¹) (crossingConjugator D e) = tau D e * lam D e := by
    unfold crossingConjugator
    rw [map_mul, map_mul, map_mul, hp, hm, ht, hl]
    have hc : (modelElement 0 * modelElement 3 * modelElement 6) * modelElement 1 *
        (modelElement 0 * modelElement 1 * modelElement 6) * modelElement 6 =
        modelElement 3 * modelElement 6 := by decide +kernel
    simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) hc
  have hp : (tau D e * lam D e) * crossingConjugator D e = pi D e * mu D e := by
    have hc : (modelElement 3 * modelElement 6) *
        (modelElement 0 * modelElement 1 * modelElement 3 * modelElement 6) =
        modelElement 0 * modelElement 1 := by decide +kernel
    simpa only [element, map_mul, crossingConjugator] using congrArg (D.a10ModelEmbedding e) hc
  change crossingConjugator D e * L.v * (crossingConjugator D e)⁻¹ = _
  simp only [MulAut.conj_apply, inv_inv] at h
  rw [crossingConjugator_inv]
  calc
    _ = L.v * (L.v⁻¹ * crossingConjugator D e * L.v) * crossingConjugator D e := by group
    _ = _ := by rw [h, mul_assoc, hp]

public theorem crossingConjugator_first :
    (MulAut.conj (crossingConjugator D e)) (L.v * mu' D e) = L.v * mu' D e := by
  rw [map_mul, crossingConjugator_v D e L, crossingConjugator_mu', mul_assoc]
  congr 1
  have hc : (modelElement 0 * modelElement 1) *
      (modelElement 0 * modelElement 1 * modelElement 2) = modelElement 2 := by decide +kernel
  simpa only [element, map_mul] using congrArg (D.a10ModelEmbedding e) hc

private theorem centralizer_triple_mul (a b c : G) :
    centralizer ({a * b, b, c} : Set G) = centralizer ({a, b, c} : Set G) := by
  ext y
  simp only [mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp]
  constructor
  · rintro ⟨hab, hb, hc⟩
    refine ⟨?_, hb, hc⟩
    change Commute a y
    simpa using (show Commute (a * b) y from hab).mul_left
      (show Commute b y from hb).inv_left
  · rintro ⟨ha, hb, hc⟩
    exact ⟨(show Commute a y from ha).mul_left (show Commute b y from hb), hb, hc⟩

private def centralizerTripleEquiv {H : Type*} [Group H] (f : G ≃* H) (a b c : G) :
    centralizer ({a, b, c} : Set G) ≃* centralizer ({f a, f b, f c} : Set H) where
  toFun y := ⟨f y, by
    rw [mem_centralizer_iff] at *
    intro z hz
    rcases hz with rfl | rfl | rfl
    all_goals simpa only [map_mul] using congrArg f (y.property _ (by simp))⟩
  invFun y := ⟨f.symm y, by
    rw [mem_centralizer_iff]
    intro z hz
    apply f.injective
    simp only [map_mul, f.apply_symm_apply]
    apply y.property
    rcases hz with rfl | rfl | rfl <;> simp⟩
  left_inv y := by ext; exact f.symm_apply_apply y
  right_inv y := by ext; exact f.apply_symm_apply y
  map_mul' a b := Subtype.ext (map_mul f (a : G) (b : G))

public def crossingToV : Source.crossingCentralizer D e L ≃*
    centralizer ({L.v, mu' D e, xi D e} : Set G) :=
  (centralizerTripleEquiv (MulAut.conj (crossingConjugator D e))
    (L.v * mu' D e) (pi D e * mu D e * mu' D e) (xi D e)).trans
    (MulEquiv.subgroupCongr (by rw [crossingConjugator_first D e L,
      crossingConjugator_middle, crossingConjugator_xi, centralizer_triple_mul]))

public theorem tau'_mu' : (MulAut.conj (tau' D e)) (mu' D e) = mu' D e := by
  rw [MulAut.conj_apply]
  have h : modelElement 4 * modelElement 2 * (modelElement 4)⁻¹ = modelElement 2 :=
    by decide +kernel
  simpa only [element, map_mul, map_inv] using congrArg (D.a10ModelEmbedding e) h

private theorem centralizer_triple_inv_mul (a b c : G) :
    centralizer ({a⁻¹, b, b * c} : Set G) = centralizer ({a, b, c} : Set G) := by
  ext y
  simp only [mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨ha, hb, hc⟩
    refine ⟨?_, hb, ?_⟩
    · exact (Commute.inv_left_iff.mp (show Commute a⁻¹ y from ha)).eq
    · change Commute c y
      simpa using (show Commute b y from hb).inv_left.mul_left
        (show Commute (b * c) y from hc)
  · rintro ⟨ha, hb, hc⟩
    exact ⟨(show Commute a y from ha).inv_left,
      hb, (show Commute b y from hb).mul_left (show Commute c y from hc)⟩

public def crossingToRoot : Source.crossingCentralizer D e L ≃*
    centralizer ({L.u * L.v, mu' D e, xi D e} : Set G) :=
  (crossingToV D e L).trans
    ((centralizerTripleEquiv (MulAut.conj (tau' D e)) L.v (mu' D e) (xi D e)).trans
      (MulEquiv.subgroupCongr (by
        have hv : (MulAut.conj (tau' D e)) L.v = (L.u * L.v)⁻¹ := by
          simpa only [MulAut.conj_apply, coordinate_inv D e 4 (by decide)] using tau'_v D e L
        have hx : (MulAut.conj (tau' D e)) (xi D e) = mu' D e * xi D e := by
          simpa only [MulAut.conj_apply, coordinate_inv D e 4 (by decide)] using tau'_xi D e
        rw [hv, tau'_mu', hx, centralizer_triple_inv_mul])))

end
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction

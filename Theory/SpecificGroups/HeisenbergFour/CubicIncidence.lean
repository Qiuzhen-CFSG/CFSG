module

public import Theory.SpecificGroups.HeisenbergFour.CubicIncidence.BinaryJoins
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicEdgeIncidence

/-!
# Cubic-pair incidence in the Heisenberg-four extension

Conjugate the first cubic to the complement. Its A₄ neighbors lie on two
coordinate axes, each a single orbit under that complement. Orbit exclusion
therefore places the other cubics on opposite axes. Their literal join is
binary tetrahedral, and hence isomorphic to the matrix group SL₂(3).
The actual coordinate-model equivalence transports the conclusion to the
published GF(4) model without any ambient recognition assumption.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.6(1), p.264.
-/

public section
namespace HeisenbergFour.CubicIncidence
open Subgroup alternatingGroup.FiveLocalGeometry.CubicEdgeIncidence

private noncomputable def joinMapEquiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (P Q : Subgroup H) :
    ↥(P ⊔ Q) ≃* ↥(P.map e.toMonoidHom ⊔ Q.map e.toMonoidHom) :=
  ((P ⊔ Q).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_sup _ _ _))

private theorem cross_of_not_orbit (i j : Four × Four) (hi : Axis i) (hj : Axis j)
    (hout : C j ∉ cubicOrbit (C origin) (C i)) : Cross i j := by
  by_contra hc
  obtain ⟨n, hn⟩ := same_axis_conjugator i j hi hj hc
  apply hout
  have hm : base ^ n.val ∈ C origin := by
    rw [← gen_origin]
    exact pow_mem (mem_zpowers _) _
  refine ⟨⟨base ^ n.val, hm⟩, ?_⟩
  change (zpowers (gen i)).map (MulAut.conj (base ^ n.val)).toMonoidHom = C j
  rw [MonoidHom.map_zpowers]
  change zpowers (base ^ n.val * gen i * (base ^ n.val)⁻¹) = C j
  rw [hn]
  rfl

/-- The intrinsic theorem in the executable coordinates. -/
theorem coordinate_cubic_pair (P Q R : Subgroup CoordinateModel)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3) (hR : Nat.card R = 3)
    (ePQ : ↥(P ⊔ Q) ≃* alternatingGroup (Fin 4))
    (ePR : ↥(P ⊔ R) ≃* alternatingGroup (Fin 4))
    (hout : R ∉ cubicOrbit P Q) :
    Nonempty (↥(Q ⊔ R) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  obtain ⟨p, rfl⟩ := cubic_representative P hP
  let e := MulAut.conj (shift p)⁻¹
  have hp : (C p).map e.toMonoidHom = C origin := map_C_to_origin p
  obtain ⟨q, hq⟩ := cubic_representative (Q.map e.toMonoidHom)
    (by rw [card_map_of_injective e.injective, hQ])
  obtain ⟨r, hr⟩ := cubic_representative (R.map e.toMonoidHom)
    (by rw [card_map_of_injective e.injective, hR])
  have hpq : (C p).map e.toMonoidHom ⊔ Q.map e.toMonoidHom = C origin ⊔ C q := by
    rw [hp, hq]
  have hpr : (C p).map e.toMonoidHom ⊔ R.map e.toMonoidHom = C origin ⊔ C r := by
    rw [hp, hr]
  have haq : Axis q := axis_of_alternating q
    ((MulEquiv.subgroupCongr hpq).symm.trans ((joinMapEquiv e (C p) Q).symm.trans ePQ))
  have har : Axis r := axis_of_alternating r
    ((MulEquiv.subgroupCongr hpr).symm.trans ((joinMapEquiv e (C p) R).symm.trans ePR))
  have ho : C r ∉ cubicOrbit (C origin) (C q) := by
    rw [← hp, ← hq, ← hr, mem_cubicOrbit_map_iff]
    exact hout
  obtain ⟨d⟩ := cross_join_equiv q r (cross_of_not_orbit q r haq har ho)
  have hqr : Q.map e.toMonoidHom ⊔ R.map e.toMonoidHom = C q ⊔ C r := by rw [hq, hr]
  exact ⟨(joinMapEquiv e Q R).trans ((MulEquiv.subgroupCongr hqr).trans d)⟩

/-- The literal GF(4) model: two A₄ neighbors in different P-orbits generate SL₂(3). -/
theorem cubic_pair_SL23 (P Q R : Subgroup Model)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3) (hR : Nat.card R = 3)
    (ePQ : Nonempty (↥(P ⊔ Q) ≃* alternatingGroup (Fin 4)))
    (ePR : Nonempty (↥(P ⊔ R) ≃* alternatingGroup (Fin 4)))
    (hout : R ∉ cubicOrbit P Q) :
    Nonempty (↥(Q ⊔ R) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  let e := modelEquiv.symm
  obtain ⟨d⟩ := coordinate_cubic_pair
    (P.map e.toMonoidHom) (Q.map e.toMonoidHom) (R.map e.toMonoidHom)
    (by rw [card_map_of_injective e.injective, hP])
    (by rw [card_map_of_injective e.injective, hQ])
    (by rw [card_map_of_injective e.injective, hR])
    ((joinMapEquiv e P Q).symm.trans ePQ.some)
    ((joinMapEquiv e P R).symm.trans ePR.some)
    (by rwa [mem_cubicOrbit_map_iff])
  exact ⟨(joinMapEquiv e Q R).trans d⟩

end HeisenbergFour.CubicIncidence

module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry

/-!
# The surviving high-rank first-stage actor

At corank two, the full A₀ core and the transvection hyperplane in the A₁
core contradict the pure-summand fixed-space restriction. The arbitrary
catalogue conjugator may swap the summands, so both pure obstructions are
transported. The remaining A₂ actor has fixed dimension two and core
dimension six, on the same coordinate action.
Source: Aschbacher--Smith, H.9.3 and 12.1.8, printed pp.391--392,793.
-/

public noncomputable section
open BinaryNaturalDual BinaryNaturalDual.FourActors BinaryLinear.OuterCyclic
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.FourActors
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry
variable (d : CoordinateAction 4)

private theorem obstruction_transport (A : Subgroup M) (a : M) (U : Submodule (ZMod 2) V)
    (h : U ⊓ actorCore d A 2 ≤ actorFixed d (A ⊓ inner)) :
    U.map (action d a).toLinearMap ⊓
      actorCore d (A.map (MulAut.conj a).toMonoidHom) 2 ≤
        actorFixed d (A.map (MulAut.conj a).toMonoidHom ⊓ inner) := by
  have hh := Submodule.map_mono (f := (action d a).toLinearMap) h
  rw [Submodule.map_inf _ (action d a).injective, core_conjugate,
    inner_fixed_conjugate] at hh
  exact hh


private theorem dual_map_outer (a : M) (ha : a ∉ BinaryNaturalDual.FourActors.inner) :
    dualSummand.map (action d a).toLinearMap = naturalSummand := by
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact outer_dual d a ha v hv
  · intro v hv
    refine ⟨action d a⁻¹ v, outer_natural d a⁻¹ (by simpa using ha) v hv, ?_⟩
    change (action d a * action d a⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

private theorem dual_obstruction_of_outer (A : Subgroup M) (a : M)
    (ha : a ∈ A) (hout : a ∉ BinaryNaturalDual.FourActors.inner)
    (hn : ¬ naturalSummand ⊓ actorCore d A 2 ≤ actorFixed d (A ⊓ inner)) :
    ¬ dualSummand ⊓ actorCore d A 2 ≤ actorFixed d (A ⊓ inner) := by
  intro hd
  have ht := obstruction_transport d A a dualSummand hd
  have he : A.map (MulAut.conj a).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha)
  rw [dual_map_outer d a hout, he] at ht
  exact hn ht

private theorem A0_natural_obstruction :
    ¬ naturalSummand ⊓ actorCore d A0 2 ≤ actorFixed d (A0 ⊓ inner) := by
  intro h
  have hcore : actorCore d A0 2 = ⊤ := (Parameters.A0_parameters d).2
  rw [hcore, inf_top_eq, inf_eq_left.mpr A0_le_inner, Parameters.A0_fixed] at h
  have ht : A0Plane = ⊤ := top_unique fun x _ => (h (by simp : (x, 0) ∈ naturalSummand)).1
  have hd := A0Plane_finrank
  rw [ht, finrank_top] at hd
  norm_num [X, BinaryLinear.OuterCyclic.Space] at hd

private theorem A0_dual_obstruction :
    ¬ dualSummand ⊓ actorCore d A0 2 ≤ actorFixed d (A0 ⊓ inner) := by
  intro h
  have hcore : actorCore d A0 2 = ⊤ := (Parameters.A0_parameters d).2
  rw [hcore, inf_top_eq, inf_eq_left.mpr A0_le_inner, Parameters.A0_fixed] at h
  have ht : A0Plane.dualAnnihilator = ⊤ :=
    top_unique fun f _ => (h (by simp : (0, f) ∈ dualSummand)).2
  have hb : A0Plane = ⊥ := Submodule.dualAnnihilator_eq_top_iff.mp ht
  have hd := A0Plane_finrank
  rw [hb, finrank_bot] at hd
  contradiction

private theorem A1_natural_obstruction :
    ¬ naturalSummand ⊓ actorCore d A1 2 ≤ actorFixed d (A1 ⊓ inner) := by
  intro h
  let x : X := ![1,0,0,0]
  have hf : (x, (0 : Module.Dual (ZMod 2) X)) ∈ fixedSpace (action d r) := by
    simpa only [map_zero] using (A1Module.fixed_r_iff d x 0).mpr (by decide)
  have hc : (x, (0 : Module.Dual (ZMod 2) X)) ∈ actorCore d A1 2 := by
    rw [(Parameters.A1_parameters d).2.1]
    exact hf
  have hh := h ⟨by simp, hc⟩
  change (x, (0 : Module.Dual (ZMod 2) X)) ∈ actorFixed d B1 at hh
  rw [← show A1Module.dualCoordinates 0 = 0 from map_zero _] at hh
  obtain ⟨c,he⟩ := ((A1Module.inner_common_fixed d x 0).mp hh).1
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  norm_num [x] at h0 h1
  exact one_ne_zero (h0.trans h1.symm)


/-- At corank two the pure-core restriction leaves only the A₂ actor. -/
theorem coordinate_first_actor (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 16)
    (h : naturalSummand ⊓ actorCore d A 2 ≤ actorFixed d (A ⊓ inner)) :
    ∃ a : M, A.map (MulAut.conj a).toMonoidHom = A2 := by
  obtain ⟨i,a,he⟩ := PermutationCatalogue.actor_exhaustive A hcard
  have ht := obstruction_transport d A a naturalSummand h
  rw [he] at ht
  fin_cases i
  · by_cases ha : a ∈ BinaryNaturalDual.FourActors.inner
    · rw [natural_map_inner d a ha] at ht
      exact (A0_natural_obstruction d ht).elim
    · rw [natural_map_outer d a ha] at ht
      exact (A0_dual_obstruction d ht).elim
  · have hn := A1_natural_obstruction d
    have hd := dual_obstruction_of_outer d A1 transposition transposition_mem_A1
      transposition_outer hn
    by_cases ha : a ∈ BinaryNaturalDual.FourActors.inner
    · rw [natural_map_inner d a ha] at ht
      exact (hn ht).elim
    · rw [natural_map_outer d a ha] at ht
      exact (hd ht).elim
  · exact ⟨a,he⟩

private theorem action_equivariant (a b : M) (v : V) :
    action d a (d.representation b v) =
      d.representation (MulAut.conj a b) (action d a v) := by
  change d.representation a (d.representation b v) =
    d.representation (a * b * a⁻¹) (d.representation a v)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel_right]

/-- The surviving first-stage actor has a fixed plane and a six-dimensional core. -/
theorem coordinate_first_parameters (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 16)
    (h : naturalSummand ⊓ actorCore d A 2 ≤ actorFixed d (A ⊓ inner)) :
    Module.finrank (ZMod 2) (actorFixed d A) = 2 ∧
      Module.finrank (ZMod 2) (actorCore d A 2) = 6 := by
  obtain ⟨a,ha⟩ := coordinate_first_actor d A hcard h
  have hp := Parameters.A2_parameters d transposition_mem_A2
    (show transposition ∉ B2 from fun ht => transposition_outer ht.2)
  have hf : (actorFixed d A).map (action d a).toLinearMap =
      actorFixed d A2 := by
    rw [← ha]
    exact Transport.fixed_map d.representation d.representation (MulAut.conj a)
      (action d a) (action_equivariant d a) A
  have hfd := (Submodule.equivMapOfInjective (action d a).toLinearMap
    (action d a).injective (actorFixed d A)).finrank_eq
  rw [hf] at hfd
  have hcd := (Submodule.equivMapOfInjective (action d a).toLinearMap
    (action d a).injective (actorCore d A 2)).finrank_eq
  rw [core_conjugate,ha] at hcd
  exact ⟨hfd.trans hp.2.1,hcd.trans hp.2.2.2⟩

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry

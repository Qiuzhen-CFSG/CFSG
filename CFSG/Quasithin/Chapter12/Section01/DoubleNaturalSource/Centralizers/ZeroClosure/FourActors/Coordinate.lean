module
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFourActors

/-!
# The H.9.3 obstruction on both coordinate summands

For A₀ the corank-two core is the whole module, whereas its common fixed
spaces are proper planes. For A₁ its transvection fixes a natural hyperplane
which is not fixed by the inner actor. For A₂ the cyclic subgroup generated
by a transvection has index eight, so its fixed hyperplane lies in the
corank-three core and cannot lie in the common fixed plane.

An outer element in each outer actor transports the natural obstruction to
the dual summand. Both obstructions then transport through the arbitrary
conjugator in the genuine H.9.3 catalogue; no preservation of the natural
summand by that conjugator is assumed.

Source: Aschbacher--Smith, H.9.3, printed pp.391--392 (PDF pp.402--403),
and the final paragraph of12.1.7, printed p.792 (PDF p.809).
-/

public noncomputable section
open BinaryNaturalDual BinaryNaturalDual.FourActors
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.FourActors

variable (d : CoordinateAction 4)

private theorem conjugation_equivariant (a b : M) (v : V) :
    action d a (d.representation b v) =
      d.representation (MulAut.conj a b) (action d a v) := by
  change d.representation a (d.representation b v) =
    d.representation (a * b * a⁻¹) (d.representation a v)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel_right]

theorem core_conjugate (A : Subgroup M) (a : M) (k : ℕ) :
    (actorCore d A k).map (action d a).toLinearMap =
      actorCore d (A.map (MulAut.conj a).toMonoidHom) k := by
  let : Finite M := Finite.of_injective permutationEquiv permutationEquiv.injective
  exact Transport.core_map _ _ _ _ (conjugation_equivariant d a) A k

theorem inner_fixed_conjugate (A : Subgroup M) (a : M) :
    (actorFixed d (A ⊓ inner)).map (action d a).toLinearMap =
      actorFixed d (A.map (MulAut.conj a).toMonoidHom ⊓ inner) := by
  change (Representation.BinaryOffender.fixedSpace d.representation (A ⊓ BinaryNaturalDual.FourActors.inner)).map _ = _
  rw [Transport.fixed_map _ _ _ _ (conjugation_equivariant d a),
    Subgroup.map_inf _ _ _ (MulAut.conj a).injective]
  exact congrArg (fun B => Representation.BinaryOffender.fixedSpace d.representation
    (A.map (MulAut.conj a).toMonoidHom ⊓ B))
      (Subgroup.Normal.map_conj_eq BinaryNaturalDual.FourActors.inner a)

theorem natural_map_inner (a : M) (ha : a ∈ BinaryNaturalDual.FourActors.inner) :
    naturalSummand.map (action d a).toLinearMap = naturalSummand := by
  obtain ⟨g, rfl⟩ := ha
  ext v
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hx0 := (mem_naturalSummand x).mp hx
    apply (mem_naturalSummand _).mpr
    change (d.representation (MulAut.conj g) x).2 = 0
    rw [d.on_inner, naturalDualRepresentation_apply, hx0, map_zero]
  · intro hv
    refine ⟨(g.symm v.1, 0), by simp, ?_⟩
    change d.representation (MulAut.conj g) (g.symm v.1, 0) = v
    rw [d.on_inner, naturalDualRepresentation_apply, map_zero, LinearEquiv.apply_symm_apply]
    exact Prod.ext rfl ((mem_naturalSummand v).mp hv).symm

theorem natural_map_outer (a : M) (ha : a ∉ BinaryNaturalDual.FourActors.inner) :
    naturalSummand.map (action d a).toLinearMap = dualSummand := by
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact outer_natural d a ha v hv
  · intro v hv
    refine ⟨action d a⁻¹ v, outer_dual d a⁻¹ (by simpa using ha) v hv, ?_⟩
    change (action d a * action d a⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

theorem obstruction_transport (A : Subgroup M) (a : M) (U : Submodule (ZMod 2) V)
    (h : U ⊓ actorCore d A 3 ≤ actorFixed d (A ⊓ inner)) :
    U.map (action d a).toLinearMap ⊓
      actorCore d (A.map (MulAut.conj a).toMonoidHom) 3 ≤
        actorFixed d (A.map (MulAut.conj a).toMonoidHom ⊓ inner) := by
  have hh := Submodule.map_mono (f := (action d a).toLinearMap) h
  rw [Submodule.map_inf _ (action d a).injective, core_conjugate,
    inner_fixed_conjugate] at hh
  exact hh


private theorem core_mono (A : Subgroup M) {j k : ℕ} (hjk : j ≤ k) :
    actorCore d A j ≤ actorCore d A k :=
  generatedCore_le _ fun _ h => fixedSpace_le_generatedCore _ (h.trans hjk)

theorem dual_map_outer (a : M) (ha : a ∉ BinaryNaturalDual.FourActors.inner) :
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
    (hn : ¬ naturalSummand ⊓ actorCore d A 3 ≤ actorFixed d (A ⊓ inner)) :
    ¬ dualSummand ⊓ actorCore d A 3 ≤ actorFixed d (A ⊓ inner) := by
  intro hd
  have ht := obstruction_transport d A a dualSummand hd
  have he : A.map (MulAut.conj a).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha)
  rw [dual_map_outer d a hout, he] at ht
  exact hn ht

private theorem A0_natural_obstruction :
    ¬ naturalSummand ⊓ actorCore d A0 3 ≤ actorFixed d (A0 ⊓ inner) := by
  intro h
  have hcore : actorCore d A0 3 = ⊤ := top_unique (by
    rw [← (Parameters.A0_parameters d).2]
    exact core_mono d A0 (by decide))
  rw [hcore, inf_top_eq, inf_eq_left.mpr A0_le_inner, Parameters.A0_fixed] at h
  have ht : A0Plane = ⊤ := top_unique fun x _ => (h (by simp : (x, 0) ∈ naturalSummand)).1
  have hd := A0Plane_finrank
  rw [ht, finrank_top] at hd
  norm_num [X, BinaryLinear.OuterCyclic.Space] at hd

private theorem A0_dual_obstruction :
    ¬ dualSummand ⊓ actorCore d A0 3 ≤ actorFixed d (A0 ⊓ inner) := by
  intro h
  have hcore : actorCore d A0 3 = ⊤ := top_unique (by
    rw [← (Parameters.A0_parameters d).2]
    exact core_mono d A0 (by decide))
  rw [hcore, inf_top_eq, inf_eq_left.mpr A0_le_inner, Parameters.A0_fixed] at h
  have ht : A0Plane.dualAnnihilator = ⊤ :=
    top_unique fun f _ => (h (by simp : (0, f) ∈ dualSummand)).2
  have hb : A0Plane = ⊥ := Submodule.dualAnnihilator_eq_top_iff.mp ht
  have hd := A0Plane_finrank
  rw [hb, finrank_bot] at hd
  contradiction

private theorem A1_natural_obstruction :
    ¬ naturalSummand ⊓ actorCore d A1 3 ≤ actorFixed d (A1 ⊓ inner) := by
  intro h
  let x : X := ![1,0,0,0]
  have hf : (x, (0 : Module.Dual (ZMod 2) X)) ∈ fixedSpace (action d r) := by
    simpa only [map_zero] using (A1Module.fixed_r_iff d x 0).mpr (by decide)
  have hc : (x, (0 : Module.Dual (ZMod 2) X)) ∈ actorCore d A1 3 := by
    apply core_mono d A1 (by decide : 2 ≤ 3)
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

private theorem element_fixed_le_core (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 16) (b : A) (hb : b ≠ 1) :
    fixedSpace (action d b) ≤ actorCore d A 3 := by
  let : Finite M := Finite.of_injective permutationEquiv permutationEquiv.injective
  have hb2 : b ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 A) b
  have hc : Nat.card (Subgroup.zpowers b) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb2 hb]
  have hi : (Subgroup.zpowers b).index = 8 := by
    have hh := (Subgroup.zpowers b).index_mul_card
    rw [hc, hcard] at hh
    omega
  intro v hv
  apply fixedSpace_le_generatedCore (d.representation.comp A.subtype)
    (X := Subgroup.zpowers b) (by rw [hi]; decide)
  rw [Representation.BinaryOffender.mem_fixedSpace_zpowers_iff]
  exact (mem_fixedSpace _ _).mp hv

private theorem A2_natural_obstruction :
    ¬ naturalSummand ⊓ actorCore d A2 3 ≤ actorFixed d (A2 ⊓ inner) := by
  intro h
  let := PermutationCatalogue.A2_elementary
  let g := A2Module.axisLinear 0
  let b : A2 := ⟨MulAut.conj g, (A2Module.conj_axisLinear_mem 0).1⟩
  have hb : b ≠ 1 := by
    intro hb
    have he : MulAut.conj g = MulAut.conj (1 : G) := by
      simpa only [b, Subgroup.coe_one, map_one] using congrArg Subtype.val hb
    exact A2Module.axisLinear_ne_one 0
      (MulAut.conj_injective_of_center_eq_bot center_linear_eq_bot he)
  have hle : fixedSpace g ≤ naturalFixed B2 := by
    intro x hx
    have hv : (x, (0 : Module.Dual (ZMod 2) X)) ∈ fixedSpace (action d b) := by
      rw [mem_fixedSpace, action_apply]
      change d.representation (MulAut.conj g) (x, 0) = (x, 0)
      rw [d.on_inner, naturalDualRepresentation_apply, map_zero,
        (mem_fixedSpace _ _).mp hx]
    have hh := h ⟨by simp, element_fixed_le_core d A2 PermutationCatalogue.A2_card b hb hv⟩
    rw [mem_naturalFixed]
    intro k hk
    have hh' := (mem_actorFixed d B2 _).mp hh (MulAut.conj k) hk
    rw [d.on_inner, naturalDualRepresentation_apply, Prod.mk.injEq] at hh'
    exact hh'.1
  have hd := Submodule.finrank_mono hle
  rw [(Parameters.A2_three_transvections.1 0).2.2,
    Parameters.A2_fixed_planes.1] at hd
  omega

/-- Both summands obstruct fixation for each genuine H.9.3 representative. -/
theorem representative_obstructions (i : Fin 3) :
    (¬ naturalSummand ⊓ actorCore d (PermutationCatalogue.actor i) 3 ≤
      actorFixed d (PermutationCatalogue.actor i ⊓ inner)) ∧
    (¬ dualSummand ⊓ actorCore d (PermutationCatalogue.actor i) 3 ≤
      actorFixed d (PermutationCatalogue.actor i ⊓ inner)) := by
  fin_cases i
  · exact ⟨A0_natural_obstruction d, A0_dual_obstruction d⟩
  · exact ⟨A1_natural_obstruction d, dual_obstruction_of_outer d A1 transposition
      transposition_mem_A1 transposition_outer (A1_natural_obstruction d)⟩
  · exact ⟨A2_natural_obstruction d, dual_obstruction_of_outer d A2 transposition
      transposition_mem_A2 transposition_outer (A2_natural_obstruction d)⟩

/-- The arbitrary conjugator is allowed to exchange the two marked summands. -/
theorem coordinate_obstruction (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 16) :
    ¬ naturalSummand ⊓ actorCore d A 3 ≤ actorFixed d (A ⊓ inner) := by
  obtain ⟨i,a,he⟩ := PermutationCatalogue.actor_exhaustive A hcard
  intro h
  have ht := obstruction_transport d A a naturalSummand h
  rw [he] at ht
  by_cases ha : a ∈ BinaryNaturalDual.FourActors.inner
  · rw [natural_map_inner d a ha] at ht
    exact (representative_obstructions d i).1 ht
  · rw [natural_map_outer d a ha] at ht
    exact (representative_obstructions d i).2 ht

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.FourActors

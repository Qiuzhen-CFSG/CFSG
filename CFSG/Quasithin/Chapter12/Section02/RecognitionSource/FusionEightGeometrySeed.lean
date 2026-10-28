module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAlternatingEight
public import Theory.Representation.BinaryPermutation.AlternatingEightSylowFixed
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The actual Sylow-fixed seed in the A₈ fusion configuration

The marked augmentation core has only constant vectors fixed by a Sylow
two-subgroup of A₈. Restricting the original Sylow to the normal subgroup L
inside LT, and mapping through the literal L/O₂(L) marking, therefore gives
C_V(T) ≤ C_V(L). In particular Ω₁Z(T) ∩ V ≤ C_V(L).

This is the opposite of the seed assertion used in the last paragraph of
Aschbacher--Smith 12.2.16, printed p.800. The cited I.2.3 concerns different
orthogonal covers. The result below checks that intermediate assertion; it
does not refute 12.2.16 under its full ambient hypotheses. Compare the
compatible assertion in 12.6.1(2), printed p.823.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
namespace AlternatingEightFusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal L-conjugate span of the point-Sylow omega-center. -/
abbrev pointSpan (C : AlternatingEightFusion T L V) : Subgroup G :=
  componentOrbit (omegaCenterIn C.pointSylow) L

omit [Finite G] in
/-- The marked point itself supplies a valid nonconstant seed. -/
theorem point_mem_omega (C : AlternatingEightFusion T L V) (D : ChosenModule T L V) :
    (C.v : G) ∈ omegaCenterIn C.pointSylow := by
  let := D.elementary
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨⟨D.le_sylow C.v.property, mem_centralizer_singleton_iff.mpr rfl⟩, ?_,
    elemPow_eq_one_of_isElementaryAbelian _ C.v.property⟩
  intro t ht
  exact mem_centralizer_singleton_iff.mp ht.2

omit [Finite G] in
/-- Invariant subspace classification repairs the printed seed argument:
the weight-two point, rather than a nonfixed element of Z(T), generates V. -/
theorem chosen_le_pointSpan (C : AlternatingEightFusion T L V) (D : ChosenModule T L V) :
    V ≤ C.pointSpan := by
  let j : Multiplicative (BinaryPermutation.core (Fin 8)) →* G :=
    V.subtype.comp C.vectorEquiv.symm.toMonoidHom
  let A : Submodule (ZMod 2) (BinaryPermutation.core (Fin 8)) :=
    AddSubgroup.toZModSubmodule 2 (C.pointSpan.comap j).toAddSubgroup'
  let W := A.map (BinaryPermutation.core (Fin 8)).subtype
  have hn : L ≤ normalizer (C.pointSpan : Set G) := le_normalizer_componentOrbit _ _
  have hW : ∀ g : alternatingGroup (Fin 8), ∀ w ∈ W,
      BinaryPermutation.representation (Fin 8) g.val w ∈ W := by
    intro g w hw
    obtain ⟨x, hx, rfl⟩ := hw
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (C.groupEquiv.symm g)
    have he : C.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = g := by
      rw [hl, C.groupEquiv.apply_symm_apply]
    refine ⟨BinaryPermutation.alternatingCoreRepresentation (Fin 8) g x, ?_, rfl⟩
    change j (Multiplicative.ofAdd
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8) g x)) ∈ C.pointSpan
    have hi := C.intertwines l (C.vectorEquiv.symm (Multiplicative.ofAdd x))
    rw [C.vectorEquiv.apply_symm_apply, he] at hi
    simp only [toAdd_ofAdd] at hi
    change ((C.vectorEquiv.symm (Multiplicative.ofAdd
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8) g x))) : G) ∈ C.pointSpan
    rw [hi]
    exact (mem_normalizer_iff.mp (hn l.property) _).mp hx
  have hv : (C.vectorEquiv C.v).toAdd ∈ A := by
    change j (C.vectorEquiv C.v) ∈ C.pointSpan
    change ((C.vectorEquiv.symm (C.vectorEquiv C.v)) : G) ∈ C.pointSpan
    rw [C.vectorEquiv.symm_apply_apply]
    exact le_componentOrbit _ _ (C.point_mem_omega D)
  rcases BinaryPermutation.invariant_le_constants_or_core_le (by decide) W hW with hc | hc
  · have hh := hc (show (C.vectorEquiv C.v).toAdd.val ∈ W from ⟨_, hv, rfl⟩)
    obtain ⟨k, hk⟩ := (BinaryPermutation.mem_constants_iff _).mp hh
    have hw := C.weight_two
    have hcases : k = 0 ∨ k = 1 := (by decide : ∀ k : ZMod 2, k = 0 ∨ k = 1) k
    rcases hcases with rfl | rfl <;> norm_num [hk] at hw
  · intro w hw
    obtain ⟨x, hx, he⟩ := hc (C.vectorEquiv ⟨w, hw⟩).toAdd.property
    have he' : x = (C.vectorEquiv ⟨w, hw⟩).toAdd := Subtype.ext he
    rw [he'] at hx
    change ((C.vectorEquiv.symm (C.vectorEquiv ⟨w, hw⟩)) : G) ∈ C.pointSpan at hx
    simpa only [C.vectorEquiv.symm_apply_apply] using hx

private theorem exists_sylow_in_normalized (hn : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ P : Sylow 2 L, ∀ l ∈ (P : Subgroup L), (l : G) ∈ (T : Subgroup G) := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  let S : Sylow 2 H := T.subtype le_sup_right
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal A
  let e : A ≃* L := subgroupOfEquivOfLe (le_sup_left : L ≤ H)
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro l ⟨r, hr, rfl⟩
  rw [hR] at hr
  exact hr

/-- Under the literal A₈ marking, every T-fixed vector is already L-fixed. -/
theorem sylow_fixed_le_fixed (C : AlternatingEightFusion T L V)
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    V ⊓ centralizer ((T : Subgroup G) : Set G) ≤ centralizer (L : Set G) := by
  obtain ⟨P, hP⟩ := exists_sylow_in_normalized hn
  let f : L →* alternatingGroup (Fin 8) :=
    C.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f :=
    C.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))
  let S := P.mapSurjective hf
  rintro w ⟨hwV, hwT⟩
  let w' : V := ⟨w, hwV⟩
  let v := (C.vectorEquiv w').toAdd
  have hv : ∀ a ∈ (S : Subgroup (alternatingGroup (Fin 8))),
      BinaryPermutation.alternatingCoreRepresentation (Fin 8) a v = v := by
    rintro a ⟨l, hl, rfl⟩
    have he := C.intertwines l w'
    have hlw := hwT l (hP l hl)
    have he' : C.vectorEquiv.symm (Multiplicative.ofAdd
        (BinaryPermutation.alternatingCoreRepresentation (Fin 8) (f l) v)) = w' := by
      apply Subtype.ext
      change _ = w
      change ((C.vectorEquiv.symm (Multiplicative.ofAdd
        (BinaryPermutation.alternatingCoreRepresentation (Fin 8)
          (C.groupEquiv (QuotientGroup.mk' (pCore 2 L) l))
          (C.vectorEquiv w').toAdd))) : G) = w
      rw [he]
      change (l : G) * w * (l : G)⁻¹ = w
      rw [hlw, mul_inv_cancel_right]
    have hh := congrArg (fun a : V => (C.vectorEquiv a).toAdd) he'
    simpa only [C.vectorEquiv.apply_symm_apply, toAdd_ofAdd] using hh
  have hconstant := BinaryPermutation.alternatingEight_core_sylow_fixed_constant S v hv
  have hfixed := (BinaryPermutation.core_fixed_iff_constant
    (Ω := Fin 8) (by simp) v).mpr hconstant
  intro l hl
  have he := C.intertwines ⟨l, hl⟩ w'
  have hh := hfixed (C.groupEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩))
  change BinaryPermutation.alternatingCoreRepresentation (Fin 8) _ v = v at hh
  change ((C.vectorEquiv.symm (Multiplicative.ofAdd
    (BinaryPermutation.alternatingCoreRepresentation (Fin 8) _ v))) : G) = l * w * l⁻¹ at he
  rw [hh] at he
  simp only [v, ofAdd_toAdd, C.vectorEquiv.symm_apply_apply] at he
  change w = l * w * l⁻¹ at he
  exact (mul_inv_eq_iff_eq_mul.mp he.symm)

/-- The printed nonfixed Sylow seed is unavailable in this exact source configuration. -/
theorem sylow_omega_intersection_le_fixed (C : AlternatingEightFusion T L V)
    {K : GroupClass} (h : Hypothesis1223 K T L) (structural : Structural1222 K) :
    omegaCenterIn (T : Subgroup G) ⊓ V ≤ centralizer (L : Set G) := by
  intro w hw
  exact C.sylow_fixed_le_fixed (structural G T L h).1
    ⟨hw.2, ((mem_omegaCenterIn_iff _ _).mp hw.1).2.1⟩

end AlternatingEightFusion
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

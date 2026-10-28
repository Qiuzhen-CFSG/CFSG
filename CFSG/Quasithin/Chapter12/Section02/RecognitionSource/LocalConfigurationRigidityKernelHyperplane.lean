module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelReduction

/-!
# The literal hyperplane centralizer in 12.2.25

Write W=U∩V. Its index in V is two, and [U,V]=W. For any v outside W,
the homomorphism u↦[u,v] therefore maps U onto W: both cosets of W in V
have the same displacement, and W centralizes U. An element of C_T(W)
can consequently be adjusted by U to fix v as well as W, hence all of V.
This proves C_T(W)=U C_T(V) using the original conjugation action.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
12.2.24--25, printed pp.804--805, the observation preceding 12.2.25.
The subsequent C_T(V)=V C_T(I) and Thompson arguments remain with
qt-d-12225-common-centralizers; source assembly is qt-d-12213-local-rigidity.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel

omit [Finite G] in
private theorem index_two_generation {W V K : Subgroup G}
    (hi : W.relIndex V = 2) {v : G} (hv : v ∈ V) (hvW : v ∉ W)
    (hWK : W ≤ K) (hvK : v ∈ K) : V ≤ K := by
  intro x hx
  by_cases hxW : x ∈ W
  · exact hWK hxW
  have hw : v⁻¹ * x ∈ W :=
    ((W.subgroupOf V).mul_mem_iff_of_index_two hi
      (a := ⟨v⁻¹,V.inv_mem hv⟩) (b := ⟨x,hx⟩)).mpr
      (by simpa only [mem_subgroupOf, inv_mem_iff] using iff_of_false hvW hxW)
  simpa only [mul_inv_cancel_left] using K.mul_mem hvK (hWK hw)

omit [Finite G] in
private theorem hyperplane_index
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (U ⊓ V : Subgroup G).relIndex V = 2 := by
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, C.hyperplane, chosen_card A] at hh
  have hd : d = d - 1 + 1 := by have := A.dimension.1; omega
  have hc : 2 ^ d = 2 * 2 ^ (d - 1) := by
    calc
      2 ^ d = 2 ^ (d - 1 + 1) := congrArg (fun n : ℕ => 2 ^ n) hd
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  rw [hc] at hh
  have hp : 0 < 2 ^ (d - 1) := pow_pos (by decide) _
  nlinarith

omit [Finite G] in
/-- The original U induces every transvection with the chosen hyperplane as
axis: its displacement on any vector outside that hyperplane fills U∩V. -/
theorem hyperplane_displacement_surjective
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    {v : G} (hv : v ∈ V) (hvW : v ∉ U ⊓ V) :
    ∀ w ∈ U ⊓ V, ∃ u ∈ U, ⁅u,v⁆ = w := by
  let := C.elementary
  let W := U ⊓ V
  let delta : U →* W := {
    toFun := fun u => ⟨⁅(u : G),v⁆, C.transvections.le (commutator_mem_commutator u.property hv)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change ⁅(x : G) * (y : G),v⁆ = ⁅(x : G),v⁆ * ⁅(y : G),v⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hy : ⁅(y : G),v⁆ ∈ U := (C.transvections.le (commutator_mem_commutator y.property hv)).1
      have hx : ⁅(x : G),v⁆ ∈ U := (C.transvections.le (commutator_mem_commutator x.property hv)).1
      rw [← (le_centralizer U x.property _ hy), mul_inv_cancel_right,
        (le_centralizer U hy _ hx)] }
  let F := delta.range.map W.subtype
  have hWF : W ≤ F := by
    rw [show W = ⁅U,V⁆ from C.transvections.symm]
    apply commutator_le.mpr
    intro u hu x hx
    by_cases hxW : x ∈ W
    · have he : ⁅u,x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        (le_centralizer U hu x hxW.1).symm
      rw [he]
      exact F.one_mem
    have hw : v⁻¹ * x ∈ W :=
      ((W.subgroupOf V).mul_mem_iff_of_index_two (hyperplane_index A C)
        (a := ⟨v⁻¹,V.inv_mem hv⟩) (b := ⟨x,hx⟩)).mpr
        (by simpa only [mem_subgroupOf, inv_mem_iff] using iff_of_false hvW hxW)
    have he : ⁅u,v⁻¹*x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (le_centralizer U hu _ hw.1).symm
    have hh := commutatorElement_mul_right_eq_mul_conj u v (v⁻¹*x)
    simp only [mul_inv_cancel_left, he, mul_one, mul_inv_cancel_right] at hh
    rw [hh]
    exact mem_map.mpr ⟨delta ⟨u,hu⟩, ⟨⟨u,hu⟩,rfl⟩,rfl⟩
  intro w hw
  obtain ⟨z,⟨u,hu⟩,hz⟩ := hWF hw
  exact ⟨u,u.property,(congrArg Subtype.val hu).trans hz⟩

/-- The pointwise hyperplane centralizer is the original transvection group
times the original action kernel, before either dimensional splitting. -/
theorem hyperplane_centralizer_eq_core_sup_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) =
      U ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G)) := by
  let := C.elementary
  let W := U ⊓ V
  have hTV := ((structural G T L h).2.2 V D).1
  obtain ⟨v,hv,hvU,_⟩ := C.inverted
  have hvW : v ∉ W := fun hvW => hvU hvW.1
  apply le_antisymm
  · intro t ht
    have htvV : t * v * t⁻¹ ∈ V := (mem_normalizer_iff.mp (hTV ht.1) v).mp hv
    have htvW : t * v * t⁻¹ ∉ W := by
      intro hw
      have hc := ht.2 _ hw
      have he : t * v * t⁻¹ = v := by
        apply (mul_left_cancel (a := t))
        simpa only [mul_inv_cancel_right, inv_mul_cancel_right] using hc.symm
      exact hvW (he ▸ hw)
    have hw : ⁅t,v⁆ ∈ W :=
      ((W.subgroupOf V).mul_mem_iff_of_index_two (hyperplane_index A C)
        (a := ⟨t*v*t⁻¹,htvV⟩) (b := ⟨v⁻¹,V.inv_mem hv⟩)).mpr
        (by simpa only [mem_subgroupOf, inv_mem_iff] using iff_of_false htvW hvW)
    obtain ⟨u,hu,he⟩ := hyperplane_displacement_surjective A C hv hvW _ hw
    have hcv : v * (u⁻¹*t) = (u⁻¹*t) * v := by
      have hc : u * v * u⁻¹ = t * v * t⁻¹ :=
        mul_right_cancel (show (u*v*u⁻¹)*v⁻¹ = (t*v*t⁻¹)*v⁻¹ from he)
      calc
        v * (u⁻¹*t) = u⁻¹ * (u*v*u⁻¹) * t := by group
        _ = u⁻¹ * (t*v*t⁻¹) * t := by rw [hc]
        _ = (u⁻¹*t)*v := by group
    have hcW : u⁻¹*t ∈ centralizer (W : Set G) :=
      (centralizer (W : Set G)).mul_mem
        ((centralizer _).inv_mem (centralizer_le (show W ≤ U from inf_le_left) (le_centralizer U hu))) ht.2
    have hcV : u⁻¹*t ∈ centralizer (V : Set G) := by
      intro x hx
      have hgen := index_two_generation (hyperplane_index A C) hv hvW
        (K := centralizer ({u⁻¹*t} : Set G))
        (fun w hw => mem_centralizer_singleton_iff.mpr (hcW w hw))
        (mem_centralizer_singleton_iff.mpr hcv)
      exact mem_centralizer_singleton_iff.mp (hgen hx)
    have hm := mul_mem_sup hu (show u⁻¹*t ∈ (T : Subgroup G) ⊓ centralizer (V : Set G) from
      ⟨(T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem (C.core_le_sylow hu)) ht.1,hcV⟩)
    simpa only [mul_inv_cancel_left] using hm
  · exact sup_le (le_inf C.core_le_sylow ((le_centralizer U).trans (centralizer_le inf_le_left)))
      (le_inf inf_le_left (inf_le_right.trans (centralizer_le inf_le_right)))

end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

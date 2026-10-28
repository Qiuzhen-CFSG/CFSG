module
public import Theory.GroupTheory.ElementaryOuterSylow

/-!
# Transport of elementary outer Sylow actions

A multiplicative equivalence transports the actual Sylow subgroup, its outer
automorphism, and its elementary displacement subgroup. In particular, no
replacement of an automorphism by another representative of its outer coset
is made. Elementary displacements have square one and commute pairwise;
these identities are the inputs to coordinate calculations in binary GL.

Source: the Sylow commutator step in Aschbacher--Smith G.10.15(3), printed p.363.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative
namespace Theory.GroupTheory.ElementaryOuterSylowAction
variable {H K : Type*} [Group H] [Group K]

/-- Transport all the data along the same group equivalence. -/
def transport [Finite H] (a : ElementaryOuterSylowAction H) (e : H ≃* K) :
    ElementaryOuterSylowAction K := by
  letI := a.elementary
  refine ⟨a.sylow.mapSurjective (f := e.toMonoidHom) e.surjective,
    MulAut.congr e a.automorphism, ?_, ?_, ?_,
    a.displacementGroup.map e.toMonoidHom, IsElementaryAbelian.map e.toMonoidHom,
    Subgroup.map_mono a.contained, ?_⟩
  · rw [← map_pow, a.square, map_one]
  · intro hi
    rw [← MulAut.map_innerSubgroup_congr e] at hi
    obtain ⟨b, hb, he⟩ := hi
    exact a.outer ((MulAut.congr e).injective he ▸ hb)
  · rintro u ⟨v, hv, rfl⟩
    refine ⟨a.automorphism v, a.preserves v hv, ?_⟩
    simp [MulAut.congr_apply]
  · rintro u ⟨v, hv, rfl⟩
    refine ⟨a.automorphism v * v⁻¹, a.displacement v hv, ?_⟩
    simp [MulAut.congr_apply]

/-- The transported automorphism is conjugation of the literal original map. -/
theorem transport_automorphism_apply [Finite H] (a : ElementaryOuterSylowAction H)
    (e : H ≃* K) (u : H) :
    (a.transport e).automorphism (e u) = e (a.automorphism u) := by
  simp [transport, MulAut.congr_apply]

/-- Every displacement has square one. -/
theorem displacement_sq (a : ElementaryOuterSylowAction H) (u : H)
    (hu : u ∈ (a.sylow : Subgroup H)) :
    (a.automorphism u * u⁻¹) ^ 2 = 1 := by
  let _ := a.elementary
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (a.displacement u hu)

/-- Any two Sylow displacements commute in the original group. -/
theorem displacement_commute (a : ElementaryOuterSylowAction H) (u v : H)
    (hu : u ∈ (a.sylow : Subgroup H)) (hv : v ∈ (a.sylow : Subgroup H)) :
    Commute (a.automorphism u * u⁻¹) (a.automorphism v * v⁻¹) := by
  let _ := a.elementary
  exact congrArg Subtype.val (mul_comm
    (⟨_, a.displacement u hu⟩ : a.displacementGroup)
    (⟨_, a.displacement v hv⟩ : a.displacementGroup))

end Theory.GroupTheory.ElementaryOuterSylowAction

module

public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage.RootGroups

/-!
# Field coordinates of projective root-group automorphisms

An automorphism preserving the upper root group induces an additive equivalence
of the field: the projective upper transvections have unique parameters. If this
equivalence also preserves multiplication and the automorphism fixes the Weyl
element, generation identifies it with the actual entrywise field action.

This is a conditional reduction for the A₁ automorphism theorem in GLS3,
Theorem 2.5.12 and §2.7. Multiplicativity and normalization are separate proof
obligations. The additive-coordinate construction adapts the corresponding
binary SL₂ argument in `BenderSuzuki/.../SemilinearCoverage/RootParameters.lean`;
all group elements here belong to the genuine PSL₂ quotient.
-/

namespace Theory.PSL2.OuterSolvable.OddCoverage

variable {K : Type*} [Field K]

private theorem exists_root_image (a : MulAut (Group K))
    (hU : (rootGroup K).map a.toMonoidHom = rootGroup K) (t : K) :
    ∃ s : K, upper s = a (upper t) := by
  apply (mem_rootGroup _).mp
  rw [← hU]
  exact ⟨upper t, (mem_rootGroup _).mpr ⟨t, rfl⟩, rfl⟩

/-- The unique parameter of the image of an upper transvection. -/
public noncomputable def rootParameter (a : MulAut (Group K))
    (hU : (rootGroup K).map a.toMonoidHom = rootGroup K) (t : K) : K :=
  Classical.choose (exists_root_image a hU t)

public theorem map_upper (a : MulAut (Group K))
    (hU : (rootGroup K).map a.toMonoidHom = rootGroup K) (t : K) :
    a (upper t) = upper (rootParameter a hU t) :=
  (Classical.choose_spec (exists_root_image a hU t)).symm

public theorem rootParameter_add (a : MulAut (Group K))
    (hU : (rootGroup K).map a.toMonoidHom = rootGroup K) (s t : K) :
    rootParameter a hU (s + t) = rootParameter a hU s + rootParameter a hU t := by
  apply upper_injective
  rw [← map_upper a hU, upper_add, map_mul, map_upper a hU, map_upper a hU, upper_add]

public theorem rootParameter_bijective (a : MulAut (Group K))
    (hU : (rootGroup K).map a.toMonoidHom = rootGroup K) :
    Function.Bijective (rootParameter a hU) := by
  constructor
  · intro s t h
    apply upper_injective
    apply a.injective
    rw [map_upper a hU, map_upper a hU, h]
  · intro t
    have ht : upper t ∈ (rootGroup K).map a.toMonoidHom := by
      rw [hU]
      exact (mem_rootGroup _).mpr ⟨t, rfl⟩
    obtain ⟨g, hg, he⟩ := ht
    obtain ⟨s, rfl⟩ := (mem_rootGroup _).mp hg
    refine ⟨s, ?_⟩
    apply upper_injective
    rw [← map_upper a hU]
    exact he

/-- The additive field equivalence induced on the actual projective root group. -/
@[expose] public noncomputable def rootParameterEquiv (a : MulAut (Group K))
    (hU : (rootGroup K).map a.toMonoidHom = rootGroup K) : K ≃+ K :=
  { Equiv.ofBijective (rootParameter a hU) (rootParameter_bijective a hU) with
    map_add' := rootParameter_add a hU }

public theorem rootParameterEquiv_apply (a : MulAut (Group K))
    (hU : (rootGroup K).map a.toMonoidHom = rootGroup K) (t : K) :
    rootParameterEquiv a hU t = rootParameter a hU t := rfl

public theorem rootParameter_one_of_fixed (a : MulAut (Group K))
    (hU : (rootGroup K).map a.toMonoidHom = rootGroup K)
    (h1 : a (upper 1) = upper 1) : rootParameter a hU 1 = 1 := by
  apply upper_injective
  rw [← map_upper a hU]
  exact h1

/-- Multiplicative root coordinates and the Weyl image determine the field action.
This does not assert multiplicativity for arbitrary normalized automorphisms. -/
public theorem eq_projectiveFieldAut_of_rootParameter_mul (a : MulAut (Group K))
    (hU : (rootGroup K).map a.toMonoidHom = rootGroup K)
    (hw : a (weyl K) = weyl K)
    (hmul : ∀ s t : K,
      rootParameter a hU (s * t) = rootParameter a hU s * rootParameter a hU t) :
    ∃ σ : K ≃+* K, a = projectiveFieldAutHom σ := by
  let σ : K ≃+* K := { rootParameterEquiv a hU with map_mul' := hmul }
  refine ⟨σ, ?_⟩
  apply MulEquiv.toMonoidHom_injective
  apply hom_ext_root_weyl
  · intro t
    change a (upper t) = projectiveFieldAutHom σ (upper t)
    rw [map_upper a hU, projectiveFieldAut_upper]
    rfl
  · change a (weyl K) = projectiveFieldAutHom σ (weyl K)
    simpa only [projectiveFieldAut_weyl] using hw

end Theory.PSL2.OuterSolvable.OddCoverage

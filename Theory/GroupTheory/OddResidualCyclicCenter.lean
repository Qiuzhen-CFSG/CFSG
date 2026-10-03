module

public import Theory.GroupTheory.OddLayerCentralInvolutionKernel

/-!
# Cyclic center from a full odd-layer commutator criterion

The odd-layer criterion gives uniqueness of central involutions. Hence the
square map on the center has kernel of order at most two, and its image has
index at most two. A generator modulo squares lifts to a generator of the
center by Frattini nongeneration for finite two-groups.
-/


open scoped IsMulCommutative

namespace Theory.GroupTheory

@[expose] public section

private theorem cyclic_of_square_kernel_bound
    {C : Type*} [CommGroup C] [Finite C] (hC : IsPGroup 2 C)
    (hker : Nat.card (powMonoidHom 2 : C →* C).ker ≤ 2) : IsCyclic C := by
  let : Fact (IsPGroup 2 C) := ⟨hC⟩
  let squares := (powMonoidHom 2 : C →* C).range
  have hindex : squares.index ≤ 2 := by rwa [Subgroup.index_range]
  have hpositive := Nat.card_pos (α := C ⧸ squares)
  have hdiv : Nat.card (C ⧸ squares) ∣ 2 := by
    change Nat.card (C ⧸ squares) ≤ 2 at hindex
    interval_cases Nat.card (C ⧸ squares) <;> norm_num
  let : IsCyclic (C ⧸ squares) := isCyclic_of_card_dvd_prime hdiv
  obtain ⟨quotientGenerator, hgenerator⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (C ⧸ squares))
  obtain ⟨generator, rfl⟩ := QuotientGroup.mk'_surjective squares quotientGenerator
  have hmap : (Subgroup.zpowers generator).map (QuotientGroup.mk' squares) = ⊤ := by
    simpa using hgenerator
  have hsup : Subgroup.zpowers generator ⊔ squares = ⊤ := by
    simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using
      congrArg (Subgroup.comap (QuotientGroup.mk' squares)) hmap
  have hsquares : squares ≤ frattini C := by
    rintro element ⟨root, rfl⟩
    exact pth_power_mem_frattini_of_isPGroup (p := 2) root
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨generator, frattini_nongenerating (G := C) ?_⟩
  apply top_unique
  rw [← hsup]
  exact sup_le_sup_left hsquares _

theorem center_isCyclic_of_odd_pgroup_commutator
    {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (R A : Subgroup X) (hRn : R.Normal) (hRp : IsPGroup p R)
    (hRne : R ≠ ⊥) (hA2 : IsPGroup 2 A)
    (hcomm : ∀ J : Subgroup X, J ≤ A → (J.subgroupOf A).Normal →
      J ≠ ⊥ → ⁅R, J⁆ = R) : IsCyclic (Subgroup.center A) := by
  classical
  let C := Subgroup.center A
  let K := (powMonoidHom 2 : C →* C).ker
  have hunique (first second : K) (hfirst : first ≠ 1) (hsecond : second ≠ 1) :
      first = second := by
    apply Subtype.ext
    apply Subtype.ext
    apply central_involutions_eq_of_odd_pgroup_commutator
      hpodd R A hRn hRp hRne hA2 hcomm
      first.val.val second.val.val first.val.property second.val.property
    · refine ⟨?_, ?_⟩
      · intro heq
        exact hfirst (Subtype.ext (Subtype.ext heq))
      · exact congrArg Subtype.val first.property
    · refine ⟨?_, ?_⟩
      · intro heq
        exact hsecond (Subtype.ext (Subtype.ext heq))
      · exact congrArg Subtype.val second.property
  have hinjective : Function.Injective (fun element : K => decide (element = 1)) := by
    intro first second heq
    by_cases hfirst : first = 1
    · have hsecond : second = 1 := by simpa [hfirst] using heq.symm
      exact hfirst.trans hsecond.symm
    · have hsecond : second ≠ 1 := by simpa [hfirst] using heq.symm
      exact hunique first second hfirst hsecond
  apply cyclic_of_square_kernel_bound (hA2.to_subgroup C)
  have hcard : Nat.card K ≤ 2 := by
    simpa using Nat.card_le_card_of_injective _ hinjective
  exact hcard

end

end Theory.GroupTheory

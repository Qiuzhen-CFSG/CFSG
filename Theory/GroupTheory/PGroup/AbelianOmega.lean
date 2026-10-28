module

public import Theory.GroupTheory.PGroup.Omega
public import Theory.Frattini.PGroup

/-!
# Involutions in abelian two-groups

An abelian finite two-group with at most two elements in its first omega
subgroup is cyclic. The square homomorphism has kernel contained in omega,
and its image has index equal to the kernel order. Thus the quotient by
squares is cyclic; squares lie in the Frattini subgroup, so a lifted generator
generates the group.

This supplies the abelian reduction for the normal four-group argument in
GLS, *The Classification of the Finite Simple Groups*, volume 2, Lemma 10.11.
-/

open scoped IsMulCommutative

namespace IsPGroup

/-- An abelian finite two-group with at most one nonidentity involution is cyclic. -/
public theorem isCyclic_of_card_omega_one_le_two
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hA : IsPGroup 2 A) (hcard : Nat.card (omega₁ A (p := 2)) ≤ 2) :
    IsCyclic A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  let square : A →* A := powMonoidHom 2
  have hker : square.ker ≤ omega₁ A (p := 2) := by
    intro x hx
    apply Subgroup.subset_closure
    simpa [square] using hx
  have hquot : Nat.card (A ⧸ square.range) ≤ 2 := by
    rw [← Subgroup.index_eq_card, Subgroup.index_range]
    exact (Subgroup.card_le_of_le hker).trans hcard
  have hdiv : Nat.card (A ⧸ square.range) ∣ 2 := by
    have hpos := Nat.card_pos (α := A ⧸ square.range)
    have : Nat.card (A ⧸ square.range) = 1 ∨
        Nat.card (A ⧸ square.range) = 2 := by omega
    rcases this with h | h <;> simp [h]
  let : IsCyclic (A ⧸ square.range) := isCyclic_of_card_dvd_prime hdiv
  obtain ⟨q, hq⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (A ⧸ square.range))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective square.range q
  have hmap : (Subgroup.zpowers x).map (QuotientGroup.mk' square.range) = ⊤ := by
    simpa using hq
  have hsup : Subgroup.zpowers x ⊔ square.range = ⊤ := by
    simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using
      congrArg (Subgroup.comap (QuotientGroup.mk' square.range)) hmap
  have hrange : square.range ≤ frattini A := by
    rintro y ⟨z, rfl⟩
    exact pth_power_mem_frattini_of_isPGroup (p := 2) z
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨x, frattini_nongenerating (G := A) ?_⟩
  apply top_unique
  rw [← hsup]
  exact sup_le_sup_left hrange _

end IsPGroup

module

public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicEdges

/-!
# The three cubic subgroups across an A₅ edge

Mark an A₄-generating pair by the three-cycles (012) and (013).
The other orbit of neighbors under (012) consists of (014), (024), (124).
Exactly one of these generates A₄ with (013), and the other two generate A₅.
Small permutation identities and the existing cubic-pair classification prove
this on the literal A₅; group equivalences then retain the actual conjugators.

Source: Aschbacher, *Sporadic Groups* (1994), 47.6(2), p.264.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace alternatingGroup.FiveLocalGeometry.CubicEdgeIncidence
open CubicEdges
variable {H : Type*} [Group H]

/-- The literal conjugation orbit, with conjugating elements in P. -/
def cubicOrbit (P R : Subgroup H) : Set (Subgroup H) :=
  {S | ∃ x : P, R.map (MulAut.conj (x : H)).toMonoidHom = S}

theorem mem_cubicOrbit_self (P R : Subgroup H) : R ∈ cubicOrbit P R := by
  refine ⟨1, ?_⟩
  change (MulAut.conj (1 : H) • R) = R
  rw [map_one, one_smul]

theorem cubicOrbit_eq_of_mem {P R S : Subgroup H} (h : S ∈ cubicOrbit P R) :
    cubicOrbit P S = cubicOrbit P R := by
  obtain ⟨x, rfl⟩ := h
  ext T
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y * x, conj_map_mul _ _ _⟩
  · rintro ⟨y, rfl⟩
    refine ⟨y * x⁻¹, ?_⟩
    rw [← conj_map_mul]
    simp

/-- Equivalences preserve the orbit and the actual subgroup of conjugators. -/
theorem mem_cubicOrbit_map_iff {H' : Type*} [Group H'] (e : H ≃* H')
    (P R S : Subgroup H) :
    S.map e.toMonoidHom ∈ cubicOrbit (P.map e.toMonoidHom) (R.map e.toMonoidHom) ↔
      S ∈ cubicOrbit P R := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, he⟩ := x.property
    refine ⟨⟨y, hy⟩, map_injective (f := e.toMonoidHom) e.injective ?_⟩
    rw [map_conj_equiv]
    change e y = (x : H') at he
    change (R.map e.toMonoidHom).map (MulAut.conj (e y)).toMonoidHom = _
    rw [he]
    exact hx
  · rintro ⟨x, rfl⟩
    exact ⟨⟨e x, mem_map_of_mem _ x.property⟩, (map_conj_equiv e x R).symm⟩

theorem C_injective : Function.Injective C := by
  intro i j he
  have h : ∀ i j, (cycle i = 1 ∨ cycle i = cycle j ∨ cycle i = (cycle j)⁻¹) → i = j := by
    decide +kernel
  exact h i j ((mem_C j _).mp (he ▸ mem_zpowers (cycle i)))

private theorem orbit_model (i j k : Fin 10)
    (hj : (C i).map (MulAut.conj (cycle 0)).toMonoidHom = C j)
    (hk : (C i).map (MulAut.conj (cycle 0)⁻¹).toMonoidHom = C k) :
    cubicOrbit (C 0) (C i) = {C i, C j, C k} := by
  ext S
  constructor
  · rintro ⟨x, rfl⟩
    rcases (mem_C 0 x).mp x.property with h | h | h
    · have he : (C i).map (MulAut.conj (x : A5)).toMonoidHom = C i := by
        change MulAut.conj (x : A5) • C i = C i
        rw [h, map_one, one_smul]
      rw [he]
      simp
    · rw [h, hj]
      simp
    · rw [h, hk]
      simp
  · intro h
    rcases h with h | h | h
    · subst S; exact mem_cubicOrbit_self _ _
    · subst S; exact ⟨⟨cycle 0, mem_zpowers _⟩, hj⟩
    · have he : S = C k := h
      subst S
      exact ⟨⟨(cycle 0)⁻¹, inv_mem (mem_zpowers _)⟩, hk⟩

private theorem orbit_one : cubicOrbit (C 0) (C 1) = {C 1, C 6, C 3} := by
  apply orbit_model <;> apply map_C_of_cycle <;> decide +kernel

private theorem orbit_two : cubicOrbit (C 0) (C 2) = {C 2, C 7, C 4} := by
  apply orbit_model <;> apply map_C_of_cycle <;> decide +kernel

private theorem external_model (R : Subgroup A5) (hR : Nat.card R = 3)
    (hPR : Nat.card (C 0 ⊔ R : Subgroup A5) = 12)
    (hout : R ∉ cubicOrbit (C 0) (C 1)) :
    cubicOrbit (C 0) R = {C 2, C 7, C 4} := by
  obtain ⟨i, rfl⟩ := cubic_representative R hR
  have hc : Nat.card (C 0 ⊔ C (representative i) : Subgroup A5) = 12 := by
    rw [← (adjustment_maps i).1, ← (adjustment_maps i).2,
      ← Subgroup.map_sup, card_map_of_injective (MulAut.conj _).injective, hPR]
  have cases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 := by
    have hr : representative i = 0 ∨ representative i = 1 ∨ representative i = 5 := by
      have h : ∀ i, representative i = 0 ∨ representative i = 1 ∨ representative i = 5 := by
        decide +kernel
      exact h i
    have hi : representative i = 1 := by
      rcases hr with h | h | h
      · rw [h, sup_idem, card_C] at hc; omega
      · exact h
      · rw [h, nonedge_join, card_top, card] at hc; omega
    have h : ∀ i, representative i = 1 →
        i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 := by decide +kernel
    exact h i hi
  have hi : i = 2 ∨ i = 7 ∨ i = 4 := by
    rw [orbit_one] at hout
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  have hm : C i ∈ cubicOrbit (C 0) (C 2) := by
    rw [orbit_two]
    rcases hi with rfl | rfl | rfl <;> simp
  exact (cubicOrbit_eq_of_mem hm).trans orbit_two

private theorem pair_models :
    Nonempty (↥(C 1 ⊔ C 2) ≃* alternatingGroup (Fin 4)) ∧
      C 1 ⊔ C 7 = ⊤ ∧ C 1 ⊔ C 4 = ⊤ := by
  have ha : ∃ g : A5,
      (g * cycle 0 * g⁻¹ = cycle 1 ∨ g * cycle 0 * g⁻¹ = (cycle 1)⁻¹) ∧
      (g * cycle 1 * g⁻¹ = cycle 2 ∨ g * cycle 1 * g⁻¹ = (cycle 2)⁻¹) := by
    decide +kernel
  obtain ⟨g, hg, hg'⟩ := ha
  have he : (C 0 ⊔ C 1).map (MulAut.conj g).toMonoidHom = C 1 ⊔ C 2 := by
    rw [Subgroup.map_sup, map_C_of_cycle hg, map_C_of_cycle hg']
  have full (k : Fin 10) (hk : k = 7 ∨ k = 4) : C 1 ⊔ C k = ⊤ := by
    have h : ∀ k : Fin 10, k = 7 ∨ k = 4 → ∃ g : A5,
        (g * cycle 0 * g⁻¹ = cycle 1 ∨ g * cycle 0 * g⁻¹ = (cycle 1)⁻¹) ∧
        (g * cycle 5 * g⁻¹ = cycle k ∨ g * cycle 5 * g⁻¹ = (cycle k)⁻¹) := by
      decide +kernel
    obtain ⟨g, hg, hg'⟩ := h k hk
    rw [← map_C_of_cycle hg, ← map_C_of_cycle hg', ← Subgroup.map_sup,
      nonedge_join, map_top_of_surjective _ (MulAut.conj g).surjective]
  exact ⟨⟨(MulEquiv.subgroupCongr he.symm).trans
    (((C 0 ⊔ C 1).equivMapOfInjective _ (MulAut.conj g).injective).symm.trans modelEquiv)⟩,
    full 7 (Or.inl rfl), full 4 (Or.inr rfl)⟩

/-- The outer orbit has three distinct members, one A₄ join and two full joins.
The only orbit exclusion is the endpoint's own P-orbit. -/
theorem external_orbit_partition (e : H ≃* A5) (P Q R : Subgroup H)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3) (hR : Nat.card R = 3)
    (ePQ : ↥(P ⊔ Q) ≃* alternatingGroup (Fin 4))
    (ePR : ↥(P ⊔ R) ≃* alternatingGroup (Fin 4))
    (hout : R ∉ cubicOrbit P Q) :
    ∃ S₀ S₁ S₂ : Subgroup H,
      S₀ ≠ S₁ ∧ S₀ ≠ S₂ ∧ S₁ ≠ S₂ ∧
      cubicOrbit P R = {S₀, S₁, S₂} ∧
      Nonempty (↥(Q ⊔ S₀) ≃* alternatingGroup (Fin 4)) ∧
      Q ⊔ S₁ = ⊤ ∧ Q ⊔ S₂ = ⊤ := by
  obtain ⟨a, hp, hq⟩ := exists_marking e P Q hP hQ ePQ
  have hm : cubicOrbit (C 0) (R.map a.toMonoidHom) = {C 2, C 7, C 4} := by
    apply external_model
    · rw [card_map_of_injective a.injective, hR]
    · rw [← hp, ← Subgroup.map_sup, card_map_of_injective a.injective,
        Nat.card_congr ePR.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    · rw [← hp, ← hq, mem_cubicOrbit_map_iff]
      exact hout
  let S (i : Fin 10) : Subgroup H := (C i).map a.symm.toMonoidHom
  have hs (i : Fin 10) : (S i).map a.toMonoidHom = C i := by simp [S, map_map]
  have hinj : Function.Injective S := by
    intro i j h
    exact C_injective (by simpa only [hs] using congrArg (map a.toMonoidHom) h)
  refine ⟨S 2, S 7, S 4, by exact fun h => (by decide : (2 : Fin 10) ≠ 7) (hinj h),
    by exact fun h => (by decide : (2 : Fin 10) ≠ 4) (hinj h),
    by exact fun h => (by decide : (7 : Fin 10) ≠ 4) (hinj h), ?_, ?_, ?_, ?_⟩
  · ext T
    rw [← mem_cubicOrbit_map_iff a, hp, hm]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, ← hs]
    simp only [map_injective (f := a.toMonoidHom) a.injective |>.eq_iff]
  · have he : (Q ⊔ S 2).map a.toMonoidHom = C 1 ⊔ C 2 := by
      rw [Subgroup.map_sup, hq, hs]
    exact ⟨((Q ⊔ S 2).equivMapOfInjective _ a.injective).trans
      ((MulEquiv.subgroupCongr he).trans pair_models.1.some)⟩
  · apply map_injective (f := a.toMonoidHom) a.injective
    rw [Subgroup.map_sup, hq, hs, pair_models.2.1, map_top_of_surjective _ a.surjective]
  · apply map_injective (f := a.toMonoidHom) a.injective
    rw [Subgroup.map_sup, hq, hs, pair_models.2.2, map_top_of_surjective _ a.surjective]

end alternatingGroup.FiveLocalGeometry.CubicEdgeIncidence

module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Five.Model

/-!
# Permutation-equivariant sections of the SU₅(4) diagonal torus

The full torus preimage is abelian by `torus_preimage_commutative`.
Conjugation by lifts of permutation matrices descends to an action of the
actual symmetric group on that preimage, fixing the central kernel pointwise.

For a root supported on coordinates i and j, its transposition inverts its
image. If a is any lift and α is that transposition action, the defect
z = α(a)a is in the kernel. Since z⁵ = 1, the corrected lift az² is inverted.
This inverted lift is unique: the ratio of two such lifts is a kernel element
of order dividing both two and five. Uniqueness gives root homomorphisms and
their permutation equivariance. The triangle defect is fixed by every
permutation but inverted by the transposition of its endpoints, so it vanishes.

Multiplying the root lifts against coordinate zero constructs the section.
The triangle relation and the determinant-one coordinate product prove its
full permutation equation, including permutations that move coordinate zero.
The final theorem supplies the literal `HasPermutationTorusLift` contract for
the five-primary transfer consumer, without any additional lifting premises.

Source: Aschbacher--Smith I.1.1--2 and the multiplier calculation I.1.4(4),
`refs/quasithin.pdf`, printed pp.407--408; GLS III Section 6.1,
`refs/KGroup/GLS3/chapter6.tex`.
-/

public section


open Subgroup
open scoped IsMulCommutative
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Five
namespace PermutationLift
noncomputable section
variable {C A : Type*} [CommGroup C] [CommGroup A]

private theorem root_one (i j : Fin 5) : root C i j 1 = 1 := by
  apply Subtype.ext
  simp [root]

private theorem root_mul (i j : Fin 5) (u v : C) :
    root C i j (u*v) = root C i j u * root C i j v := by
  apply Subtype.ext
  simp only [root, Pi.mulSingle_mul, mul_inv_rev, Subgroup.coe_mul]
  ac_rfl

private theorem root_reverse (i j : Fin 5) (u : C) :
    root C j i u = (root C i j u)⁻¹ := by
  apply Subtype.ext
  simp [root, Pi.mulSingle_inv]

private theorem root_triangle (i j k : Fin 5) (u : C) :
    root C i j u * root C j k u = root C i k u := by
  apply Subtype.ext
  simp only [root, Subgroup.coe_mul, Pi.mulSingle_inv]
  group

private theorem root_same (i : Fin 5) (u : C) : root C i i u = 1 := by
  apply Subtype.ext
  simp [root, Pi.mulSingle_inv]

private theorem odd_kernel_eq_one (q : A →* Coordinates C)
    (hk : ∀ z, q z = 1 → z^5 = 1) {z : A} (hz : q z = 1) (he : z = z⁻¹) :
    z = 1 := by
  have h2 : z^2 = 1 := by rw [pow_two, he, inv_mul_eq_one]; exact he
  have h5 := hk z hz
  calc
    z = (z^2)^2*z := by rw [h2]; simp
    _ = z^5 := by group
    _ = 1 := h5

private theorem inverted_lift (q : A →* Coordinates C) (hq : Function.Surjective q)
    (hk : ∀ z, q z = 1 → z^5 = 1) (α : MulAut A)
    (hfix : ∀ z, q z = 1 → α z = z) (x : Coordinates C)
    (hx : ∀ a, q a = x → q (α a) = x⁻¹) :
    ∃! a, q a = x ∧ α a = a⁻¹ := by
  obtain ⟨a, ha⟩ := hq x
  let z := α a * a
  have hz : q z = 1 := by simp only [z, map_mul, hx a ha, ha, inv_mul_cancel]
  have hz5 := hk z hz
  have haz : α a = z*a⁻¹ := by dsimp [z]; group
  have hnew : α (a*z^2) = (a*z^2)⁻¹ := by
    rw [map_mul, map_pow, hfix z hz, haz]
    have he : z^3 = z⁻¹^2 := by
      apply mul_right_cancel (b := z^2)
      calc
        z^3*z^2 = z^5 := by group
        _ = 1 := hz5
        _ = z⁻¹^2*z^2 := by group
    calc
      z*a⁻¹*z^2 = a⁻¹*z^3 := by simp [pow_succ, mul_comm, mul_left_comm]
      _ = (a*z^2)⁻¹ := by rw [he]; simp [mul_comm]
  refine ⟨a*z^2, ⟨by simp [ha, hz], hnew⟩, ?_⟩
  rintro b ⟨hb, hαb⟩
  have hz' : q (b*(a*z^2)⁻¹) = 1 := by simp [hb, ha, hz]
  have he : b*(a*z^2)⁻¹ = (b*(a*z^2)⁻¹)⁻¹ := by
    calc
      _ = α (b*(a*z^2)⁻¹) := (hfix _ hz').symm
      _ = _ := by rw [map_mul, map_inv, hαb, hnew]; simp [mul_comm]
  exact mul_inv_eq_one.mp (odd_kernel_eq_one q hk hz' he)

variable (q : A →* Coordinates C) (hq : Function.Surjective q)
    (hk : ∀ z, q z = 1 → z^5 = 1)
    (ρ : Equiv.Perm (Fin 5) →* MulAut A)
    (hfix : ∀ σ z, q z = 1 → ρ σ z = z)
    (hact : ∀ σ a, q (ρ σ a) = permute C σ (q a))

include hq hk hfix hact

private theorem root_exists (i j : Fin 5) (u : C) :
    ∃! a, q a = root C i j u ∧ ρ (Equiv.swap i j) a = a⁻¹ := by
  apply inverted_lift q hq hk (ρ (Equiv.swap i j)) (hfix _) (root C i j u)
  intro a ha
  rw [hact, ha, permute_root, Equiv.swap_apply_left, Equiv.swap_apply_right,
    root_reverse]

private def liftRoot (i j : Fin 5) (u : C) : A :=
  (root_exists q hq hk ρ hfix hact i j u).choose

private theorem liftRoot_spec (i j : Fin 5) (u : C) :
    q (liftRoot q hq hk ρ hfix hact i j u) = root C i j u ∧
    ρ (Equiv.swap i j) (liftRoot q hq hk ρ hfix hact i j u) =
      (liftRoot q hq hk ρ hfix hact i j u)⁻¹ :=
  (root_exists q hq hk ρ hfix hact i j u).choose_spec.1

private theorem liftRoot_unique (i j : Fin 5) (u : C) (a : A)
    (ha : q a = root C i j u) (hi : ρ (Equiv.swap i j) a = a⁻¹) :
    a = liftRoot q hq hk ρ hfix hact i j u :=
  (root_exists q hq hk ρ hfix hact i j u).choose_spec.2 a ⟨ha,hi⟩

private def rootHom (i j : Fin 5) : C →* A where
  toFun := liftRoot q hq hk ρ hfix hact i j
  map_one' := (liftRoot_unique q hq hk ρ hfix hact i j 1 1
    (by rw [map_one, root_one]) (by simp)).symm
  map_mul' u v := by
    symm
    apply liftRoot_unique q hq hk ρ hfix hact
    · rw [map_mul, (liftRoot_spec q hq hk ρ hfix hact i j u).1,
        (liftRoot_spec q hq hk ρ hfix hact i j v).1, root_mul]
    · rw [map_mul, (liftRoot_spec q hq hk ρ hfix hact i j u).2,
        (liftRoot_spec q hq hk ρ hfix hact i j v).2, mul_inv_rev, mul_comm]

private theorem rootHom_map (i j : Fin 5) (u : C) :
    q (rootHom q hq hk ρ hfix hact i j u) = root C i j u :=
  (liftRoot_spec q hq hk ρ hfix hact i j u).1

private theorem rootHom_inverted (i j : Fin 5) (u : C) :
    ρ (Equiv.swap i j) (rootHom q hq hk ρ hfix hact i j u) =
      (rootHom q hq hk ρ hfix hact i j u)⁻¹ :=
  (liftRoot_spec q hq hk ρ hfix hact i j u).2

private theorem rootHom_reverse (i j : Fin 5) (u : C) :
    rootHom q hq hk ρ hfix hact j i u = (rootHom q hq hk ρ hfix hact i j u)⁻¹ := by
  symm
  apply liftRoot_unique q hq hk ρ hfix hact
  · rw [map_inv, rootHom_map]
    exact (root_reverse i j u).symm
  · rw [map_inv, Equiv.swap_comm, rootHom_inverted]

private theorem rootHom_same (i : Fin 5) (u : C) :
    rootHom q hq hk ρ hfix hact i i u = 1 := by
  symm
  apply liftRoot_unique q hq hk ρ hfix hact
  · rw [map_one, root_same]
  · simp

private theorem rootHom_action (σ : Equiv.Perm (Fin 5)) (i j : Fin 5) (u : C) :
    ρ σ (rootHom q hq hk ρ hfix hact i j u) =
      rootHom q hq hk ρ hfix hact (σ i) (σ j) u := by
  apply liftRoot_unique q hq hk ρ hfix hact
  · rw [hact, rootHom_map, permute_root]
  · have he : Equiv.swap (σ i) (σ j) * σ = σ * Equiv.swap i j := by
      apply Equiv.ext
      intro k
      exact σ.injective.swap_apply i j k
    change (ρ (Equiv.swap (σ i) (σ j)) * ρ σ) _ = _
    rw [← map_mul, he, map_mul]
    change ρ σ (ρ (Equiv.swap i j) _) = _
    rw [rootHom_inverted, map_inv]

private theorem rootHom_triangle (i j k : Fin 5) (u : C) :
    rootHom q hq hk ρ hfix hact i j u * rootHom q hq hk ρ hfix hact j k u =
      rootHom q hq hk ρ hfix hact i k u := by
  let l := rootHom q hq hk ρ hfix hact
  change l i j u * l j k u = l i k u
  by_cases hij : i = j
  · subst j; simp [l, rootHom_same]
  by_cases hjk : j = k
  · subst k; simp [l, rootHom_same]
  by_cases hik : i = k
  · subst k
    rw [show l j i u = (l i j u)⁻¹ from rootHom_reverse q hq hk ρ hfix hact i j u,
      show l i i u = 1 from rootHom_same q hq hk ρ hfix hact i u, mul_inv_cancel]
  let z := l i j u * l j k u * (l i k u)⁻¹
  have hz : q z = 1 := by
    simp only [z, l, map_mul, map_inv, rootHom_map, root_triangle, mul_inv_cancel]
  have he : z = z⁻¹ := by
    calc
      z = ρ (Equiv.swap i k) z := (hfix _ _ hz).symm
      _ = z⁻¹ := by
        dsimp only [z, l]
        simp only [map_mul, map_inv, rootHom_action, Equiv.swap_apply_left,
          Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) hjk]
        rw [rootHom_reverse q hq hk ρ hfix hact k j,
          rootHom_reverse q hq hk ρ hfix hact j i,
          rootHom_reverse q hq hk ρ hfix hact k i]
        simp [mul_comm, mul_assoc]
  exact mul_inv_eq_one.mp (odd_kernel_eq_one q hk hz he)

private def sectionHom : Coordinates C →* A where
  toFun a := ∏ i : Fin 5, rootHom q hq hk ρ hfix hact i 0 (a.val i)
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib]

private theorem sectionHom_map (a : Coordinates C) :
    q (sectionHom q hq hk ρ hfix hact a) = a := by
  change q (∏ i : Fin 5, rootHom q hq hk ρ hfix hact i 0 (a.val i)) = a
  simp only [map_prod, rootHom_map]
  apply Subtype.ext
  change (∏ i : Fin 5, (root C i 0 (a.val i)).val) = a.val
  simp only [root, Finset.prod_mul_distrib]
  rw [Finset.univ_prod_mulSingle]
  have he : (∏ i : Fin 5, Pi.mulSingle 0 (a.val i)⁻¹) =
      (Pi.mulSingle 0 (∏ i, a.val i)⁻¹ : Fin 5 → C) := by
    simpa only [Finset.prod_inv_distrib, MonoidHom.mulSingle_apply] using
      (map_prod (MonoidHom.mulSingle (fun _ : Fin 5 => C) 0)
        (fun i : Fin 5 => (a.val i)⁻¹) Finset.univ).symm
  rw [he, show ∏ i, a.val i = 1 from a.property]
  simp

private theorem sectionHom_action (σ : Equiv.Perm (Fin 5)) (a : Coordinates C) :
    ρ σ (sectionHom q hq hk ρ hfix hact a) =
      sectionHom q hq hk ρ hfix hact (permute C σ a) := by
  let l := rootHom q hq hk ρ hfix hact
  change ρ σ (∏ i, l i 0 (a.val i)) = ∏ i, l i 0 (a.val (σ⁻¹ i))
  simp only [map_prod, l, rootHom_action]
  have ht (i : Fin 5) : l (σ i) (σ 0) (a.val i) =
      l (σ i) 0 (a.val i) * (l (σ 0) 0 (a.val i))⁻¹ := by
    apply eq_mul_inv_iff_mul_eq.mpr
    exact rootHom_triangle q hq hk ρ hfix hact (σ i) (σ 0) 0 (a.val i)
  change (∏ i, l (σ i) (σ 0) (a.val i)) = _
  simp_rw [ht]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← map_prod]
  rw [show ∏ i, a.val i = 1 from a.property, map_one, inv_one, mul_one]
  simpa using (Equiv.prod_comp σ (fun i => l i 0 (a.val (σ⁻¹ i))))

end
end PermutationLift

open BenderSuzuki.MatrixGroups PerfectCentralCovering

/-- A central kernel of order five permits a section of the determinant-one
norm-one diagonal torus equivariant under every coordinate permutation lift. -/
theorem hasPermutationTorusLift_of_kernel_card_five
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 5 F) (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x^4)
    (_hcard : Nat.card F = 16)
    {E : Type*} [Group E] [Finite E] (d : Cover E J.specialSubgroup)
    (hd : Nat.card d.toMonoidHom.ker = 5) : HasPermutationTorusLift J hJ hconj d := by
  classical
  let C := rootsOfUnity 5 F
  let f := d.toMonoidHom
  let T := torus J hJ hconj
  let A := T.comap f
  let : IsMulCommutative A :=
    torus_preimage_commutative J hJ hconj f d.surjective d.ker_le_center
  let : CommGroup A := IsMulCommutative.instCommGroup
  let e : Coordinates C ≃* T := MonoidHom.ofInjective (diagonal_injective J hJ hconj)
  let q : A →* Coordinates C := e.symm.toMonoidHom.comp (f.subgroupComap T)
  have hq : Function.Surjective q :=
    e.symm.surjective.comp (f.subgroupComap_surjective_of_surjective T d.surjective)
  have hqa (a : A) : diagonal J hJ hconj (q a) = f a :=
    congrArg Subtype.val (e.apply_symm_apply (f.subgroupComap T a))
  have hqker (a : A) (ha : q a = 1) : (a : E) ∈ f.ker := by
    change f a = 1
    rw [← hqa, ha, map_one]
  have hk (a : A) (ha : q a = 1) : a^5 = 1 := by
    apply Subtype.ext
    have hh := pow_card_eq_one' (x := (⟨(a : E), hqker a ha⟩ : f.ker))
    rw [show Nat.card f.ker = 5 from hd] at hh
    exact congrArg (fun z : f.ker => (z : E)) hh
  let P := (permutation J hJ).range
  let N := P.comap f
  let ep : Equiv.Perm (Fin 5) ≃* P := MonoidHom.ofInjective (permutation_injective J hJ)
  let p : N →* Equiv.Perm (Fin 5) := ep.symm.toMonoidHom.comp (f.subgroupComap P)
  have hp : Function.Surjective p :=
    ep.symm.surjective.comp (f.subgroupComap_surjective_of_surjective P d.surjective)
  have hpb (b : N) : permutation J hJ (p b) = f b :=
    congrArg Subtype.val (ep.apply_symm_apply (f.subgroupComap P b))
  have hn (b : N) : (b : E) ∈ normalizer (A : Set E) := by
    apply mem_normalizer_iff.mpr
    intro a
    change f a ∈ T ↔ f ((b : E)*a*(b : E)⁻¹) ∈ T
    simpa only [map_mul, map_inv, ← hpb] using
      mem_normalizer_iff.mp (permutation_mem_normalizer J hJ hconj (p b)) (f a)
  let n : N →* normalizer (A : Set E) := N.subtype.codRestrict _ hn
  let β : N →* MulAut A := A.normalizerMonoidHom.comp n
  have hβ (b : N) (a : A) : (β b a : E) = (b : E)*a*(b : E)⁻¹ := rfl
  have hkill : p.ker ≤ β.ker := by
    intro b hb
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [hβ]
    have hbker : (b : E) ∈ f.ker := by
      change f b = 1
      rw [← hpb, MonoidHom.mem_ker.mp hb, map_one]
    rw [← mem_center_iff.mp (d.ker_le_center hbker) (a : E)]
    simp
  let ρ : Equiv.Perm (Fin 5) →* MulAut A := p.liftOfSurjective hp ⟨β,hkill⟩
  have hρ (b : N) : ρ (p b) = β b := p.liftOfRightInverse_comp_apply _ _ _ b
  have hρval (σ : Equiv.Perm (Fin 5)) (b : E)
      (hb : f b = permutation J hJ σ) (a : A) :
      (ρ σ a : E) = b*a*b⁻¹ := by
    let bN : N := ⟨b, ⟨σ,hb.symm⟩⟩
    have he : p bN = σ :=
      permutation_injective J hJ ((hpb bN).trans hb)
    rw [← he, hρ, hβ]
  have hfix (σ : Equiv.Perm (Fin 5)) (a : A) (ha : q a = 1) : ρ σ a = a := by
    obtain ⟨b,hb⟩ := d.surjective (permutation J hJ σ)
    apply Subtype.ext
    rw [hρval σ b hb a, mem_center_iff.mp (d.ker_le_center (hqker a ha)) b]
    simp
  have hact (σ : Equiv.Perm (Fin 5)) (a : A) :
      q (ρ σ a) = permute C σ (q a) := by
    obtain ⟨b,hb⟩ := d.surjective (permutation J hJ σ)
    apply diagonal_injective J hJ hconj
    rw [hqa, hρval σ b hb, map_mul, map_mul, map_inv, hb, ← hqa,
      permutation_diagonal]
  let s := A.subtype.comp (PermutationLift.sectionHom q hq hk ρ hfix hact)
  refine ⟨s, ?_, ?_⟩
  · apply MonoidHom.ext
    intro a
    change f (PermutationLift.sectionHom q hq hk ρ hfix hact a) = _
    rw [← hqa, PermutationLift.sectionHom_map]
  · intro σ b hb a
    change b*(PermutationLift.sectionHom q hq hk ρ hfix hact a : E)*b⁻¹ = _
    rw [← hρval σ b hb, PermutationLift.sectionHom_action]
    rfl

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Five

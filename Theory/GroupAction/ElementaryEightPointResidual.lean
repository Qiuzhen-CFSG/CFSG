module
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.KernelCard
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Quotient
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupTheory.PPerfectHom

/-!
# Two-perfect point actions on an elementary eight-group

A two-perfect group fixing a nonidentity element of an elementary abelian
8-group has automorphism image of order 1, 3 or 12. The quotient by the
fixed line has dimension two. The actual quotient-action kernel has order
four, and the two-perfect image on the quotient lies in A₃. Thus the image
order divides twelve; a normal index-two Sylow subgroup excludes order six.

At order twelve the faithful action on the four cosets of a Sylow three
subgroup identifies the group with the actual alternating group A₄.
The normal core of that Sylow subgroup is trivial by two-perfectness.

Source application: Aschbacher–Smith, 14.7.6, printed pp.1044–1045 of
refs/quasithin.pdf. The original endpoint application retains the possible
cubic image; its exclusion requires further ambient mathematics.
-/

public noncomputable section
open scoped IsMulCommutative
namespace Theory.GroupAction.ElementaryEightPointResidual
open Subgroup
open Theory.LinearAlgebra.BinaryFivePointStabilizer

private theorem twoPerfect_card_of_dvd_twelve
    {A : Type*} [Group A] [Finite A] (hp : IsPPerfect 2 A)
    (hd : Nat.card A ∣ 12) : Nat.card A = 1 ∨ Nat.card A = 3 ∨ Nat.card A = 12 := by
  have hsmall : Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 3 ∨
      Nat.card A = 4 ∨ Nat.card A = 6 ∨ Nat.card A = 12 := by
    have hh := Nat.mem_divisors.mpr ⟨hd,(by decide : (12 : ℕ) ≠ 0)⟩
    have he : (12 : ℕ).divisors = {1,2,3,4,6,12} := by decide
    rw [he] at hh
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have htwo (hA : IsPGroup 2 A) : Nat.card A = 1 := by
    have hh := hp.hom_eq_one_of_isPGroup hA (MonoidHom.id A)
    have hs : Subsingleton A := ⟨fun a b => by
      have ha := DFunLike.congr_fun hh a
      have hb := DFunLike.congr_fun hh b
      exact ha.trans hb.symm⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨hs,inferInstance⟩
  rcases hsmall with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inl (htwo (IsPGroup.of_card (n := 1) h))
  · exact Or.inr (Or.inl h)
  · exact Or.inl (htwo (IsPGroup.of_card (n := 2) h))
  · let P : Sylow 3 A := Classical.choice inferInstance
    have hc : Nat.card P = 3 := by rw [P.card_eq_multiplicity,h]; decide +kernel
    have hi : (P : Subgroup A).index = 2 := by
      have hh := (P : Subgroup A).card_mul_index
      rw [hc,h] at hh
      omega
    let : (P : Subgroup A).Normal := normal_of_index_eq_two hi
    have hq : IsPGroup 2 (A ⧸ (P : Subgroup A)) := IsPGroup.of_card (n := 1) hi
    have he := hp.hom_eq_one_of_isPGroup hq (QuotientGroup.mk' (P : Subgroup A))
    have htop : (P : Subgroup A) = ⊤ := by
      apply top_unique
      intro a _
      exact (QuotientGroup.eq_one_iff a).mp (DFunLike.congr_fun he a)
    rw [htop,index_top] at hi
    contradiction
  · exact Or.inr (Or.inr h)

/-- A two-perfect image fixing a nonzero vector in a binary three-space
has order one, three or twelve. This uses the actual quotient action. -/
private theorem linear_three_twoPerfect_point_image
    {A E : Type*} [Group A] [Finite A] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (hp : IsPPerfect 2 A)
    (hE : Module.finrank (ZMod 2) E = 3) (z : E) (hz : z ≠ 0)
    (f : A →* stabilizer z) :
    Nat.card f.range = 1 ∨ Nat.card f.range = 3 ∨ Nat.card f.range = 12 := by
  classical
  let : Finite E := Module.finite_of_finite (ZMod 2)
  let q₀ := quotientAction z
  have hdim : Module.finrank (ZMod 2) (QuotientSpace z) = 2 := by
    have hh := (line z).finrank_quotient_add_finrank
    rw [finrank_span_singleton hz,hE] at hh
    change Module.finrank (ZMod 2) (QuotientSpace z) + 1 = 3 at hh
    omega
  let e := (BinaryLinear.SmallParabolicLevi.linearGroupCongr
      (LinearEquiv.ofFinrankEq (QuotientSpace z) (Fin 2 → ZMod 2) (by simpa using hdim))).trans
    BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree
  let q := e.toMonoidHom.comp q₀
  have hq : Function.Surjective q := e.surjective.comp (quotientAction_surjective z)
  have hk : Nat.card q.ker = 4 := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    change Nat.card (kernel z) = 4
    rw [Nat.card_congr (kernelDisplacementEquiv z).toEquiv]
    change Nat.card (QuotientSpace z →ₗ[ZMod 2] line z) = 4
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Module.finrank_linearMap,
      hdim,finrank_span_singleton hz,Nat.card_zmod]
    rfl
  have hc : Nat.card (stabilizer z) = 24 := by
    have hh := q.ker.card_mul_index
    rw [hk,index_ker,MonoidHom.range_eq_top.mpr hq,card_top] at hh
    norm_num [Nat.card_perm,Nat.card_fin,Nat.factorial] at hh
    exact hh.symm
  let B := (alternatingGroup (Fin 3)).comap q
  have hB : B.index = 2 := by rw [index_comap_of_surjective _ hq]; simp
  have hBc : Nat.card B = 12 := by
    have hh := B.card_mul_index
    rw [hB,hc] at hh
    omega
  have hfb : f.range ≤ B := by
    rintro _ ⟨a,rfl⟩
    change q (f a) ∈ alternatingGroup (Fin 3)
    rw [←Equiv.Perm.twoResidual_eq_alternating]
    exact map_pResidual_le 2 (q.comp f) ⟨a,
      by rw [(pResidual_eq_top_iff 2 A).mpr hp]; trivial,rfl⟩
  let : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  apply twoPerfect_card_of_dvd_twelve (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  exact hBc ▸ card_dvd_of_le hfb
/-- A two-perfect group of order twelve is the actual alternating group A₄.
The faithful four-coset action supplies the isomorphism. -/
theorem twoPerfect_twelve_equiv_alternatingFour
    {A : Type*} [Group A] [Finite A] (hp : IsPPerfect 2 A)
    (hc : Nat.card A = 12) : Nonempty (A ≃* alternatingGroup (Fin 4)) := by
  classical
  let P : Sylow 3 A := Classical.choice inferInstance
  have hP : Nat.card P = 3 := by rw [P.card_eq_multiplicity,hc]; decide +kernel
  have hi : (P : Subgroup A).index = 4 := by
    have hh := (P : Subgroup A).card_mul_index
    rw [hP,hc] at hh
    omega
  have hcore : (P : Subgroup A).normalCore = ⊥ := by
    have hd := card_dvd_of_le (P : Subgroup A).normalCore_le
    rw [hP] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with he | he
    · exact (P : Subgroup A).normalCore.eq_bot_iff_card.mpr he
    · have heq : (P : Subgroup A).normalCore = P :=
        eq_of_le_of_card_ge (P : Subgroup A).normalCore_le (by omega)
      let : (P : Subgroup A).Normal := heq ▸ (P : Subgroup A).normalCore_normal
      have hq : IsPGroup 2 (A ⧸ (P : Subgroup A)) := IsPGroup.of_card (n := 2) hi
      have he := hp.hom_eq_one_of_isPGroup hq (QuotientGroup.mk' (P : Subgroup A))
      have htop : (P : Subgroup A) = ⊤ := by
        apply top_unique
        intro a _
        exact (QuotientGroup.eq_one_iff a).mp (DFunLike.congr_fun he a)
      rw [htop,index_top] at hi
      contradiction
  let e : (A ⧸ (P : Subgroup A)) ≃ Fin 4 := Finite.equivFinOfCardEq hi
  let f := e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom A (A ⧸ (P : Subgroup A)))
  have hf : Function.Injective f := e.permCongrHom.injective.comp
    ((MonoidHom.ker_eq_bot_iff _).mp (by
      rw [←(P : Subgroup A).normalCore_eq_ker,hcore]))
  have hfc : Nat.card f.range = 12 := (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hc
  have hfi : f.range.index = 2 := by
    have hh := f.range.card_mul_index
    rw [hfc] at hh
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh
    omega
  exact ⟨(MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hfi))⟩

/-- The same trichotomy for a literal automorphism action on an elementary
abelian eight-group, fixing a specified nonidentity element. -/
theorem elementary_eight_twoPerfect_point_image
    {A E : Type*} [Group A] [Finite A] [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hp : IsPPerfect 2 A) (hE : Nat.card E = 8)
    (f : A →* MulAut E) (z : E) (hz : z ≠ 1) (hfix : ∀ a, f a z = z) :
    Nat.card f.range = 1 ∨ Nat.card f.range = 3 ∨ Nat.card f.range = 12 := by
  let α : MulAut E ≃* (Additive E ≃ₗ[ZMod 2] Additive E) :=
    { toFun := fun a => { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
      invFun := fun a => MulEquiv.toAdditive.symm a.toAddEquiv
      left_inv := by intro a; ext; rfl
      right_inv := by intro a; ext; rfl
      map_mul' := by intro a b; ext; rfl }
  let f₀ := α.toMonoidHom.comp f
  let g : A →* stabilizer (Additive.ofMul z) := f₀.codRestrict _ hfix
  have hd : Module.finrank (ZMod 2) (Additive E) = 3 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hh
    rw [hE,Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) hh.symm
  have hh := linear_three_twoPerfect_point_image hp hd (Additive.ofMul z) hz g
  have he : Nat.card g.range = Nat.card f.range := by
    have hk : g.ker = f.ker := by
      ext a
      change g a = 1 ↔ f a = 1
      rw [Subtype.ext_iff]
      change α (f a) = 1 ↔ f a = 1
      rw [←α.map_one,α.injective.eq_iff]
    rw [←index_ker,hk,index_ker]
  rwa [he] at hh

end Theory.GroupAction.ElementaryEightPointResidual

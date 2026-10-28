module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.Local
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Inner action from component containment and the S₃ shadow

Every conjugate of the actual relative component L is either L or centralizes
L. Consequently the entire S-span is contained in L C_G(L), proving literal
inner action in alternative (i) of 15.3.43. We also give the elementwise
implementation of this containment, and compare it with the earlier section
kernel when the two-core is central.

The S₃ shadow also kills every cubic element under an abelian action of
Y₊S. An involution in S₃ inverts its cubic elements; lifting that conjugation
puts the square of the abelian image in a two-group. Its cube is also trivial,
so the image is trivial. Theta generation then kills the whole Y₊ image.
In particular, an abelian actual outer automorphism group suffices for
literal inner action on L.

The rank-one quotient-model and signed diagonal alternatives are not settled
here. Their producers must use the S₃ setup in `Local`, without importing the
rank-two hypothesis of 15.3.12 or the later 15.3.35 and 15.3.38 conclusions.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the paragraph
between 15.3.43(d) and (e), printed p.1139, and component calculus A.3.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion
variable {G : Type*} [Group G]

/-- Component calculus inside I controls the S-span in the ambient group. -/
theorem component_orbit_le_inner {I L S : Subgroup G} (hLI : L ≤ I) (hSI : S ≤ I)
    (hL : IsComponent I (L.subgroupOf I)) :
    localSpan L S ≤ L ⊔ centralizer (L : Set G) := by
  apply (closure_le _).mpr
  rintro x ⟨s, hs, l, hl, rfl⟩
  let a : I := ⟨s, hSI hs⟩
  let b : I := ⟨l, hLI hl⟩
  let K := (L.subgroupOf I).map (MulAut.conj a).toMonoidHom
  have hb : a * b * a⁻¹ ∈ K := mem_map.mpr ⟨b, hl, rfl⟩
  by_cases he : K = L.subgroupOf I
  · have hx : a * b * a⁻¹ ∈ L.subgroupOf I := he ▸ hb
    exact mem_sup_left hx
  · have hc := (hL.map_conj a).commutator_eq_bot_of_ne hL he
    apply mem_sup_right
    apply mem_centralizer_iff.mpr
    intro z hz
    have hzI : (⟨z, hLI hz⟩ : I) ∈ L.subgroupOf I := hz
    exact congrArg Subtype.val (mem_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hc hb) ⟨z, hLI hz⟩ hzI)

/-- The product containment means literal conjugation by elements of L. -/
theorem le_inner_iff_implemented (Y L : Subgroup G) :
    Y ≤ L ⊔ centralizer (L : Set G) ↔
      ∀ y ∈ Y, ∃ l ∈ L, ∀ x ∈ L, y * x * y⁻¹ = l * x * l⁻¹ := by
  constructor
  · intro h y hy
    have hm : y ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L (centralizer (L : Set G))
        (Subgroup.centralizer_le_normalizer _)]
      exact h hy
    obtain ⟨l, hl, c, hc, rfl⟩ := hm
    refine ⟨l, hl, ?_⟩
    intro x hx
    have he := mem_centralizer_iff.mp hc x hx
    calc
      (l * c) * x * (l * c)⁻¹ = l * (c * x) * c⁻¹ * l⁻¹ := by group
      _ = l * (x * c) * c⁻¹ * l⁻¹ := by rw [he]
      _ = l * x * l⁻¹ := by group
  · intro h y hy
    obtain ⟨l, hl, he⟩ := h y hy
    have hc : l⁻¹ * y ∈ centralizer (L : Set G) := by
      apply mem_centralizer_iff.mpr
      intro x hx
      calc
        x * (l⁻¹ * y) = l⁻¹ * (l * x * l⁻¹) * y := by group
        _ = l⁻¹ * (y * x * y⁻¹) * y := by rw [he x hx]
        _ = (l⁻¹ * y) * x := by group
    have hh := (L ⊔ centralizer (L : Set G)).mul_mem (mem_sup_left hl)
      (mem_sup_right hc)
    simpa only [mul_inv_cancel_left] using hh

/-- The subgroup of elements acting innerly on L normalizes L. -/
theorem normalizes_of_le_inner {Y L : Subgroup G}
    (h : Y ≤ L ⊔ centralizer (L : Set G)) : Y ≤ normalizer (L : Set G) :=
  h.trans (sup_le L.le_normalizer (Subgroup.centralizer_le_normalizer _))

/-- Alternative (i) gives literal inner action on the chosen component even
when S permutes multiple components. No component-containment assumption is used. -/
theorem inner_of_contained_alternative {Yplus S M I L : Subgroup G}
    (h : LocalSetup Yplus S M I L)
    (halt : Yplus ≤ theta I ∧ theta I = localSpan L S) :
    Yplus ≤ L ⊔ centralizer (L : Set G) ∧ Yplus ≤ normalizer (L : Set G) := by
  have hi := (halt.1.trans halt.2.le).trans
    (component_orbit_le_inner h.component_le h.sylow_le_overgroup h.component)
  exact ⟨hi, normalizes_of_le_inner hi⟩

/-- With a perfect component and central two-core, section-inner witnesses
already implement literal inner automorphisms. This handles central two-covers. -/
theorem le_inner_of_section_inner {Y L : Subgroup G} [Group.IsPerfect L]
    (hcore : pCore 2 L ≤ center L)
    (hinner : ComponentIntersection.InducesInnerOnTwoCoreQuotient Y L) :
    Y ≤ L ⊔ centralizer (L : Set G) := by
  intro y hy
  obtain ⟨l, hl, hc⟩ := hinner y hy
  rw [sectionCentralizer_eq_centralizer_of_perfect hcore] at hc
  have hm := (L ⊔ centralizer (L : Set G)).mul_mem (mem_sup_left hl) (mem_sup_right hc)
  simpa only [mul_inv_cancel_left] using hm

variable {H A : Type*} [Group H] [Group A] [IsMulCommutative A]

/-- In an extension of S₃ by a two-group, every cubic element is killed
by every homomorphism to an abelian group. -/
theorem cubic_map_eq_one_of_s3_two_kernel
    (q : H →* Equiv.Perm (Fin 3)) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (f : H →* A) (y : H) (hy : y ^ 3 = 1) : f y = 1 := by
  have hqi : ∃ t : Equiv.Perm (Fin 3), t * q y * t⁻¹ = (q y)⁻¹ := by
    exact (by decide : ∀ a : Equiv.Perm (Fin 3), ∃ t, t * a * t⁻¹ = a⁻¹) (q y)
  obtain ⟨t, ht⟩ := hqi
  obtain ⟨s, rfl⟩ := hq t
  let z := s * y * s⁻¹ * y
  have hz : z ∈ q.ker := by
    change q z = 1
    simp only [z, map_mul, map_inv, ht, inv_mul_cancel]
  obtain ⟨n, hn⟩ := hk (⟨z, hz⟩ : q.ker)
  have hzpow : z ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have hfz : f z = f y ^ 2 := by
    simp only [z, map_mul, map_inv]
    rw [mul_comm' (f s) (f y), mul_assoc (f y) (f s), mul_inv_cancel,
      mul_one, pow_two]
  have hd2 : orderOf (f y) ∣ 2 * 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, ← hfz, ← map_pow, hzpow, map_one]
  have hd3 : orderOf (f y) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hy, map_one])
  have hcop : Nat.Coprime (2 * 2 ^ n) 3 :=
    (by decide : Nat.Coprime 2 3).mul_left ((by decide : Nat.Coprime 2 3).pow_left n)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd2 hd3)

variable [Finite G] {Yplus S M I L : Subgroup G}

omit [Finite G] in
/-- Theta generation promotes the cubic calculation to all of Y₊. -/
theorem LocalSetup.abelian_action_trivial (h : LocalSetup Yplus S M I L)
    (f : (Yplus ⊔ S : Subgroup G) →* A) (y : Yplus) :
    f (inclusion le_sup_left y) = 1 := by
  obtain ⟨e⟩ := h.shadow
  let J := Yplus ⊔ S
  let q : J →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 J := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 J) x) = 1 ↔ x ∈ pCore 2 J
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  let D : Subgroup G := f.ker.map J.subtype
  have hYD : Yplus ≤ D := by
    rw [← h.theta_eq]
    apply (closure_le _).mpr
    intro x hx
    have hxY : x ∈ Yplus := h.theta_eq ▸ subset_closure hx
    let xJ : J := ⟨x, mem_sup_left hxY⟩
    have hx3 : xJ ^ 3 = 1 := by
      apply Subtype.ext
      change x ^ 3 = 1
      rw [← hx.2, pow_orderOf_eq_one]
    exact ⟨xJ, cubic_map_eq_one_of_s3_two_kernel q hq (hker ▸ pCore_isPGroup)
      f xJ hx3, rfl⟩
  obtain ⟨z, hz, he⟩ := hYD y.property
  have heq : z = inclusion le_sup_left y := Subtype.ext he
  exact heq ▸ hz

omit [Group H] [Group A] [IsMulCommutative A] in
/-- In the single-component case, an abelian actual outer group forces
literal inner action. The outer-group calculation remains a model obligation. -/
theorem LocalSetup.inner_of_abelian_outer (h : LocalSetup Yplus S M I L)
    (horbit : L = localSpan L S) (ho : IsMulCommutative (MulAut.Outer L)) :
    Yplus ≤ L ⊔ centralizer (L : Set G) := by
  let := ho
  let a : (Yplus ⊔ S : Subgroup G) →* MulAut L :=
    L.normalizerMonoidHom.comp (inclusion (h.join_normalizes horbit))
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup L)).comp a
  apply (le_inner_iff_implemented Yplus L).mpr
  intro y hy
  have hi : a (inclusion le_sup_left (⟨y, hy⟩ : Yplus)) ∈ MulAut.innerSubgroup L :=
    (QuotientGroup.eq_one_iff _).mp (h.abelian_action_trivial f ⟨y, hy⟩)
  obtain ⟨l, hl⟩ := hi
  refine ⟨l, l.property, ?_⟩
  intro x hx
  have he := congrArg (fun b : MulAut L => (b ⟨x, hx⟩ : G)) hl
  exact he.symm

end CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion

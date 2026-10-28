module

public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import Theory.SpecificGroups.AlternatingFiveTriangle
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Splitting every extension by the natural SL₂(4) module

The upper involution has its fixed space equal to its norm image, so an
arbitrary lift can be corrected to an involution. The two odd actors in a
specified (2,3,5) pair are fixed-point-free on the kernel, forcing the cube
and fifth power of their lifts to be trivial. The proved icosahedral
presentation supplies an actual A₅ subgroup. Its intersection with the
original elementary-sixteen kernel is trivial, and the orders give a
complement. The kernel coordinates and original quotient are retained.

This is a group-extension statement for the scalar-restricted natural
F₄² module, distinct from the five-point binary augmentation module. No
splitting premise, cohomology classification, or ambient local-type input
is used.
-/

public noncomputable section
open Subgroup Matrix
namespace Representation.SL2FourNaturalExtensions
open SL2FourNatural

private def triangleOdd : SL :=
  ⟨!![0, QuadraticAlgebra.omega ^ 2; QuadraticAlgebra.omega, 1], by decide +kernel⟩

private theorem triangle_relations : (upper 1 : SL) ≠ 1 ∧
    (upper 1 : SL) ^ 2 = 1 ∧ triangleOdd ^ 3 = 1 ∧
    (upper 1 * triangleOdd) ^ 5 = 1 := by decide +kernel

private theorem triangle_fixed :
    (∀ v : V, action triangleOdd v = v → v = 0) ∧
    (∀ v : V, action (upper 1 * triangleOdd) v = v → v = 0) := by decide +kernel

private theorem upper_norm (v : V) (hv : action (upper 1) v = v) :
    ∃ w : V, w + action (upper 1) w = v := by
  have hv1 : v 1 = 0 := by
    have hh := congrFun hv 0
    simpa only [upper_action, Fin.isValue, cons_val_zero, one_mul, add_eq_left] using hh
  refine ⟨![0, v 0], ?_⟩
  rw [upper_action]
  funext i
  fin_cases i <;> simp [hv1, CharTwo.add_self_eq_zero]

variable {G : Type*} [Group G]

private theorem lift_pow_eq_one (q : G →* SL)
    (e : q.ker ≃* Multiplicative V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (action (q g) (e v).toAdd))
    (g : G) (d : SL) (hg : q g = d) (n : ℕ) (hd : d ^ n = 1)
    (hfixed : ∀ v : V, action d v = v → v = 0) : g ^ n = 1 := by
  let k : q.ker := ⟨g ^ n, by change q (g ^ n) = 1; rw [map_pow, hg, hd]⟩
  have hk : MulAut.conjNormal g k = k := by
    apply Subtype.ext
    change g * g ^ n * g⁻¹ = g ^ n
    group
  have hfix := congrArg e hk
  rw [he, hg] at hfix
  have hv := hfixed (e k).toAdd (congrArg Multiplicative.toAdd hfix)
  have hk1 : k = 1 := e.injective (by
    rw [map_one]
    exact congrArg Multiplicative.ofAdd hv)
  exact congrArg Subtype.val hk1

private theorem upper_lift (q : G →* SL) (hq : Function.Surjective q)
    (e : q.ker ≃* Multiplicative V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (action (q g) (e v).toAdd)) :
    ∃ x : G, q x = upper 1 ∧ x ^ 2 = 1 := by
  obtain ⟨x, hx⟩ := hq (upper 1)
  let s : q.ker := ⟨x ^ 2, by
    change q (x ^ 2) = 1
    rw [map_pow, hx, triangle_relations.2.1]⟩
  have hs : MulAut.conjNormal x s = s := by
    apply Subtype.ext
    change x * x ^ 2 * x⁻¹ = x ^ 2
    group
  have hsf := congrArg e hs
  rw [he, hx] at hsf
  obtain ⟨w, hw⟩ := upper_norm (e s).toAdd (congrArg Multiplicative.toAdd hsf)
  let p := e.symm (Multiplicative.ofAdd w)
  have hep : e p = Multiplicative.ofAdd w := e.apply_symm_apply _
  have hk : p * MulAut.conjNormal x p * s = 1 := by
    apply e.injective
    rw [map_mul, map_mul, he, hx, hep, map_one]
    change w + action (upper 1) w + (e s).toAdd = 0
    rw [hw]
    funext i
    exact CharTwo.add_self_eq_zero _
  refine ⟨(p : G) * x, ?_, ?_⟩
  · rw [map_mul, show q (p : G) = 1 from p.property, one_mul, hx]
  · have hh := congrArg Subtype.val hk
    change (p : G) * (x * (p : G) * x⁻¹) * x ^ 2 = 1 at hh
    calc
      ((p : G) * x) ^ 2 = (p : G) * (x * (p : G) * x⁻¹) * x ^ 2 := by simp only [pow_two]; group
      _ = 1 := hh

/-- Every finite extension of SL₂(4) by its marked natural binary module
has a complement to its literal kernel. -/
theorem exists_complement [Finite G] (q : G →* SL) (hq : Function.Surjective q)
    (e : q.ker ≃* Multiplicative V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (action (q g) (e v).toAdd)) :
    ∃ K : Subgroup G, q.ker.IsComplement' K := by
  obtain ⟨x, hx, hx2⟩ := upper_lift q hq e he
  obtain ⟨y, hy⟩ := hq triangleOdd
  have hx1 : x ≠ 1 := by
    intro hh
    exact triangle_relations.1 (hx.symm.trans (by rw [hh, map_one]))
  have hy3 : y ^ 3 = 1 :=
    lift_pow_eq_one q e he y triangleOdd hy 3 triangle_relations.2.2.1 triangle_fixed.1
  have hxy5 : (x * y) ^ 5 = 1 :=
    lift_pow_eq_one q e he (x * y) (upper 1 * triangleOdd)
      (by rw [map_mul, hx, hy]) 5 triangle_relations.2.2.2 triangle_fixed.2
  obtain ⟨f, hf⟩ := alternatingGroup.exists_injective_hom_of_triangle x y hx1 hx2 hy3 hxy5
  have hAlt : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hSL : Nat.card SL = 60 :=
    (Nat.card_congr alternatingFiveEquiv.toEquiv).trans hAlt
  have hK : Nat.card f.range = 60 := (Nat.card_congr (Equiv.ofInjective f hf)).symm.trans hAlt
  have hker : Nat.card q.ker = 16 := by
    rw [Nat.card_congr e.toEquiv]
    exact (Nat.card_eq_fintype_card (α := V)).trans card_vector
  have hqi : Function.Injective (q.comp f) := by
    apply (q.comp f).ker_eq_bot_iff.mp
    rcases (inferInstance : (q.comp f).ker.Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · have hr : f.range ≤ q.ker := by
        rintro _ ⟨a, rfl⟩
        exact (show a ∈ (q.comp f).ker from hh ▸ mem_top a)
      have hc := card_le_of_le hr
      rw [hK, hker] at hc
      omega
  have hdis : Disjoint q.ker f.range := by
    apply disjoint_def.mpr
    intro g hg hgR
    obtain ⟨a, rfl⟩ := hgR
    have ha : a = 1 := hqi (by simpa only [MonoidHom.comp_apply, map_one] using (show q (f a) = 1 from hg))
    rw [ha, map_one]
  have hidx : q.ker.index = 60 := by
    rw [index_eq_card, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv]
    exact hSL
  refine ⟨f.range, isComplement'_of_card_mul_and_disjoint ?_ hdis⟩
  simpa only [hK, ← hidx] using q.ker.card_mul_index

/-- The complement is identified by the original quotient map, preserving
the original natural kernel marking for later split-extension coordinates. -/
theorem exists_marked_complement [Finite G] (q : G →* SL) (hq : Function.Surjective q)
    (e : q.ker ≃* Multiplicative V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (action (q g) (e v).toAdd)) :
    ∃ K : Subgroup G, q.ker.IsComplement' K ∧
      ∃ k : K ≃* SL, ∀ x : K, k x = q x := by
  obtain ⟨K, hK⟩ := exists_complement q hq e he
  let a := QuotientGroup.quotientKerEquivOfSurjective q hq
  let k := hK.symm.QuotientMulEquiv.symm.trans a
  refine ⟨K, hK, k, ?_⟩
  intro x
  have hh : hK.symm.QuotientMulEquiv.symm x = QuotientGroup.mk' q.ker x := by
    apply hK.symm.QuotientMulEquiv.injective
    rw [MulEquiv.apply_symm_apply, quotientMulEquiv_mk_apply_of_isComplement']
  change a (hK.symm.QuotientMulEquiv.symm x) = q x
  rw [hh]
  rfl

end Representation.SL2FourNaturalExtensions

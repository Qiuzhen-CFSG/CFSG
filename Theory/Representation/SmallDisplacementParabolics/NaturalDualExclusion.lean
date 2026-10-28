module
public import Theory.Representation.SmallDisplacementParabolics.Models
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.PointCores
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Structure
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Outer.Orders

/-!
# Excluding the natural-plus-dual partner chief models

A Sylow-fixed nonzero vector in degrees four or five cannot be pure: its
stabilizer would lie in the index-two inner group. A nonsingular pair also
has a stabilizer of even index, so cannot be fixed by the full Sylow.
For an incident pair, restrict to the covector kernel. The restriction
kernel is parametrized by the displacement of a complement vector, and
the restriction image is the point stabilizer on that hyperplane. This
gives inner stabilizer orders 192 and 21504. The full stabilizer has at
most two inner cosets, and its order is therefore not divisible by nine.

The prescribed two-core quotient of X has order 72, forcing nine to divide
its order. The contradiction excludes the literal coordinate action and
then transports through the actual actor isomorphism and intertwiner.
No order-72 assertion about X itself is used.

Source: Aschbacher--Smith, original 15.2.27(2), printed p.1119 (PDF p.1136),
using the natural-plus-dual stabilizer geometry of H.9, pp.389--390.
-/

public noncomputable section
open Subgroup BinaryLinear
namespace Representation.SmallDisplacementParabolics.NaturalDualExclusion
open BinaryNaturalDual BinaryNaturalDual.VectorStabilizers
open BinaryNaturalDual.VectorStabilizers.PointCores
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem restriction_kernel_fixes {x : V} {f : Module.Dual (ZMod 2) V}
    (h : f x = 0) (g : (incidentRestriction h).ker) (v : f.ker) : g.val.val v = v := by
  have he := congrArg (fun a : Pure.pointStabilizer (⟨x,h⟩ : f.ker) => (a.val v : V)) g.property
  exact he

private def kernelEvaluation {x t : V} {f : Module.Dual (ZMod 2) V} (h : f x = 0) :
    (incidentRestriction h).ker → f.ker := fun g =>
  ⟨g.val.val t - t, by
    rw [LinearMap.mem_ker, map_sub, g.val.property.2 t, sub_self]⟩

private theorem kernelEvaluation_injective {x t : V} {f : Module.Dual (ZMod 2) V}
    (h : f x = 0) (ht : f t = 1) : Function.Injective (kernelEvaluation (t := t) h) := by
  intro g k he
  have ht' : g.val.val t = k.val.val t := sub_left_injective (congrArg Subtype.val he)
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hg := restriction_kernel_fixes h g (kernelProjection ht v)
  have hk := restriction_kernel_fixes h k (kernelProjection ht v)
  change g.val.val (v - f v • t) = v - f v • t at hg
  change k.val.val (v - f v • t) = v - f v • t at hk
  rw [map_sub, map_smul] at hg hk
  rw [ht'] at hg
  exact sub_left_injective (hg.trans hk.symm)

private theorem kernelEvaluation_surjective {x t : V} {f : Module.Dual (ZMod 2) V}
    (h : f x = 0) (ht : f t = 1) : Function.Surjective (kernelEvaluation (t := t) h) := by
  intro u
  let a := transvection (u : V) f u.property
  have ha : a ∈ pairStabilizer x f := by
    constructor
    · change x + f x • (u : V) = x
      rw [h, zero_smul, add_zero]
    · intro v
      change f (v + f v • (u : V)) = f v
      simp only [map_add, map_smul, show f (u : V) = 0 from u.property, smul_zero, add_zero]
  have hk : (⟨a,ha⟩ : pairStabilizer x f) ∈ (incidentRestriction h).ker := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change (v : V) + f (v : V) • (u : V) = v
    rw [show f (v : V) = 0 from v.property, zero_smul, add_zero]
  refine ⟨⟨⟨a,ha⟩,hk⟩, ?_⟩
  apply Subtype.ext
  change t + f t • (u : V) - t = u
  rw [ht, one_smul, add_sub_cancel_left]

/-- The kernel of restriction to the marked hyperplane has precisely one
free hyperplane vector, the displacement of a complement vector. -/
theorem incidentRestriction_kernel_card {x : V} {f : Module.Dual (ZMod 2) V}
    (hf : f ≠ 0) (h : f x = 0) : Nat.card (incidentRestriction h).ker = Nat.card f.ker := by
  have ht : ∃ t, f t ≠ 0 := by
    by_contra! ht
    exact hf (LinearMap.ext ht)
  obtain ⟨t, ht⟩ := ht
  have ht1 : f t = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ ht
  exact Nat.card_congr (Equiv.ofBijective (kernelEvaluation (t := t) h)
    ⟨kernelEvaluation_injective h ht1, kernelEvaluation_surjective h ht1⟩)


open Theory.LinearAlgebra BinaryLinear.OuterCyclic

private theorem point_card [FiniteDimensional (ZMod 2) V] {x : V} (hx : x ≠ 0) :
    Nat.card (Pure.pointStabilizer x) =
      2 ^ (Module.finrank (ZMod 2) V - 1) *
        Nat.card (LinearGroup (Module.finrank (ZMod 2) V - 1)) := by
  let Q := Pure.pointQuotient x
  have hd : Module.finrank (ZMod 2) Q = Module.finrank (ZMod 2) V - 1 := by
    have hh := (Submodule.span (ZMod 2) {x}).finrank_quotient_add_finrank
    rw [finrank_span_singleton hx] at hh
    change Module.finrank (ZMod 2) Q + 1 = Module.finrank (ZMod 2) V at hh
    omega
  let e : Q ≃ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) V - 1) → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hd, Module.finrank_pi, Fintype.card_fin])
  have he : (Pure.pointKernel x).index = Nat.card (LinearGroup (Module.finrank (ZMod 2) V - 1)) :=
    Nat.card_congr ((BinaryFivePointStabilizer.quotientEquiv x).trans (Pure.linearGroupCongr e)).toEquiv
  rw [← (Pure.pointKernel x).card_mul_index, Pure.pointKernel_card hx, he]

/-- Order of an incident pair stabilizer, through its literal restriction
map to the marked hyperplane. -/
theorem incident_pair_card [FiniteDimensional (ZMod 2) V]
    {x : V} {f : Module.Dual (ZMod 2) V} (hx : x ≠ 0) (hf : f ≠ 0) (h : f x = 0) :
    Nat.card (pairStabilizer x f) = Nat.card f.ker *
      (2 ^ (Module.finrank (ZMod 2) f.ker - 1) *
        Nat.card (LinearGroup (Module.finrank (ZMod 2) f.ker - 1))) := by
  have hi : (incidentRestriction h).ker.index = Nat.card (Pure.pointStabilizer (⟨x,h⟩ : f.ker)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (incidentRestriction_surjective hf h)).toEquiv
  rw [← (incidentRestriction h).ker.card_mul_index, incidentRestriction_kernel_card hf h, hi,
    point_card (show (⟨x,h⟩ : f.ker) ≠ 0 from fun he => hx (congrArg Subtype.val he))]


private instance finiteLinear (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : BinaryLinear.OuterCyclic.Space n → BinaryLinear.OuterCyclic.Space n)) DFunLike.coe_injective

private instance finiteAut (n : ℕ) : Finite (MulAut (LinearGroup n)) :=
  Finite.of_injective (fun g : MulAut (LinearGroup n) => (g : LinearGroup n → LinearGroup n))
    DFunLike.coe_injective

private theorem linear_card_two : Nat.card (LinearGroup 2) = 6 := by
  rw [← Nat.card_congr (matrixEquivLinear 2).toEquiv, Matrix.card_GL_field]
  decide
private theorem linear_card_three : Nat.card (LinearGroup 3) = 168 := by
  rw [← Nat.card_congr (matrixEquivLinear 3).toEquiv, Matrix.card_GL_field]
  decide
private theorem linear_card_four : Nat.card (LinearGroup 4) = 20160 := by
  rw [← Nat.card_congr (matrixEquivLinear 4).toEquiv, Matrix.card_GL_field]
  decide
private theorem linear_card_five : Nat.card (LinearGroup 5) = 9999360 := by
  rw [← Nat.card_congr (matrixEquivLinear 5).toEquiv, Matrix.card_GL_field]
  decide

private theorem automorphism_card {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n) :
    Nat.card (MulAut (LinearGroup n)) = 2 * Nat.card (LinearGroup n) := by
  let c : LinearGroup n →* MulAut (LinearGroup n) := MulAut.conj
  let e : LinearGroup n ≃* MulAut.innerSubgroup (LinearGroup n) :=
    MulEquiv.ofBijective c.rangeRestrict
      ⟨fun a b he => inner_injective d (congrArg Subtype.val he), c.rangeRestrict_surjective⟩
  have hc : Nat.card (MulAut.innerSubgroup (LinearGroup n)) = Nat.card (LinearGroup n) :=
    (Nat.card_congr e.toEquiv).symm
  rw [← (MulAut.innerSubgroup (LinearGroup n)).index_mul_card, innerSubgroup_index hn d, hc]

private theorem incident_card_four {x : BinaryLinear.OuterCyclic.Space 4} {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space 4)}
    (hx : x ≠ 0) (hf : f ≠ 0) (h : f x = 0) : Nat.card (pairStabilizer x f) = 192 := by
  have hd : Module.finrank (ZMod 2) f.ker = 3 := by
    have hh : Module.finrank (ZMod 2) f.ker + 1 = 4 := by
      simpa only [Module.finrank_pi, Fintype.card_fin] using
        Module.Dual.finrank_ker_add_one_of_ne_zero hf
    omega
  rw [incident_pair_card hx hf h, Module.natCard_eq_pow_finrank (K := ZMod 2), hd, Nat.card_zmod]
  norm_num [linear_card_two]

private theorem incident_card_five {x : BinaryLinear.OuterCyclic.Space 5} {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space 5)}
    (hx : x ≠ 0) (hf : f ≠ 0) (h : f x = 0) : Nat.card (pairStabilizer x f) = 21504 := by
  have hd : Module.finrank (ZMod 2) f.ker = 4 := by
    have hh : Module.finrank (ZMod 2) f.ker + 1 = 5 := by
      simpa only [Module.finrank_pi, Fintype.card_fin] using
        Module.Dual.finrank_ker_add_one_of_ne_zero hf
    omega
  rw [incident_pair_card hx hf h, Module.natCard_eq_pow_finrank (K := ZMod 2), hd, Nat.card_zmod]
  norm_num [linear_card_three]

private theorem full_card_dvd_twice_pair {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) (x : BinaryLinear.OuterCyclic.Space n) (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) :
    Nat.card (fullStabilizer d (x,f)) ∣ 2 * Nat.card (pairStabilizer x f) := by
  have he : innerInFull d (x,f) =
      (MulAut.innerSubgroup (LinearGroup n)).subgroupOf (fullStabilizer d (x,f)) := by
    ext a
    exact mem_innerInFull d (x,f) a
  have hi : (innerInFull d (x,f)).index ∣ 2 := by
    rw [he]
    exact (relIndex_dvd_index_of_normal (MulAut.innerSubgroup (LinearGroup n))
      (fullStabilizer d (x,f))).trans (by rw [innerSubgroup_index hn d])
  have hc : Nat.card (innerInFull d (x,f)) = Nat.card (pairStabilizer x f) :=
    Nat.card_congr ((innerInFullEquiv d (x,f)).trans (innerStabilizerEquivPair d x f)).toEquiv
  rw [← (innerInFull d (x,f)).index_mul_card, ← hc]
  exact Nat.mul_dvd_mul hi dvd_rfl

private theorem pure_covector_le_inner {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (hf : f ≠ 0) :
    fullStabilizer d (0,f) ≤ MulAut.innerSubgroup (LinearGroup n) := by
  intro a ha
  obtain ⟨g,rfl | rfl⟩ := inner_graph hn a
  · exact ⟨g,rfl⟩
  · have he := congrArg Prod.snd ha
    change (d.representation (graphLinear n * MulAut.conj g) (0,f)).2 = f at he
    rw [map_mul, Module.End.mul_apply, d.on_inner, d.on_graph,
      naturalDualRepresentation_apply, coordinateSwap_apply, map_zero, map_zero] at he
    exact (hf he.symm).elim

private theorem sylow_not_le_inner {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) (S : Sylow 2 (MulAut (LinearGroup n))) :
    ¬ (S : Subgroup (MulAut (LinearGroup n))) ≤ MulAut.innerSubgroup (LinearGroup n) := by
  intro hs
  have hd := index_dvd_of_le hs
  rw [innerSubgroup_index hn d] at hd
  exact S.not_dvd_index hd

/-- The marked vector-stabilizer test excludes both natural-plus-dual rows.
Only the quotient of X by its two-core is identified with the order-72 group. -/
theorem coordinate_exclusion {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    (S : Sylow 2 (MulAut (LinearGroup n))) (X : Subgroup (MulAut (LinearGroup n)))
    (hSX : (S : Subgroup (MulAut (LinearGroup n))) ≤ X)
    (hX : Nonempty ((X ⧸ pCore 2 X) ≃* RegularWreathProduct (Equiv.Perm (Fin 3))
      (Multiplicative (ZMod 2)))) (w : CoordinateSpace n) (hw : w ≠ 0)
    (hfix : ∀ g ∈ X, d.representation g w = w) : False := by
  rcases w with ⟨x,f⟩
  have hXC : X ≤ fullStabilizer d (x,f) := hfix
  have hSC := hSX.trans hXC
  have hx : x ≠ 0 := by
    intro he
    subst x
    have hf : f ≠ 0 := fun he => hw (Prod.ext rfl he)
    exact sylow_not_le_inner hn d S (hSC.trans (pure_covector_le_inner hn d hf))
  have hf : f ≠ 0 := by
    intro he
    subst f
    exact sylow_not_le_inner hn d S (hSC.trans (pure_fullStabilizer_le_inner hn d hx))
  have hpair : f x = 0 := by
    by_contra hh
    have h1 : f x = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hh
    have hi := (fullStabilizer d (x,f)).card_mul_index
    have hdiv := index_dvd_of_le hSC
    have htwo : 2 ∣ (fullStabilizer d (x,f)).index := by
      rcases hn with rfl | rfl
      · rw [fullStabilizer_card_four d h1, automorphism_card (Or.inl rfl) d,
          linear_card_four] at hi
        have he : (fullStabilizer d (x,f)).index = 120 := by omega
        rw [he]
        decide
      · rw [fullStabilizer_card_five d h1, automorphism_card (Or.inr rfl) d,
          linear_card_five] at hi
        have he : (fullStabilizer d (x,f)).index = 496 := by omega
        rw [he]
        decide
    exact S.not_dvd_index (htwo.trans hdiv)
  obtain ⟨eX⟩ := hX
  have hcX : Nat.card (X ⧸ pCore 2 X) = 72 := by
    rw [Nat.card_congr eX.toEquiv, RegularWreathProduct.card, Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  have h9 : 9 ∣ Nat.card X :=
    (show 9 ∣ Nat.card (X ⧸ pCore 2 X) by rw [hcX]; decide).trans (card_quotient_dvd_card _)
  have hc := (card_dvd_of_le hXC).trans (full_card_dvd_twice_pair hn d x f)
  have hbad := h9.trans hc
  rcases hn with rfl | rfl
  · rw [incident_card_four hx hf hpair] at hbad
    norm_num at hbad
  · rw [incident_card_five hx hf hpair] at hbad
    norm_num at hbad


/-- Exclusion on an arbitrary carrier, using the actual actor isomorphism
and intertwining equivalence rather than a group-family tag. -/
theorem false_of_equiv {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    (e : D ≃* MulAut (LinearGroup n)) (f : ρ.Equiv (d.representation.comp e.toMonoidHom))
    (S : Sylow 2 D) (X : Subgroup D) (hSX : (S : Subgroup D) ≤ X)
    (hX : Nonempty ((X ⧸ pCore 2 X) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) PairIndex))
    (w : W) (hw : w ≠ 0) (hfix : ∀ g ∈ X, ρ g w = w) : False := by
  let X' := X.map e.toMonoidHom
  let eX : X ≃* X' := X.equivMapOfInjective e.toMonoidHom e.injective
  let eQ := QuotientGroup.congr (pCore 2 X) (pCore 2 X') eX (pCore_map_iso 2 eX)
  obtain ⟨qX⟩ := hX
  have hX' : Nonempty ((X' ⧸ pCore 2 X') ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) PairIndex) := ⟨eQ.symm.trans qX⟩
  have hw' : f w ≠ 0 := fun he => hw (f.injective (he.trans (map_zero f).symm))
  have hf (g : D) (v : W) : f (ρ g v) = d.representation (e g) (f v) :=
    Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap g v
  have hfix' : ∀ g ∈ X', d.representation g (f w) = f w := by
    rintro g ⟨a,ha,rfl⟩
    exact (hf a w).symm.trans (congrArg f (hfix a ha))
  exact coordinate_exclusion hn d (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    X' (map_mono hSX) hX' (f w) hw' hfix'

end Representation.SmallDisplacementParabolics.NaturalDualExclusion

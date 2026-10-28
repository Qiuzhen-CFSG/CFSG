module

public import Theory.Representation.BinaryNaturalDual.FourActors.Model
public import Theory.Representation.BinaryNaturalDual.FourActors.Swapping
public import Theory.Representation.BinaryNaturalDual.FourActors.A1Module.Coordinates

/-!
# Fixed space and corank-two core of the four-pair actor

The eight explicitly marked inner matrices have a common fixed line in each
summand. The outer diagonal equivalence gives the one-dimensional fixed space
of A₁. Each pure vector in the fixed hyperplanes of r has at least four fixing
inner actors, so its actual stabilizer contributes to the corank-two core.
Conversely, every subgroup occurring in that core meets the inner subgroup
nontrivially, and the marked matrix calculation places its fixed vectors in
C_V(r). This proves the subspace equality, with dimension six.

The only inputs to `parameters` are the independently supplied elementary
abelian and order-sixteen facts for A₁. The actual matrix for r is proved to
be a transvection without extra assumptions. Its uniqueness in A₁ uses the
explicit universal cycle-type marking supplied by the separate marking result.
No fixed-space, containment, or generated-core conclusion is an input.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), H.9.3(5),
printed p.391, PDF p.402.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.FourActors BinaryLinear.OuterCyclic
open scoped IsMulCommutative
namespace BinaryNaturalDual.FourActors.A1Module
variable (d : CoordinateAction 4)

local instance : Finite M := Finite.of_injective permutationEquiv permutationEquiv.injective

theorem actor_fixed_finrank (hE : IsElementaryAbelian 2 A1) :
    Module.finrank (ZMod 2) (actorFixed d A1) = 1 := by
  let : IsElementaryAbelian 2 A1 := hE
  rw [actorFixed_finrank d A1 (fun b hb c hc =>
    congrArg Subtype.val (mul_comm (⟨b,hb⟩ : A1) (⟨c,hc⟩ : A1)))
    transposition transposition_mem_A1
    (by simpa only [transposition_order] using pow_orderOf_eq_one transposition) transposition_outer]
  exact natural_fixed_finrank

theorem fixed_r_iff (x y : X) :
    (x, dualCoordinates y) ∈ BinaryNaturalDual.fixedSpace (action d r) ↔
      x 2 = x 3 ∧ y 0 = y 1 := by
  rw [mem_fixedSpace, action_apply, r_eq, d.on_inner, naturalDualRepresentation_apply,
    Prod.mk.injEq, natural_r_fixed, dual_r_fixed]

theorem inner_fixed_le_r (b : M) (hb : b ∈ B1) (hne : b ≠ 1) :
    BinaryNaturalDual.fixedSpace (action d b) ≤ BinaryNaturalDual.fixedSpace (action d r) := by
  obtain ⟨t, rfl⟩ := inner_cover b hb
  have ht : t ≠ 0 := by intro h; subst t; simp [linear_zero] at hne
  intro v hv
  rw [mem_fixedSpace, action_apply, d.on_inner, naturalDualRepresentation_apply,
    Prod.mk.injEq] at hv
  rw [mem_fixedSpace, action_apply, r_eq, d.on_inner, naturalDualRepresentation_apply,
    Prod.mk.injEq]
  exact ⟨natural_fixed_le_r t ht v.1 hv.1, dual_fixed_le_r t ht v.2 hv.2⟩

private theorem mem_core_of_four_fixers (hcard : Nat.card A1 = 16) (v : V)
    {I : Type} [Finite I] (f : I → A1) (hf : Function.Injective f)
    (hI : 4 ≤ Nat.card I) (hfix : ∀ i, d.representation (f i) v = v) :
    v ∈ actorCore d A1 2 := by
  let K : Subgroup A1 := (MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v).comap
    ((action d).comp A1.subtype)
  let j : I → K := fun i => ⟨f i, hfix i⟩
  have hj : Function.Injective j := fun i k h => hf (congrArg Subtype.val h)
  have hk : 4 ≤ Nat.card K := hI.trans (Nat.card_le_card_of_injective j hj)
  have hc := K.card_mul_index
  rw [hcard] at hc
  have hi : K.index ≤ 4 := by nlinarith
  exact fixedSpace_le_generatedCore (d.representation.comp A1.subtype)
    (show Nat.log 2 K.index ≤ 2 from (Nat.log_mono_right hi).trans (by decide))
    (fun k => k.property)

private theorem natural_mem_core (hcard : Nat.card A1 = 16) (x : X) (hx : x 2 = x 3) :
    (x, (0 : Module.Dual (ZMod 2) X)) ∈ actorCore d A1 2 := by
  let I := {t : Fin 8 // (matrix t).mulVec x = x}
  let f : I → A1 := fun t => ⟨MulAut.conj (linear t.val), (conj_linear_mem t.val).1⟩
  apply mem_core_of_four_fixers d hcard _ f
  · intro i j h
    exact Subtype.ext (conj_linear_injective (congrArg Subtype.val h))
  · change 4 ≤ Nat.card {t : Fin 8 // (matrix t).mulVec x = x}
    rw [Nat.card_eq_fintype_card]
    exact (by decide +kernel : ∀ x : X, x 2 = x 3 →
      4 ≤ Fintype.card {t : Fin 8 // (matrix t).mulVec x = x}) x hx
  · intro i
    change d.representation (MulAut.conj (linear i.val)) (x, 0) = (x, 0)
    rw [d.on_inner, naturalDualRepresentation_apply, map_zero]
    exact Prod.ext i.property rfl

private theorem dual_mem_core (hcard : Nat.card A1 = 16) (y : X) (hy : y 0 = y 1) :
    ((0 : X), dualCoordinates y) ∈ actorCore d A1 2 := by
  let I := {t : Fin 8 // (matrix t).transpose.mulVec y = y}
  let f : I → A1 := fun t => ⟨MulAut.conj (linear t.val), (conj_linear_mem t.val).1⟩
  apply mem_core_of_four_fixers d hcard _ f
  · intro i j h
    exact Subtype.ext (conj_linear_injective (congrArg Subtype.val h))
  · change 4 ≤ Nat.card {t : Fin 8 // (matrix t).transpose.mulVec y = y}
    rw [Nat.card_eq_fintype_card]
    exact (by decide +kernel : ∀ y : X, y 0 = y 1 →
      4 ≤ Fintype.card {t : Fin 8 // (matrix t).transpose.mulVec y = y}) y hy
  · intro i
    change d.representation (MulAut.conj (linear i.val)) (0, dualCoordinates y) = _
    rw [d.on_inner, naturalDualRepresentation_apply, map_zero, dual_apply, i.property]

private theorem core_le (hcard : Nat.card A1 = 16) :
    actorCore d A1 2 ≤ BinaryNaturalDual.fixedSpace (action d r) := by
  apply generatedCore_le
  intro K hK v hv
  have hc := K.card_mul_index
  rw [hcard] at hc
  have hi : K.index < 8 := Nat.lt_pow_of_log_lt (by decide) (by omega : Nat.log 2 K.index < 3)
  have hk : 4 ≤ Nat.card K := by
    by_contra! hh
    interval_cases hh' : Nat.card K <;> omega
  let f : K →* M := A1.subtype.comp K.subtype
  let J := inner.comap f
  have hjindex : J.index ≤ 2 := by
    rw [Subgroup.index_comap]
    have hd := inner.relIndex_dvd_index_of_normal f.range
    rw [inner_index] at hd
    exact Nat.le_of_dvd (by decide) hd
  have hjcard : 1 < Nat.card J := by
    have hj := J.card_mul_index
    have hm := Nat.mul_le_mul_left (Nat.card J) hjindex
    nlinarith
  let : Nontrivial J := Finite.one_lt_card_iff_nontrivial.mp hjcard
  obtain ⟨j, hj⟩ := exists_ne (1 : J)
  have hb : f j.val ∈ B1 := ⟨j.val.val.property, j.property⟩
  have hbne : f j.val ≠ 1 := by
    intro h
    apply hj
    exact Subtype.ext (Subtype.ext (Subtype.ext h))
  exact inner_fixed_le_r d (f j.val) hb hbne (by
    rw [mem_fixedSpace]
    exact hv j.val)

theorem core_eq (hcard : Nat.card A1 = 16) :
    actorCore d A1 2 = BinaryNaturalDual.fixedSpace (action d r) := by
  apply le_antisymm (core_le d hcard)
  rintro ⟨x, f⟩ hv
  obtain ⟨y, rfl⟩ := dualCoordinates.surjective f
  obtain ⟨hx, hy⟩ := (fixed_r_iff d x y).mp hv
  have h := (actorCore d A1 2).add_mem (natural_mem_core d hcard x hx)
    (dual_mem_core d hcard y hy)
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using h

theorem natural_r_finrank : Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace (linear 7)) = 3 := by
  let e : BinaryNaturalDual.fixedSpace (linear 7) ≃ {x : X // x 2 = x 3} :=
    Equiv.subtypeEquivRight fun x => (mem_fixedSpace _ x).trans (natural_r_fixed x)
  have hc : Nat.card (BinaryNaturalDual.fixedSpace (linear 7)) = 8 := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card]
    decide +kernel
  have hn := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := BinaryNaturalDual.fixedSpace (linear 7))
  rw [Nat.card_zmod] at hn
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) (hn.symm.trans hc)

theorem dual_r_finrank :
    Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace (linear 7).symm.dualMap) = 3 := by
  let e : {y : X // y 0 = y 1} ≃ BinaryNaturalDual.fixedSpace (linear 7).symm.dualMap :=
    dualCoordinates.toEquiv.subtypeEquiv fun y =>
      (dual_r_fixed y).symm.trans (mem_fixedSpace _ _).symm
  have hc : Nat.card (BinaryNaturalDual.fixedSpace (linear 7).symm.dualMap) = 8 := by
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
    decide +kernel
  have hn := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := BinaryNaturalDual.fixedSpace (linear 7).symm.dualMap)
  rw [Nat.card_zmod] at hn
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) (hn.symm.trans hc)

theorem fixed_r_finrank : Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace (action d r)) = 6 := by
  let e : {v : X × X // v.1 2 = v.1 3 ∧ v.2 0 = v.2 1} ≃
      BinaryNaturalDual.fixedSpace (action d r) :=
    ((Equiv.refl X).prodCongr dualCoordinates.toEquiv).subtypeEquiv fun v =>
      (fixed_r_iff d v.1 v.2).symm
  have hc : Nat.card (BinaryNaturalDual.fixedSpace (action d r)) = 64 := by
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
    decide +kernel
  have hn := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := BinaryNaturalDual.fixedSpace (action d r))
  rw [Nat.card_zmod] at hn
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) (hn.symm.trans hc)

theorem inner_common_fixed (x y : X) :
    (x, dualCoordinates y) ∈ actorFixed d B1 ↔
      (∃ c : ZMod 2, x = c • (![1,1,0,0] : X)) ∧
        (∃ c : ZMod 2, y = c • (![0,0,1,1] : X)) := by
  have hy : (∀ t : Fin 8, (matrix t).transpose.mulVec y = y) ↔
      ∃ c : ZMod 2, y = c • (![0,0,1,1] : X) :=
    (by decide +kernel : ∀ y : X, (∀ t : Fin 8, (matrix t).transpose.mulVec y = y) ↔
      ∃ c : ZMod 2, y = c • (![0,0,1,1] : X)) y
  rw [← natural_fixed_iff, ← hy, mem_actorFixed, mem_naturalFixed]
  constructor
  · intro hv
    constructor
    · intro g hg
      have h := hv (MulAut.conj g) hg
      rw [d.on_inner, naturalDualRepresentation_apply, Prod.mk.injEq] at h
      exact h.1
    · intro t
      have h := hv (MulAut.conj (linear t)) (conj_linear_mem t)
      rw [d.on_inner, naturalDualRepresentation_apply, Prod.mk.injEq, dual_apply,
        dualCoordinates.injective.eq_iff] at h
      exact h.2
  · rintro ⟨hx, hy⟩ b hb
    obtain ⟨t, rfl⟩ := inner_cover b hb
    rw [d.on_inner, naturalDualRepresentation_apply, Prod.mk.injEq, dual_apply,
      dualCoordinates.injective.eq_iff]
    exact ⟨hx (linear t) (conj_linear_mem t), hy t⟩

/-- The four-pair involution is the actual rank-one transvection with this
natural center and functional, independently of the cycle-type criterion. -/
theorem linear_seven_isTransvection : IsTransvection (linear 7) := by
  let w : X := ![1,1,0,0]
  let f : X →ₗ[ZMod 2] ZMod 2 := LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 4 => ZMod 2) 2 +
    LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 4 => ZMod 2) 3
  have hw : w ≠ 0 := by decide +kernel
  have hf : f ≠ 0 := by
    intro hf
    have h := congrArg (fun l : X →ₗ[ZMod 2] ZMod 2 => l ![0,0,1,0]) hf
    simp [f] at h
  have hfw : f w = 0 := by decide +kernel
  refine ⟨w, f, hw, hf, hfw, ?_⟩
  apply LinearEquiv.ext
  intro x
  change (matrix 7).mulVec x = x + (x 2 + x 3) • (![1,1,0,0] : X)
  exact (by decide +kernel : ∀ x : X,
    (matrix 7).mulVec x = x + (x 2 + x 3) • (![1,1,0,0] : X)) x

/-- The literal diagonal description of the actor's one-dimensional fixed space. -/
theorem actor_fixed_span (hE : IsElementaryAbelian 2 A1) :
    actorFixed d A1 = Submodule.span (ZMod 2)
      {((![1,1,0,0] : X), 0) + d.representation transposition ((![1,1,0,0] : X), 0)} := by
  let : IsElementaryAbelian 2 A1 := hE
  have ha : transposition ^ 2 = 1 := by
    simpa only [transposition_order] using pow_orderOf_eq_one transposition
  let e := outerDiagonalEquiv d transposition ha transposition_outer
  ext v
  rw [actorFixed_eq_outer_diagonal d A1 (fun b hb c hc =>
    congrArg Subtype.val (mul_comm (⟨b,hb⟩ : A1) (⟨c,hc⟩ : A1)))
    transposition transposition_mem_A1 ha transposition_outer,
    show A1 ⊓ inner = B1 from rfl, natural_fixed_line, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨c, ?_⟩
    have hs := congrArg (fun z : BinaryNaturalDual.fixedSpace (action d transposition) => (z : V))
      (e.map_smul c (![1,1,0,0] : X))
    exact hs.symm.trans he
  · rintro ⟨c, hc⟩
    refine ⟨c • (![1,1,0,0] : X), Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self _), ?_⟩
    have hs := congrArg (fun z : BinaryNaturalDual.fixedSpace (action d transposition) => (z : V))
      (e.map_smul c (![1,1,0,0] : X))
    exact hs.trans hc

theorem distinguished_transvection
    (hmark : ∀ g : G, IsTransvection g ↔
      (linearAlternatingEquiv g).val.cycleType = {2,2,2,2}) :
    MulAut.conj (linear 7) = r ∧ IsTransvection (linear 7) ∧
      ∀ g : G, MulAut.conj g ∈ A1 → IsTransvection g → g = linear 7 := by
  refine ⟨r_eq.symm, linear_seven_isTransvection, ?_⟩
  intro g hg hgt
  obtain ⟨t, ht⟩ := inner_cover (MulAut.conj g) ⟨hg, ⟨g, rfl⟩⟩
  have he : g = linear t := MulAut.conj_injective_of_center_eq_bot center_linear_eq_bot ht
  rw [he, hmark, marking] at hgt
  have ht7 : t = 7 := (by decide +kernel : ∀ t : Fin 8,
    (evenPerm t).cycleType = {2,2,2,2} → t = 7) t hgt
  exact he.trans (congrArg linear ht7)

theorem parameters (hE : IsElementaryAbelian 2 A1) (hcard : Nat.card A1 = 16) :
    Module.finrank (ZMod 2) (actorFixed d A1) = 1 ∧
      actorCore d A1 2 = BinaryNaturalDual.fixedSpace (action d r) ∧
        Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace (action d r)) = 6 :=
  ⟨actor_fixed_finrank d hE, core_eq d hcard, fixed_r_finrank d⟩

end BinaryNaturalDual.FourActors.A1Module

module
public import CFSG.Quasithin.ChapterG.Section10.InvariantGeometry
public import Theory.Representation.BinaryFullAxisRecognition
public import Theory.LinearAlgebra.BinaryInvariantAlternating
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# Common-axis geometry for normal-subgroup reductions

An X-invariant subspace avoiding the marked point and moved by X has the
full common-axis action and complements W. Each actor consequently has
whole-module displacement rank at most two. If a subgroup containing X
acts irreducibly in dimension at least three, the subspace is Lagrangian;
every X-invariant complement then contains the marked point.

These are the literal HX-subspace steps of Aschbacher--Smith G.10.4(2),
printed pp.358--359. No ambient G-invariance of the subspace is required.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- Full common-axis action on an X-invariant space avoiding the point and moved by X. -/
theorem full_axis_on_moved_space (U : Submodule (ZMod 2) V)
    (hs : X ≤ subspaceStabilizer ρ U) (hv : v ∉ U)
    (hm : ¬ U ≤ fixedSpace ρ X) :
    let f := (B v).comp U.subtype
    IsCompl U W ∧
      finrank (ZMod 2) U = Group.rank (X ⧸ X₀) + 1 ∧
      ∀ a : f.ker, ∃ x : X, ∀ u : U,
        ρ x u = (u : V) + f u • (a : U) := by
  let S : Subrepresentation (ρ.comp X.subtype) :=
    ⟨U, fun x u hu => (hs x.property u).2 hu⟩
  let σ : Representation (ZMod 2) X U := S.toRepresentation
  let f := (B v).comp U.subtype
  let : Finite f.ker := Module.finite_of_finite (ZMod 2)
  have hf : f ≠ 0 := by
    intro hz
    apply hm
    intro u hu x
    exact h.fixes_axis U (fun x u hu => (hs x.property u).2 hu) hv x u hu
      (LinearMap.congr_fun hz ⟨u,hu⟩)
  obtain ⟨b, hb⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hf) 1
  have hfix (x : X) (u : U) (hu : f u = 0) : σ x u = u := by
    apply Subtype.ext
    exact h.fixes_axis U (fun x u hu => (hs x.property u).2 hu) hv x u u.property hu
  have hform (x : X) (u : U) : f (σ x u) = f u := by
    have he := h.preserves (x : G) v u
    rw [show ρ (x : G) v = v from h.fixes_point x.property] at he
    exact he
  let d : X →* Multiplicative f.ker := {
    toFun x := Multiplicative.ofAdd ⟨σ x b - b, by
      change f (σ x b - b) = 0
      rw [map_sub, hform, sub_self]⟩
    map_one' := by
      apply congrArg Multiplicative.ofAdd
      apply Subtype.ext
      simp
    map_mul' x y := by
      apply congrArg Multiplicative.ofAdd
      apply Subtype.ext
      change σ (x * y) b - b =
        (σ x b - b) + (σ y b - b)
      have he := hfix x (σ y b - b) (by rw [map_sub, hform, sub_self])
      rw [map_sub] at he
      rw [map_mul, Module.End.mul_apply]
      rw [show σ x (σ y b) =
        (σ y b - b) + σ x b from sub_eq_iff_eq_add.mp he]
      abel }
  have hk : d.ker ≤ X₀ := by
    intro x hx
    by_contra hx0
    have he : σ x b = b := by
      apply sub_eq_zero.mp
      exact congrArg (fun a : Multiplicative f.ker => (a.toAdd : U)) hx
    have hz := h.fixed_bound x hx0 b (congrArg Subtype.val he)
    have hh : f b = 0 := hz
    rw [hb] at hh
    exact one_ne_zero hh
  have hcard : Nat.card (X ⧸ X₀) ≤ 2 ^ finrank (ZMod 2) f.ker := by
    calc
      Nat.card (X ⧸ X₀) = X₀.index := rfl
      _ ≤ d.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero d.ker.index_ne_zero_of_finite) (index_dvd_of_le hk)
      _ = Nat.card d.range := index_ker d
      _ ≤ Nat.card (Multiplicative f.ker) := d.range.card_le_card_group
      _ = 2 ^ finrank (ZMod 2) f.ker := by
        rw [Nat.card_congr Multiplicative.toAdd]
        simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := f.ker)
  have hr := IsElementaryAbelian.rank_le_of_card_le (X ⧸ X₀) hcard
  have hker : finrank (ZMod 2) f.ker + 1 = finrank (ZMod 2) U := by
    have he := f.finrank_range_add_finrank_ker
    rw [Module.Dual.range_eq_top_of_ne_zero hf, finrank_top, Module.finrank_self] at he
    omega
  have hdis := h.disjoint_W_of_point_not_mem U (fun x u hu => (hs x.property u).2 hu) hv
  have hsum : finrank (ZMod 2) U + finrank (ZMod 2) W ≤ finrank (ZMod 2) V := by
    have he := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hdis.eq_bot, finrank_bot, add_zero] at he
    rw [← he]
    exact Submodule.finrank_le _
  have hp : 0 < finrank (ZMod 2) V := by
    let : Nontrivial V := ⟨⟨v, 0, h.point_ne_zero⟩⟩
    exact Module.finrank_pos
  have heqdim : finrank (ZMod 2) U = Group.rank (X ⧸ X₀) + 1 := by
    have hs := h.dimension
    omega
  have hcompl : IsCompl U W := by
    refine ⟨hdis, codisjoint_iff.mpr ?_⟩
    apply Submodule.eq_top_of_finrank_eq
    have he := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hdis.eq_bot, finrank_bot, add_zero] at he
    have hs := h.dimension
    omega
  have hsur : Function.Surjective d := by
    have hpow : 2 ^ Group.rank (X ⧸ X₀) ≤ Nat.card (X ⧸ X₀) := by
      have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (X ⧸ X₀))
      have hr := IsElementaryAbelian.rank_le_finrank (p := 2) (X ⧸ X₀)
      rw [← Nat.card_congr Additive.ofMul, Nat.card_zmod] at hc
      rw [hc]
      exact Nat.pow_le_pow_right (by decide) hr
    have hsize : Nat.card (Multiplicative f.ker) ≤ Nat.card d.range := by
      calc
        _ = 2 ^ finrank (ZMod 2) f.ker := by
          rw [Nat.card_congr Multiplicative.toAdd]
          simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := f.ker)
        _ = 2 ^ Group.rank (X ⧸ X₀) := by congr 1; omega
        _ ≤ Nat.card (X ⧸ X₀) := hpow
        _ ≤ d.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero d.ker.index_ne_zero_of_finite) (index_dvd_of_le hk)
        _ = Nat.card d.range := index_ker d
    have ht : d.range = ⊤ := Subgroup.eq_top_of_card_eq d.range (le_antisymm d.range.card_le_card_group hsize)
    exact MonoidHom.range_eq_top.mp ht
  have haxis : ∀ a : f.ker, ∃ x : X, ∀ u : U, σ x u = u + f u • (a : U) := by
    intro a
    obtain ⟨x, hx⟩ := hsur (Multiplicative.ofAdd a)
    refine ⟨x, fun u => ?_⟩
    have he := hfix x (u - f u • b) (by simp [map_sub, map_smul, hb])
    have hd : σ x b - b = (a : U) :=
      congrArg (fun a : Multiplicative f.ker => (a.toAdd : U)) hx
    rw [map_sub, map_smul] at he
    rw [sub_eq_iff_eq_add] at he
    rw [show σ x b = (a : U) + b from sub_eq_iff_eq_add.mp hd, smul_add] at he
    rw [he]
    abel
  refine ⟨hcompl, heqdim, ?_⟩
  intro a
  obtain ⟨x,hx⟩ := haxis a
  exact ⟨x, fun u => congrArg Subtype.val (hx u)⟩

/-- The axis count bounds each actor's displacement on the whole module by two. -/
theorem displacement_rank_le_two_of_moved_space (U : Submodule (ZMod 2) V)
    (hs : X ≤ subspaceStabilizer ρ U) (hv : v ∉ U)
    (hm : ¬ U ≤ fixedSpace ρ X) (x : X) :
    finrank (ZMod 2) (LinearMap.range (ρ x - LinearMap.id)) ≤ 2 := by
  let f := (B v).comp U.subtype
  have hf : f ≠ 0 := by
    intro hz
    apply hm
    intro u hu y
    exact h.fixes_axis U (fun y u hu => (hs y.property u).2 hu) hv y u hu
      (LinearMap.congr_fun hz ⟨u,hu⟩)
  obtain ⟨b,hb⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hf) 1
  let d := ρ x - LinearMap.id
  have hd (u : U) : d u = f u • d b := by
    have he := h.fixes_axis U (fun y u hu => (hs y.property u).2 hu) hv x
      (u - f u • b) (U.sub_mem u.property (U.smul_mem _ b.property))
      (by change f (u - f u • b) = 0; simp [map_sub, map_smul, hb])
    change ρ x (u - f u • b) = u - f u • b at he
    simp only [map_sub,map_smul] at he
    change ρ x u - (u : V) = f u • (ρ x b - (b : V))
    rw [smul_sub]
    exact sub_eq_sub_iff_add_eq_add.mpr
      ((sub_eq_sub_iff_add_eq_add.mp he).trans (add_comm _ _))
  have hr : LinearMap.range d ≤ Submodule.span (ZMod 2) {d b} ⊔ Submodule.span (ZMod 2) {v} := by
    rintro z ⟨w,rfl⟩
    have hsplit : w ∈ U ⊔ W := by rw [(h.full_axis_on_moved_space U hs hv hm).1.sup_eq_top]; trivial
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hsplit
    rw [map_add,hd ⟨u,hu⟩]
    apply Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
    obtain ⟨k,_,hk⟩ := h.transvections x
    have he : d w = k ⟨w,hw⟩ • v := by
      change ρ x w - w = _
      rw [hk ⟨w,hw⟩, add_sub_cancel_left]
    rw [he]
    exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span (ZMod 2) {d b}) (Submodule.span (ZMod 2) {v})
  have ha : finrank (ZMod 2) (Submodule.span (ZMod 2) {d b}) ≤ 1 := by
    simpa using finrank_span_le_card ({d b} : Set V)
  have hv' : finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) ≤ 1 := by
    simpa using finrank_span_le_card ({v} : Set V)
  exact (Submodule.finrank_mono hr).trans (by omega)

/-- Recognition uses only irreducibility under the actual subgroup containing X. -/
theorem full_linear_on_moved_space (K : Subgroup G) (hXK : X ≤ K)
    (U : Subrepresentation (ρ.comp K.subtype)) [IsIrreducible U.toRepresentation]
    (hv : v ∉ U.toSubmodule) (hm : ¬ U.toSubmodule ≤ fixedSpace ρ X) :
    ∀ e : U.toSubmodule ≃ₗ[ZMod 2] U.toSubmodule,
      ∃ g : K, ∀ u : U.toSubmodule, U.toRepresentation g u = e u := by
  have hs : X ≤ subspaceStabilizer ρ U.toSubmodule :=
    le_subspaceStabilizer ρ U.toSubmodule (fun x hx u hu => U.apply_mem_toSubmodule ⟨x,hXK hx⟩ hu)
  have hf : (B v).comp U.toSubmodule.subtype ≠ 0 := by
    intro hz
    apply hm
    intro u hu x
    exact h.fixes_axis U.toSubmodule (fun x u hu => (hs x.property u).2 hu) hv x u hu
      (LinearMap.congr_fun hz ⟨u,hu⟩)
  apply full_linear_action_of_irreducible_axis U.toRepresentation _ hf
  intro a
  obtain ⟨x,hx⟩ := (h.full_axis_on_moved_space U.toSubmodule hs hv hm).2.2 a
  refine ⟨⟨x,hXK x.property⟩, fun u => ?_⟩
  exact Subtype.ext (hx u)

/-- The literal HX-submodule is Lagrangian in the large-degree contrary case. -/
theorem lagrangian_of_large_moved_space (K : Subgroup G) (hXK : X ≤ K)
    (U : Subrepresentation (ρ.comp K.subtype)) [IsIrreducible U.toRepresentation]
    (hv : v ∉ U.toSubmodule) (hm : ¬ U.toSubmodule ≤ fixedSpace ρ X)
    (hdim : 3 ≤ finrank (ZMod 2) U.toSubmodule) :
    B.orthogonal U.toSubmodule = U.toSubmodule ∧
      finrank (ZMod 2) V = 2 * finrank (ZMod 2) U.toSubmodule := by
  have hz : B.restrict U.toSubmodule = 0 :=
    (B.restrict U.toSubmodule).eq_zero_of_full_binary_linear_invariance
      (fun u => h.alternating u) (by
        intro e u w
        obtain ⟨g,hg⟩ := h.full_linear_on_moved_space K hXK U hv hm e
        rw [← hg u, ← hg w]
        exact h.preserves g u w) hdim
  have hiso : ∀ u ∈ U.toSubmodule, ∀ w ∈ U.toSubmodule, B u w = 0 := by
    intro u hu w hw
    exact congrArg (fun b : LinearMap.BilinForm (ZMod 2) U.toSubmodule => b ⟨u,hu⟩ ⟨w,hw⟩) hz
  have hle : U.toSubmodule ≤ B.orthogonal U.toSubmodule := fun u hu w hw => hiso w hw u hu
  have hsize := B.twice_finrank_le_of_isotropic h.nondegenerate U.toSubmodule hiso
  have hs : X ≤ subspaceStabilizer ρ U.toSubmodule :=
    le_subspaceStabilizer ρ U.toSubmodule (fun x hx u hu => U.apply_mem_toSubmodule ⟨x,hXK hx⟩ hu)
  have heq := (h.full_axis_on_moved_space U.toSubmodule hs hv hm).2.1
  have hb := h.dimension_bound.1
  have hd : finrank (ZMod 2) V = 2 * finrank (ZMod 2) U.toSubmodule := by omega
  refine ⟨(Submodule.eq_of_le_of_finrank_eq hle ?_).symm,hd⟩
  rw [B.finrank_orthogonal h.nondegenerate]
  omega

/-- Every X-stable complement of a large moved Lagrangian contains the point. -/
theorem point_mem_complement_of_large_moved_lagrangian
    (U C : Submodule (ZMod 2) V)
    (hs : X ≤ subspaceStabilizer ρ U) (hv : v ∉ U)
    (hm : ¬ U ≤ fixedSpace ρ X) (hdim : 3 ≤ finrank (ZMod 2) U)
    (horth : B.orthogonal U = U) (hcomp : IsCompl U C)
    (hC : X ≤ subspaceStabilizer ρ C) : v ∈ C := by
  by_contra hvC
  let f := (B v).comp U.subtype
  let k := (B v).comp C.subtype
  have hf : f ≠ 0 := by
    intro hz
    apply hm
    intro u hu x
    exact h.fixes_axis U (fun x u hu => (hs x.property u).2 hu) hv x u hu
      (LinearMap.congr_fun hz ⟨u,hu⟩)
  obtain ⟨b,hb⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hf) 1
  let q : C →ₗ[ZMod 2] Module.Dual (ZMod 2) U :=
    U.subtype.dualMap.comp (LinearMap.comp B C.subtype)
  have hq : Function.Injective q := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro c hc
    have hcU : (c : V) ∈ U := by
      rw [←horth]
      intro u hu
      have hz := congrArg (fun l : Module.Dual (ZMod 2) U => l ⟨u,hu⟩) hc
      exact h.alternating.eq_iff.mp hz
    have hz : (c : V) ∈ U ⊓ C := ⟨hcU,c.property⟩
    rw [hcomp.inf_eq_bot] at hz
    exact Subtype.ext hz
  have hqA (c : k.ker) : q c ∈ f.ker.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro a ha
    obtain ⟨x,hx⟩ := (h.full_axis_on_moved_space U hs hv hm).2.2 ⟨a,ha⟩
    have hxc : ρ x (c : C) = (c : C) :=
      h.fixes_axis C (fun x u hu => (hC x.property u).2 hu) hvC x c c.val.property c.property
    have hxb : ρ x (b : V) = b+a := by
      have he := hx b
      change ρ x (b : V) = b + f b • (a : V) at he
      simpa only [hb,one_smul] using he
    have he := h.preserves (x : G) b c
    rw [hxb,hxc,map_add,LinearMap.add_apply] at he
    exact h.alternating.eq_iff.mpr (add_eq_left.mp he)
  let qA : k.ker →ₗ[ZMod 2] f.ker.dualAnnihilator :=
    (q.comp k.ker.subtype).codRestrict _ hqA
  have hqAi : Function.Injective qA := by
    intro c d he
    apply Subtype.ext
    apply hq
    exact congrArg Subtype.val he
  have hineq := LinearMap.finrank_le_finrank_of_injective hqAi
  have hfk := f.finrank_range_add_finrank_ker
  have hkk := k.finrank_range_add_finrank_ker
  rw [Module.Dual.range_eq_top_of_ne_zero hf,finrank_top,Module.finrank_self] at hfk
  have hkdim : finrank (ZMod 2) k.range ≤ 1 := by simpa using Submodule.finrank_le k.range
  have hA := Subspace.finrank_add_finrank_dualAnnihilator_eq f.ker
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U C
  rw [hcomp.sup_eq_top,hcomp.inf_eq_bot,finrank_top,finrank_bot,add_zero] at hsum
  have horthdim := B.finrank_orthogonal h.nondegenerate U
  rw [horth] at horthdim
  have hUdim := Submodule.finrank_le U
  omega

end CFSG.Quasithin.ChapterG.Section10.Hypothesis

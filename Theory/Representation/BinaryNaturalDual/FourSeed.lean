module
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Four.UpperSylow
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Four.FixedSpaces
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.AutomorphismModel
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality


/-!
# Binary planes in the full natural-plus-dual four-space action

A two-group has cyclic image on a binary plane. Commutation of the standard
upper transvections and graph involution therefore confines every invariant
plane to the first natural and last dual coordinate lines. A plane stabilizer
preserves nonvanishing of both components, so it fixes the Sylow-fixed point.
Sylow conjugacy and literal equivariant coordinates transport the obstruction.

The original rank-three flag in Chapter 14 has a natural residual moving this
point inside its seed plane. Its SourceAction/FullLinearExclusion consumer
therefore excludes the exceptional S₈ action without a centerlessness premise.
Source: Aschbacher--Smith 12.8.5, 14.3.23--24, printed pp.850,999--1000;
the G.10.15 full-four correction is recorded in docs/quasithin-proof-basis.md.
-/

public section
open Subgroup Module
open scoped IsMulCommutative
open BinaryLinear.OuterCyclic BinaryNaturalDual
open BinaryNaturalDual.AdaptedPair BinaryNaturalDual.AdaptedPair.Four
namespace BinaryNaturalDual.FourSeed

private theorem two_group_action_commutes {P W : Type*} [Group P] [Finite P]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (hp : IsPGroup 2 P) (hd : finrank (ZMod 2) W = 2)
    (r : P →* (W ≃ₗ[ZMod 2] W)) (a b : P) : r a * r b = r b * r a := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Finite (W ≃ₗ[ZMod 2] W) := Finite.of_injective
    (fun f : W ≃ₗ[ZMod 2] W => (f : W → W)) DFunLike.coe_injective
  have hc : Nat.card (W ≃ₗ[ZMod 2] W) = 6 := by
    rw [BinaryLinear.card_GL_of_finrank hd]
    norm_num [BinaryLinear.order, Fin.prod_univ_succ]
  have hv : Nat.card r.range ∣ 6 := hc ▸ r.range.card_subgroup_dvd_card
  obtain ⟨k,hk⟩ := (hp.of_surjective r.rangeRestrict r.rangeRestrict_surjective).exists_card_eq
  have hcop : Nat.Coprime (Nat.card r.range) 3 := by
    rw [hk]
    exact (by decide : Nat.Coprime 2 3).pow_left k
  let : IsCyclic r.range := isCyclic_of_card_dvd_prime (p := 2) (hcop.dvd_mul_left.mp hv)
  exact congrArg Subtype.val (mul_comm (r.rangeRestrict a) (r.rangeRestrict b))

private def restriction {A Z : Type*} [Group A] [AddCommGroup Z] [Module (ZMod 2) Z]
    (r : A →* (Z ≃ₗ[ZMod 2] Z)) (W : Submodule (ZMod 2) Z)
    (hs : ∀ a w, w ∈ W → r a w ∈ W) : A →* (W ≃ₗ[ZMod 2] W) where
  toFun a := {
    toFun w := ⟨r a w,hs a w w.property⟩
    invFun w := ⟨r a⁻¹ w,hs a⁻¹ w w.property⟩
    left_inv w := by apply Subtype.ext; change (r a⁻¹ * r a) w = w; rw [← map_mul,inv_mul_cancel,map_one]; rfl
    right_inv w := by apply Subtype.ext; change (r a * r a⁻¹) w = w; rw [← map_mul,mul_inv_cancel,map_one]; rfl
    map_add' x y := Subtype.ext ((r a).map_add x y)
    map_smul' c x := Subtype.ext ((r a).map_smul c x) }
  map_one' := by ext w; exact congrArg (fun f : Z ≃ₗ[ZMod 2] Z => f w) r.map_one
  map_mul' a b := by ext w; exact congrArg (fun f : Z ≃ₗ[ZMod 2] Z => f w) (r.map_mul a b)

private theorem commute_on_plane (d : CoordinateAction 4)
    (W : Submodule (ZMod 2) (CoordinateSpace 4)) (hd : finrank (ZMod 2) W = 2)
    (hs : ∀ a ∈ standardGroup 4, ∀ w ∈ W, linearAction d a w ∈ W)
    (a b : MulAut (LinearGroup 4)) (ha : a ∈ standardGroup 4) (hb : b ∈ standardGroup 4)
    (w : CoordinateSpace 4) (hw : w ∈ W) :
    linearAction d a (linearAction d b w) = linearAction d b (linearAction d a w) := by
  let : Finite (standardGroup 4) := Nat.finite_of_card_ne_zero (by
    rw [UpperSylow.standardGroup_card d]; decide)
  let r := restriction ((linearAction d).comp (standardGroup 4).subtype) W
    (fun a w hw => hs a a.property w hw)
  have he := two_group_action_commutes (UpperSylow.standardGroup_isPGroup d) hd r ⟨a,ha⟩ ⟨b,hb⟩
  exact congrArg (fun f : W ≃ₗ[ZMod 2] W => (f ⟨w,hw⟩ : CoordinateSpace 4)) he

private theorem elementary_fst (d : CoordinateAction 4) (i j : Fin 4) (hij : i < j)
    (w : CoordinateSpace 4) (k : Fin 4) :
    (linearAction d (MulAut.conj (elementary i j hij)) w).1 k =
      w.1 k + w.1 j * (if k = i then 1 else 0) := by
  rw [linearAction_inner, BinaryLinear.NaturalDualFlag.action_fst,elementary_apply]
  simp [axis,Pi.single_apply]

private theorem elementary_snd (d : CoordinateAction 4) (i j : Fin 4) (hij : i < j)
    (w : CoordinateSpace 4) (k : Fin 4) :
    (linearAction d (MulAut.conj (elementary i j hij)) w).2 (axis k) =
      w.2 (axis k) + (if k = j then 1 else 0) * w.2 (axis i) := by
  rw [linearAction_inner, BinaryLinear.NaturalDualFlag.action_snd,elementary_symm_apply]
  rw [map_add,map_smul]
  change w.2 (axis k) + axis k j * w.2 (axis i) = _
  by_cases he : k = j
  · subst k; simp [axis]
  · simp [axis,he,Ne.symm he]

/-- Every Sylow-invariant plane lies in the first-natural/last-dual two-space. -/
theorem plane_coordinates (d : CoordinateAction 4)
    (W : Submodule (ZMod 2) (CoordinateSpace 4)) (hd : finrank (ZMod 2) W = 2)
    (hs : ∀ a ∈ standardGroup 4, ∀ w ∈ W, linearAction d a w ∈ W)
    (w : CoordinateSpace 4) (hw : w ∈ W) :
    w.1 1 = 0 ∧ w.1 2 = 0 ∧ w.1 3 = 0 ∧
      w.2 (axis 0) = 0 ∧ w.2 (axis 1) = 0 ∧ w.2 (axis 2) = 0 := by
  have hc (i j : Fin 4) (hij : i < j) := commute_on_plane d W hd hs
    (MulAut.conj (elementary i j hij)) (tau 4)
    (inner_mem_standard (elementary_mem_upperGroup _ _ _)) (tau_mem_standard 4) w hw
  have h1 := congrArg (fun v : CoordinateSpace 4 => v.1 2) (hc 0 1 (by decide))
  have h2 := congrArg (fun v : CoordinateSpace 4 => v.1 0) (hc 0 1 (by decide))
  have h3 := congrArg (fun v : CoordinateSpace 4 => v.2 (axis 1)) (hc 0 1 (by decide))
  have h4 := congrArg (fun v : CoordinateSpace 4 => v.2 (axis 3)) (hc 0 1 (by decide))
  simp only [elementary_fst,elementary_snd,linearAction_tau_fst,linearAction_tau_snd_axis] at h1 h2 h3 h4
  norm_num [Fin.rev,Fin.last,Fin.ext_iff] at h1 h2 h3 h4
  have he := commute_on_plane d W hd hs
    (MulAut.conj (elementary 0 1 (by decide))) (MulAut.conj (elementary 1 2 (by decide)))
    (inner_mem_standard (elementary_mem_upperGroup _ _ _))
    (inner_mem_standard (elementary_mem_upperGroup _ _ _)) w hw
  have h5 := congrArg (fun v : CoordinateSpace 4 => v.1 0) he
  have he' := commute_on_plane d W hd hs
    (MulAut.conj (elementary 1 2 (by decide))) (MulAut.conj (elementary 2 3 (by decide)))
    (inner_mem_standard (elementary_mem_upperGroup _ _ _))
    (inner_mem_standard (elementary_mem_upperGroup _ _ _)) w hw
  have h6 := congrArg (fun v : CoordinateSpace 4 => v.2 (axis 3)) he'
  simp only [elementary_fst,elementary_snd] at h5 h6
  norm_num [Fin.ext_iff] at h5 h6
  exact ⟨h4,h5,h3,h1,h6,h2⟩

private theorem components_ne_zero (d : CoordinateAction 4)
    (a : MulAut (LinearGroup 4)) (w : CoordinateSpace 4)
    (hx : w.1 ≠ 0) (hf : w.2 ≠ 0) :
    (linearAction d a w).1 ≠ 0 ∧ (linearAction d a w).2 ≠ 0 := by
  obtain ⟨g,rfl | rfl⟩ := inner_graph (Or.inl rfl) a
  · rw [linearAction_inner]
    have hf' : (BinaryLinear.NaturalDualFlag.action g w).2 = g.symm.dualMap w.2 := by
      apply LinearMap.ext
      intro x
      exact BinaryLinear.NaturalDualFlag.action_snd g w x
    rw [BinaryLinear.NaturalDualFlag.action_fst,hf']
    exact ⟨fun he => hx (g.map_eq_zero_iff.mp he),
      fun he => hf (g.symm.dualMap.map_eq_zero_iff.mp he)⟩
  · rw [map_mul,LinearEquiv.mul_apply,linearAction_inner]
    change (d.representation (graphLinear 4) (naturalDualRepresentation g w)).1 ≠ 0 ∧
      (d.representation (graphLinear 4) (naturalDualRepresentation g w)).2 ≠ 0
    rw [d.on_graph,coordinateSwap_apply,naturalDualRepresentation_apply]
    exact ⟨fun he => hf (g.symm.dualMap.map_eq_zero_iff.mp
      ((dotProductEquiv (ZMod 2) (Fin 4)).symm.map_eq_zero_iff.mp he)),
      fun he => hx (g.map_eq_zero_iff.mp
      ((dotProductEquiv (ZMod 2) (Fin 4)).map_eq_zero_iff.mp he))⟩

/-- Every stabilizer of a Sylow-invariant binary plane fixes its Sylow-fixed point. -/
theorem standard_plane_fixes_point (d : CoordinateAction 4)
    (W : Submodule (ZMod 2) (CoordinateSpace 4)) (hd : finrank (ZMod 2) W = 2)
    (hs : ∀ a ∈ standardGroup 4, ∀ w ∈ W, linearAction d a w ∈ W)
    (v : CoordinateSpace 4) (hv : v ∈ W)
    (hfix : ∀ a ∈ standardGroup 4, linearAction d a v = v)
    (a : MulAut (LinearGroup 4)) (ha : ∀ w ∈ W, linearAction d a w ∈ W) :
    linearAction d a v = v := by
  by_cases hz : v = 0
  · simp [hz]
  have hvline : v ∈ Submodule.span (ZMod 2) {fixedVector 4} :=
    fixedVectors_standard d ▸ hfix
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hvline
  have hc1 : c = 1 := by
    have : c = 0 ∨ c = 1 := by exact (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
    rcases this with he | he
    · exact (hz (by simpa [he] using hc.symm)).elim
    · exact he
  rw [hc1,one_smul] at hc
  subst v
  have hx : (fixedVector 4).1 ≠ 0 := by
    intro he
    have hh := congrFun he 0
    change (1 : ZMod 2) = 0 at hh
    exact one_ne_zero hh
  have hf : (fixedVector 4).2 ≠ 0 := by
    intro he
    have hh := congrArg (fun f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space 4) => f (axis 3)) he
    change (1 : ZMod 2) = 0 at hh
    exact one_ne_zero hh
  obtain ⟨hx,hf⟩ := components_ne_zero d a (fixedVector 4) hx hf
  obtain ⟨hx1,hx2,hx3,hf0,hf1,hf2⟩ := plane_coordinates d W hd hs _ (ha _ hv)
  let w := linearAction d a (fixedVector 4)
  have hx0 : w.1 0 = 1 := by
    have hz : w.1 0 ≠ 0 := by
      intro he
      apply hx
      ext i
      fin_cases i
      · exact he
      · exact hx1
      · exact hx2
      · exact hx3
    have hb := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (w.1 0)
    exact hb.resolve_left hz
  have hf3 : w.2 (axis 3) = 1 := by
    have hz : w.2 (axis 3) ≠ 0 := by
      intro he
      apply hf
      apply dual_ext
      intro i
      fin_cases i
      · exact hf0
      · exact hf1
      · exact hf2
      · exact he
    have hb := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (w.2 (axis 3))
    exact hb.resolve_left hz
  change w = fixedVector 4
  apply Prod.ext
  · ext i
    fin_cases i
    · change w.1 0 = 1; exact hx0
    · change w.1 1 = 0; exact hx1
    · change w.1 2 = 0; exact hx2
    · change w.1 3 = 0; exact hx3
  · apply dual_ext
    intro i
    fin_cases i
    · change w.2 (axis 0) = 0; exact hf0
    · change w.2 (axis 1) = 0; exact hf1
    · change w.2 (axis 2) = 0; exact hf2
    · change w.2 (axis 3) = 1; exact hf3


open scoped Pointwise in
/-- The plane obstruction is independent of the chosen Sylow coordinates. -/
theorem plane_fixes_point (d : CoordinateAction 4)
    (P : Sylow 2 (MulAut (LinearGroup 4)))
    (W : Submodule (ZMod 2) (CoordinateSpace 4)) (hd : finrank (ZMod 2) W = 2)
    (hs : ∀ a ∈ P, ∀ w ∈ W, linearAction d a w ∈ W)
    (v : CoordinateSpace 4) (hv : v ∈ W)
    (hfix : ∀ a ∈ P, linearAction d a v = v)
    (a : MulAut (LinearGroup 4)) (ha : ∀ w ∈ W, linearAction d a w ∈ W) :
    linearAction d a v = v := by
  have hindex : (innerGroup 4).index = 2 :=
    ModelOrbits.AutomorphismModel.inner_index (Or.inl rfl)
  let : Finite (MulAut (LinearGroup 4)) := Nat.finite_of_card_ne_zero (by
    rw [UpperSylow.automorphismGroup_card d
      hindex]; decide)
  let S := UpperSylow.standardSylow d hindex
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq (MulAut (LinearGroup 4)) P S
  let e := linearAction d b
  let W' := W.map e.toLinearMap
  have hconj (x : MulAut (LinearGroup 4)) (hx : x ∈ standardGroup 4) :
      b⁻¹ * x * b ∈ P := by
    have hx' : x ∈ (b • P : Sylow 2 (MulAut (LinearGroup 4))) := by
      rw [hb]
      change x ∈ (UpperSylow.standardSylow d hindex : Subgroup _)
      exact (UpperSylow.standardSylow_coe d hindex).symm ▸ hx
    change x ∈ MulAut.conj b • (P : Subgroup _) at hx'
    have hh := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hx'
    change b⁻¹*x*(b⁻¹)⁻¹ ∈ (P : Subgroup _) at hh
    rw [inv_inv] at hh
    exact hh
  have heq (x : MulAut (LinearGroup 4)) (w : CoordinateSpace 4) :
      linearAction d x (e w) = e (linearAction d (b⁻¹*x*b) w) := by
    change (linearAction d x * linearAction d b) w =
      (linearAction d b * linearAction d (b⁻¹*x*b)) w
    rw [← map_mul,← map_mul]
    congr 2
    group
  have hs' : ∀ x ∈ standardGroup 4, ∀ w ∈ W', linearAction d x w ∈ W' := by
    intro x hx w hw
    obtain ⟨u,hu,rfl⟩ := hw
    change linearAction d x (e u) ∈ W'
    exact (heq x u).symm ▸ (show e (linearAction d (b⁻¹*x*b) u) ∈ W' from
      ⟨_,hs _ (hconj x hx) u hu,rfl⟩)
  have hv' : e v ∈ W' := ⟨v,hv,rfl⟩
  have hf' : ∀ x ∈ standardGroup 4, linearAction d x (e v) = e v := by
    intro x hx
    rw [heq,hfix _ (hconj x hx)]
  let a' := b*a*b⁻¹
  have haa : b⁻¹*a'*b = a := by dsimp [a']; group
  have ha' : ∀ w ∈ W', linearAction d a' w ∈ W' := by
    intro w hw
    obtain ⟨u,hu,rfl⟩ := hw
    change linearAction d a' (e u) ∈ W'
    exact (heq a' u).symm ▸ (show e (linearAction d (b⁻¹*a'*b) u) ∈ W' from
      ⟨_,haa.symm ▸ ha u hu,rfl⟩)
  have hh := standard_plane_fixes_point d W' ((e.finrank_map_eq W).trans hd)
    hs' (e v) hv' hf' a' ha'
  rw [heq,haa] at hh
  exact e.injective hh

/-- Transport the obstruction through actual group and module coordinates. -/
theorem point_fixed_of_coordinates {D U : Type*} [Group D] [Finite D]
    [AddCommGroup U] [Module (ZMod 2) U]
    (r : Representation (ZMod 2) D U) (d : CoordinateAction 4)
    (e : D ≃* MulAut (LinearGroup 4)) (c : U ≃ₗ[ZMod 2] CoordinateSpace 4)
    (he : ∀ a u, c (r a u) = linearAction d (e a) (c u))
    (P : Sylow 2 D) (W : Submodule (ZMod 2) U) (hd : finrank (ZMod 2) W = 2)
    (hs : ∀ a ∈ P, ∀ w ∈ W, r a w ∈ W)
    (v : U) (hv : v ∈ W) (hfix : ∀ a ∈ P, r a v = v)
    (a : D) (ha : ∀ w ∈ W, r a w ∈ W) : r a v = v := by
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let W' := W.map c.toLinearMap
  have hs' : ∀ x ∈ P', ∀ w ∈ W', linearAction d x w ∈ W' := by
    intro x hx w hw
    obtain ⟨y,hy,rfl⟩ := (show x ∈ (P : Subgroup D).map e.toMonoidHom from hx)
    obtain ⟨u,hu,rfl⟩ := hw
    exact ⟨_,hs y hy u hu,he y u⟩
  have hf' : ∀ x ∈ P', linearAction d x (c v) = c v := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := (show x ∈ (P : Subgroup D).map e.toMonoidHom from hx)
    exact (he y v).symm.trans (congrArg c (hfix y hy))
  have ha' : ∀ w ∈ W', linearAction d (e a) w ∈ W' := by
    intro w hw
    obtain ⟨u,hu,rfl⟩ := hw
    exact ⟨_,ha u hu,he a u⟩
  have h := plane_fixes_point d P' W' ((c.finrank_map_eq W).trans hd)
    hs' (c v) ⟨v,hv,rfl⟩ hf' (e a) ha'
  apply c.injective
  rw [he]
  exact h

end BinaryNaturalDual.FourSeed

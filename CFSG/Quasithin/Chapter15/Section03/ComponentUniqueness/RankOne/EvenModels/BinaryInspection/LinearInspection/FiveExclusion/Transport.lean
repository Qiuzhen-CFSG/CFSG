module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.QuotientGeometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.ResidualTransport
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.SmallIndexSolvable

/-!
# The actual binary component intersection and its residual

Transport the component intersection and component Sylow subgroup through a
specified isomorphism from the actual quotient component. The residual's
normal two-core has index three, so the residual is solvable. Every
three-subgroup of the intersection embeds in that residual and has order at
most three. These are separate inputs: the order bound alone does not exclude
a perfect three-dimensional Levi factor.

Source: Aschbacher--Smith, 15.3.43(a),(e) and its binary paragraph, printed
pp.1139--1140. The model-embedding construction adapts the independently
proved BinaryHigher transport for 15.3.28, without using its source hypotheses.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection.FiveExclusion
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions

variable {G : Type*} [Group G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
variable {H : Type*} [Group H] (e : c.toComponentAction.image L ≃* H)

/-- The literal component intersection in the supplied component coordinates. -/
noncomputable def intersection : Subgroup H :=
  ((c.toComponentAction.image (M ⊓ L)).subgroupOf
    (c.toComponentAction.image L)).map e.toMonoidHom

/-- The actual Sylow intersection in the same coordinates. -/
noncomputable def sylowIntersection : Subgroup H :=
  ((c.toComponentAction.image S).subgroupOf
    (c.toComponentAction.image L)).map e.toMonoidHom

/-- Include the model back in the actual quotient. -/
noncomputable def embedding : H →* c.toComponentAction.Quotient :=
  (c.toComponentAction.image L).subtype.comp e.symm.toMonoidHom

theorem embedding_injective : Function.Injective (embedding c e) :=
  (c.toComponentAction.image L).subtype_injective.comp e.symm.injective

theorem intersection_map_embedding :
    (intersection c e).map (embedding c e) = c.toComponentAction.image (M ⊓ L) := by
  rw [intersection, map_map]
  have he : (embedding c e).comp e.toMonoidHom = (c.toComponentAction.image L).subtype := by
    ext x
    exact congrArg Subtype.val (e.symm_apply_apply x)
  rw [he]
  exact map_subgroupOf_eq_of_le (map_mono (comap_mono inf_le_right))

theorem top_map_embedding :
    (⊤ : Subgroup H).map (embedding c e) = c.toComponentAction.image L := by
  rw [← MonoidHom.range_eq_map, embedding, MonoidHom.range_comp,
    e.symm.toMonoidHom.range_eq_top_of_surjective e.symm.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

/-- This comparison retains the original embedded component intersection. -/
noncomputable def intersectionEquiv :
    intersection c e ≃* c.toComponentAction.image (M ⊓ L) :=
  ((intersection c e).equivMapOfInjective (embedding c e) (embedding_injective c e)).trans
    (MulEquiv.subgroupCongr (intersection_map_embedding c e))

theorem intersection_ne_top : intersection c e ≠ ⊤ := by
  intro ht
  have he := congrArg (fun P => P.map (embedding c e)) ht
  rw [intersection_map_embedding, top_map_embedding, quotient_intersection_eq c] at he
  exact (ParabolicInspection.quotient_intersection_proper c).ne he

theorem sylowIntersection_le_intersection : sylowIntersection c e ≤ intersection c e := by
  apply map_mono
  intro x hx
  change (x : c.toComponentAction.Quotient) ∈ c.toComponentAction.image (M ⊓ L)
  rw [quotient_intersection_eq c]
  exact ⟨map_mono (comap_mono c.sylow_le_M) hx, x.property⟩

variable [Finite G]

/-- Restrict the actual quotient Sylow to its normal component, then transport it. -/
theorem exists_modelSylow :
    ∃ U : Sylow 2 H, (U : Subgroup H) = sylowIntersection c e := by
  obtain ⟨P, hP⟩ := c.sylow
  obtain ⟨T, hT⟩ := c.toComponentAction.image_sylow P hP
  obtain ⟨R, hR⟩ := T.exists_subgroupOf_eq_of_normal (c.toComponentAction.image L)
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (R : Subgroup _).map e.toMonoidHom = _
  rw [hR, hT]
  rfl

omit [Finite G] in
private theorem residual_eq : c.toComponentAction.image Yplus =
    threeResidualIn (c.toComponentAction.image (M ⊓ L)) := by
  rw [quotient_intersection_eq c]
  exact ParabolicInspection.quotient_residual_on_component c

omit [Finite G] in
private theorem actor_le_intersection :
    c.toComponentAction.image Yplus ≤ c.toComponentAction.image (M ⊓ L) := by
  rw [residual_eq c]
  exact map_subtype_le _

/-- The actor remains solvable after passing to the actual component quotient. -/
theorem actor_solvable (hs : IsSimpleGroup L) :
    Group.IsSolvable (c.toComponentAction.image Yplus) := by
  let : Group.IsNilpotent (pCore 2 (c.toComponentAction.image Yplus)) :=
    pCore_isPGroup.isNilpotent
  exact (pCore 2 (c.toComponentAction.image Yplus)).isSolvable_of_index_le_four
    (by rw [quotient_actor_index c hs]; decide)

/-- Solvability is transported for the literal prime-to-three residual. -/
theorem intersection_residual_solvable (hs : IsSimpleGroup L) :
    Group.IsSolvable (primeToResidual 3 (intersection c e)) := by
  let : Finite H := Finite.of_equiv (c.toComponentAction.image L) e.toEquiv
  let := actor_solvable c hs
  have hres := residual_eq c
  rw [threeResidualIn_eq_primeToResidual] at hres
  have hsR : Group.IsSolvable
      (primeToResidual 3 (c.toComponentAction.image (M ⊓ L))) := by
    have hh : Group.IsSolvable
        ((primeToResidual 3 (c.toComponentAction.image (M ⊓ L))).map
          (c.toComponentAction.image (M ⊓ L)).subtype) := hres ▸ inferInstance
    let := hh
    let f := (primeToResidual 3 (c.toComponentAction.image (M ⊓ L))).equivMapOfInjective
      (c.toComponentAction.image (M ⊓ L)).subtype Subtype.val_injective
    exact Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective
  let f := (intersectionEquiv c e).toMonoidHom
  have hm : Group.IsSolvable ((primeToResidual 3 (intersection c e)).map f) := by
    rw [map_primeToResidual_of_surjective 3 f (intersectionEquiv c e).surjective]
    exact hsR
  let := hm
  let g := (primeToResidual 3 (intersection c e)).equivMapOfInjective f
    (intersectionEquiv c e).injective
  exact Group.isSolvable_of_isSolvable_injective (f := g.toMonoidHom) g.injective

omit [Finite G] in
/-- The nontrivial residual quotient forces three to divide the local order. -/
theorem intersection_three_dvd (hs : IsSimpleGroup L) :
    3 ∣ Nat.card (intersection c e) := by
  rw [Nat.card_congr (intersectionEquiv c e).toEquiv]
  have hd : 3 ∣ Nat.card (c.toComponentAction.image Yplus) := by
    rw [← quotient_actor_index c hs]
    exact (pCore 2 (c.toComponentAction.image Yplus)).index_dvd_card
  exact hd.trans (card_dvd_of_le (actor_le_intersection c))

/-- Every actual three-subgroup has order at most three, not merely rank one. -/
theorem intersection_three_subgroup_bound (hs : IsSimpleGroup L)
    (X : Subgroup H) (hX : X ≤ intersection c e) (hp : IsPGroup 3 X) :
    Nat.card X ≤ 3 := by
  let A := X.map (embedding c e)
  have hAP : A ≤ c.toComponentAction.image (M ⊓ L) := by
    rw [← intersection_map_embedding c e]
    exact map_mono hX
  have hAY : A ≤ c.toComponentAction.image Yplus := by
    intro x hx
    obtain ⟨n, hn⟩ := (hp.map (embedding c e)) (⟨x, hx⟩ : A)
    rw [residual_eq c]
    refine mem_map.mpr ⟨⟨x, hAP hx⟩, mem_primePowerGenerated_of_pow (n := n) ?_, rfl⟩
    exact Subtype.ext (congrArg (fun a : A => (a : c.toComponentAction.Quotient)) hn)
  have hd : Nat.card A ∣ Nat.card (c.toComponentAction.image Yplus) := card_dvd_of_le hAY
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2)
    (G := c.toComponentAction.image Yplus)).exists_card_eq
  have hcard : Nat.card (c.toComponentAction.image Yplus) = 2 ^ k * 3 := by
    rw [← (pCore 2 (c.toComponentAction.image Yplus)).card_mul_index,
      hk, quotient_actor_index c hs]
  rw [hcard] at hd
  obtain ⟨j, hj⟩ := (hp.map (embedding c e)).exists_card_eq
  have hc : Nat.Coprime (Nat.card A) (2 ^ k) := by
    rw [hj]
    exact ((by decide : Nat.Coprime 3 2).pow_left j).pow_right k
  have hb := Nat.le_of_dvd (by decide : 0 < 3) (hc.dvd_mul_left.mp hd)
  simpa only [A, card_map_of_injective (embedding_injective c e)] using hb

/-- A common full flag is obtained from the actual Sylow, preserving its coordinates. -/
theorem exists_fullFlag {m : ℕ} (f : c.toComponentAction.image L ≃* LinearGroup (m + 1)) :
    ∃ b : Basis m, sylowIntersection c f = cutStabilizer b Set.univ := by
  obtain ⟨U, hU⟩ := exists_modelSylow c f
  obtain ⟨b, hb⟩ := sylow_eq_cutStabilizer U
  exact ⟨b, hU.symm.trans hb⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection.FiveExclusion

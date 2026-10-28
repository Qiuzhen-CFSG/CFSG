module
public import Theory.Representation.BinaryNaturalDual.FiveActors.Hyperplanes
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.Representation.BinaryOffender.NormalizerExtension

/-!
# FF witnesses for binary natural and contragredient pairs

A two-space radical has rank four or six in dimensions four and five,
while its fixed codimension on the natural/dual pair is four or five.
It is therefore an actual offender. Inner/inverse-transpose coverage
identifies any nonisomorphic automorphism twist with the dual, retaining
one group marking on both coordinates, and transports the offender to
the faithful image of that pair.

The chosen-module application in `NonFFSourceDoubledFF` descends the
original conjugator through its characteristic action kernel and supplies
all coordinate premises. This proves the FF rows used in the reduction
of Table 7.1.1, without the separate ambient doubled-natural exclusion.
Source: Aschbacher--Smith, 7.1 and H.9, printed pp.696 and389--392.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open BinaryLinear.OuterCyclic

/-- A two-space radical is an offender on the binary natural/dual pair
in dimensions four and five. -/
theorem doubledFF_naturalDual {n : ℕ} (hn : n = 4 ∨ n = 5) :
    IsFFModule (BinaryNaturalDual.naturalDualRepresentation (V := Space n)) := by
  have hnspace : Module.finrank (ZMod 2) (Space n) = n := by simp [Space]
  obtain ⟨b,hb⟩ := exists_linearIndependent_of_le_finrank (R := ZMod 2) (M := Space n)
    (n := 2) (by rw [hnspace]; omega)
  let U := Submodule.span (ZMod 2) (Set.range b)
  have hd : Module.finrank (ZMod 2) U = 2 := (finrank_span_eq_card hb).trans (by simp)
  have hu : U ≠ ⊥ := by intro he; rw [he, finrank_bot] at hd; omega
  have hut : U ≠ ⊤ := by
    intro he
    rw [he, finrank_top, hnspace] at hd
    omega
  have hq : Module.finrank (ZMod 2) ((Space n) ⧸ U) = n - 2 := by
    have hh := U.finrank_quotient_add_finrank
    rw [hd, hnspace] at hh
    omega
  have hc : Nat.card (BinaryLinear.radical U) = 2 ^ ((n - 2) * 2) := by
    rw [Nat.card_congr (BinaryNaturalDual.FiveActors.equiv U).toEquiv]
    change Nat.card (((Space n) ⧸ U) →ₗ[ZMod 2] U) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap, hq, hd,
      Nat.card_zmod]
  have hr : rank (BinaryLinear.radical U) = (n - 2) * 2 := by
    rw [rank, hc, Nat.log_pow (by decide : 1 < 2)]
  have hne : BinaryLinear.radical U ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hc
    rcases hn with rfl | rfl <;> norm_num at hc
  have hfix : fixedSpace BinaryNaturalDual.naturalDualRepresentation
      (BinaryLinear.radical U) = U.prod U.dualAnnihilator := by
    simpa only [fixedSpace_comp_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using
      BinaryNaturalDual.fixedSpace_radical U hu hut
  have hcost := fixedCodim_add_finrank
    (BinaryNaturalDual.naturalDualRepresentation (V := Space n)) (BinaryLinear.radical U)
  rw [hfix, BinaryNaturalDual.finrank_prod_dualAnnihilator] at hcost
  have hpair : Module.finrank (ZMod 2) (BinaryNaturalDual.Space (Space n)) = 2*n := by
    simp [BinaryNaturalDual.Space, Module.finrank_prod, Subspace.dual_finrank_eq,
      hnspace, two_mul]
  rw [hnspace, hpair] at hcost
  refine ⟨BinaryLinear.radical U, ⟨hne,inferInstance⟩, ?_⟩
  rw [hr]
  rcases hn with rfl | rfl <;> omega

/-- The natural/dual model acts faithfully on its actual vector space. -/
private theorem doubledFF_naturalDual_injective {n : ℕ} :
    Function.Injective (BinaryNaturalDual.naturalDualRepresentation (V := Space n)) := by
  intro a b hab
  apply LinearEquiv.ext
  intro v
  simpa only [BinaryNaturalDual.naturalDualRepresentation_apply] using
    congrArg Prod.fst (LinearMap.congr_fun hab (v,0))

private theorem doubledFF_dot_graph {n : ℕ} (g : LinearGroup n) (v : Space n) :
    dotProductEquiv (ZMod 2) (Fin n) (graphLinear n g v) =
      g.symm.dualMap (dotProductEquiv (ZMod 2) (Fin n) v) := by
  apply LinearMap.ext
  intro w
  change dotProduct (graphLinear n g v) w = dotProduct v (g.symm w)
  simpa only [g.apply_symm_apply] using graphLinear_dotProduct g v (g.symm w)

/-- The original nonisomorphic twist forces the contragredient coordinate;
the group marking is unchanged on both summands. -/
theorem doubledFF_pair_coordinates {J U : Type*} [Group J]
    [AddCommGroup U] [Module (ZMod 2) U] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (ρ : Representation (ZMod 2) J U) (q : J →* LinearGroup n)
    (e : U ≃ₗ[ZMod 2] Space n) (he : ∀ j v, e (ρ j v) = q j (e v))
    (α : MulAut J) (a : MulAut (LinearGroup n))
    (ha : ∀ j, a (q j) = q (α j))
    (hne : ¬ Nonempty (ρ.Equiv (ρ.comp α.toMonoidHom))) :
    ∃ E : (U × U) ≃ₗ[ZMod 2] BinaryNaturalDual.CoordinateSpace n,
      ∀ j v, E ((ρ.prod (ρ.comp α.toMonoidHom)) j v) =
        BinaryNaturalDual.naturalDualRepresentation (q j) (E v) := by
  obtain ⟨g,hg | hg⟩ := inner_graph hn a
  · exfalso
    apply hne
    let b := (e.trans g).trans e.symm
    refine ⟨Representation.Equiv.mk b ?_⟩
    intro j
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (b (ρ j v)) = e (ρ (α j) (b v))
    rw [he]
    change e (e.symm (g (e (ρ j v)))) = q (α j) (e (e.symm (g (e v))))
    rw [e.apply_symm_apply, e.apply_symm_apply, he, ← ha, hg]
    change g (q j (e v)) = g (q j (g.symm (g (e v))))
    rw [g.symm_apply_apply]
  · let c := (e.trans (graphLinear n g).symm).trans (dotProductEquiv (ZMod 2) (Fin n))
    refine ⟨e.prodCongr c, ?_⟩
    intro j v
    rw [BinaryNaturalDual.naturalDualRepresentation_apply]
    apply Prod.ext
    · exact he j v.1
    · change c (ρ (α j) v.2) = (q j).symm.dualMap (c v.2)
      dsimp only [c, LinearEquiv.trans_apply]
      rw [he, ← ha, hg]
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
        LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
      exact doubledFF_dot_graph (q j) _

/-- The literal image of a nonisomorphic twisted binary natural pair is FF. -/
theorem doubledFF_pair_image {J U : Type*} [Group J]
    [AddCommGroup U] [Module (ZMod 2) U] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (ρ : Representation (ZMod 2) J U) (q : J →* LinearGroup n)
    (hq : Function.Surjective q)
    (e : U ≃ₗ[ZMod 2] Space n) (he : ∀ j v, e (ρ j v) = q j (e v))
    (α : MulAut J) (a : MulAut (LinearGroup n))
    (ha : ∀ j, a (q j) = q (α j))
    (hne : ¬ Nonempty (ρ.Equiv (ρ.comp α.toMonoidHom))) :
    IsFFModule (imageRepresentation (ρ.prod (ρ.comp α.toMonoidHom))) := by
  let σ := BinaryNaturalDual.naturalDualRepresentation (V := Space n)
  have hf : Function.Injective (actionHom σ) := by
    intro x y hh
    apply doubledFF_naturalDual_injective
    exact congrArg (imageRepresentation σ) hh
  have hmodel : IsFFModule (imageRepresentation σ) :=
    (doubledFF_naturalDual hn).map_equivariant σ (imageRepresentation σ)
      (actionHom σ) hf (LinearEquiv.refl _ _) (fun _ _ => rfl)
  obtain ⟨E,hE⟩ := doubledFF_pair_coordinates hn ρ q e he α a ha hne
  apply image_isFFModule_of_equivariant _ σ q hq E.symm _ hmodel
  intro j w
  apply E.injective
  rw [hE, E.apply_symm_apply, E.apply_symm_apply]

end CFSG.Quasithin.Chapter7.NormalizedSource

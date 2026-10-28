module

public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.PPerfectHom

/-!
# Three-free invariant subgroups in an actual containing model

Restrict the original full Sylow to a subnormal containing subgroup and
transport the invariant subgroup along an actual model equivalence. If
the model forces every three-free Sylow-invariant subgroup to be a
two-group, a two-perfect such subgroup is trivial.

Source application: the Held exclusion in Aschbacher–Smith 1.3.8,
printed p.513; the transport and residual argument are general.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- Transport a three-free Sylow-invariant subgroup to the containing model,
then use two-perfection to kill the resulting two-group. -/
theorem eq_bot_of_three_free_model
    (T : Sylow 2 G) {X D : Subgroup G} (hD : D.IsSubnormal) (hXD : X ≤ D)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hp : IsPPerfect 2 X) (hthree : ¬ 3 ∣ Nat.card X) (e : D ≃* H)
    (hmodel : ∀ (S : Sylow 2 H) (V : Subgroup H),
      (S : Subgroup H) ≤ normalizer (V : Set H) →
      ¬ 3 ∣ Nat.card V → IsPGroup 2 V) : X = ⊥ := by
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal D hD
  let V := (X.subgroupOf D).map e.toMonoidHom
  let a : X ≃* V := (subgroupOfEquivOfLe hXD).symm.trans (e.subgroupMap _)
  have hnD : (S : Subgroup D) ≤ normalizer (X.subgroupOf D : Set D) := by
    rw [hS, ← subgroupOf_normalizer_eq hXD]
    exact comap_mono hn
  have hnV : (S : Subgroup D).map e.toMonoidHom ≤ normalizer (V : Set H) :=
    (map_mono hnD).trans ((X.subgroupOf D).le_normalizer_map e.toMonoidHom)
  have hv3 : ¬ 3 ∣ Nat.card V := by
    rw [← Nat.card_congr a.toEquiv]
    exact hthree
  have hv := hmodel (S.mapSurjective (f := e.toMonoidHom) e.surjective) V hnV hv3
  have hz := (hp.of_surjective a.toMonoidHom a.surjective).hom_eq_one_of_isPGroup
    hv (MonoidHom.id V)
  apply eq_bot_iff.mpr
  intro x hx
  have hx' : a ⟨x,hx⟩ = 1 := DFunLike.congr_fun hz _
  have he : (⟨x,hx⟩ : X) = 1 := a.injective (by simpa only [map_one] using hx')
  exact congrArg Subtype.val he

end Theory.GroupTheory

module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.WreathRecognition.ResidualModel.Concrete
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Recognition of the residual as A₄ × A₄

The genuine natural action of M on V restricts to a surjection from Y onto
the order-nine cubic base when its image is the two-residual of the
orthogonal actor. The hypothesis C_Y(V)=V identifies its kernel with V,
so V is normal in Y and has index nine. Schur–Zassenhaus constructs a
complement to this order-sixteen kernel. Restricting the original actor map
to that complement gives an isomorphism onto the cubic base, and the supplied
compatibility equation identifies the actual conjugation action with the
literal coordinate action. Thus Y is the concrete affine group, already
identified with A₄ × A₄ in the descendant module.

This proves the conditional model contract needed in 15.3.9. Its source
assembly must supply the image equality from 15.3.7 and the centralizer
equality from the contrary core-equality branch; neither exclusion of
15.3.9 is used here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7–9, printed pp.1122–1123 (PDF pp.1139–1140).
-/

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.WreathRecognition
open ResidualModel

variable {G : Type*} [Group G]

/-- The residual with its genuine coordinate action is the alternating pair.
The normal Hall splitting and its compatible actor isomorphism are constructed
from the stated centralizer and image equalities. -/
public theorem residual_model_of_natural_action [Finite G]
    {M Y V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (hYM : Y ≤ M) (hVY : V ≤ Y)
    (hCY : Y ⊓ centralizer (V : Set G) = V)
    (himage : (Y.subgroupOf M).map d.actor =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    Nonempty (Y ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))) := by
  let f₀ : Y →* OrthogonalActor := d.actor.comp (inclusion hYM)
  have hrange : f₀.range = cubicBase := by
    rw [cubicBase_eq_residual, ← himage]
    ext a
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨inclusion hYM y, y.property, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  let f : Y →* cubicBase := f₀.codRestrict cubicBase
    (fun y => hrange ▸ (show f₀ y ∈ f₀.range from ⟨y, rfl⟩))
  have hf : Function.Surjective f := by
    intro a
    have ha : (a : OrthogonalActor) ∈ f₀.range := by rw [hrange]; exact a.property
    obtain ⟨y, hy⟩ := ha
    exact ⟨y, Subtype.ext hy⟩
  let N := V.subgroupOf Y
  have hker : f.ker = N := by
    ext y
    constructor
    · intro hy
      have hk : inclusion hYM y ∈ d.actor.ker := congrArg cubicBase.subtype hy
      rw [d.ker_actor] at hk
      have hm : (y : G) ∈ Y ⊓ centralizer (V : Set G) := ⟨y.property, hk⟩
      change (y : G) ∈ V
      rw [← hCY]
      exact hm
    · intro hy
      have hm : (y : G) ∈ Y ⊓ centralizer (V : Set G) := hCY.symm ▸ hy
      have hk : inclusion hYM y ∈ d.actor.ker := d.ker_actor.symm ▸ hm.2
      exact Subtype.ext hk
  let : N.Normal := hker ▸ inferInstance
  have hindex : N.index = 9 := by
    rw [← hker, index_ker, f.range_eq_top_of_surjective hf, card_top, cubicBase_card]
  have hcard : Nat.card N = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVY).toEquiv).trans d.card_vector
  obtain ⟨K, hcomp⟩ := exists_right_complement'_of_coprime
    (show Nat.Coprime (Nat.card N) N.index by rw [hcard, hindex]; decide)
  let fk : K →* cubicBase := f.comp K.subtype
  have hfk : Function.Bijective fk := by
    constructor
    · intro a b hab
      have hn : (a : Y)⁻¹ * b ∈ N := by
        rw [← hker]
        change f ((a : Y)⁻¹ * b) = 1
        rw [map_mul, map_inv, show f a = f b from hab, inv_mul_cancel]
      have hk : (a : Y)⁻¹ * b ∈ K := K.mul_mem (K.inv_mem a.property) b.property
      exact Subtype.ext (inv_mul_eq_one.mp ((disjoint_def.mp hcomp.disjoint) hn hk))
    · intro z
      obtain ⟨y, rfl⟩ := hf z
      obtain ⟨⟨n, k⟩, rfl⟩ := hcomp.2 y
      refine ⟨k, ?_⟩
      have hn : f n = 1 := by
        change (n : Y) ∈ f.ker
        rw [hker]
        exact n.property
      change f k = f ((n : Y) * k)
      rw [map_mul, hn, one_mul]
  let eK : K ≃* cubicBase := MulEquiv.ofBijective fk hfk
  let eN : N ≃* OrthogonalVector := (subgroupOfEquivOfLe hVY).trans d.coordinates
  let γ : K →* MulAut N :=
    N.normalizerMonoidHom.comp (inclusion (N.normalizer_eq_top ▸ le_top))
  have hagree (k : K) : (γ k).trans eN = eN.trans (pairAction (eK k)) := by
    apply MulEquiv.ext
    intro n
    exact d.compatible (inclusion hYM k.val) ((subgroupOfEquivOfLe hVY) n)
  let e : Y ≃* PairAffine :=
    (SemidirectProduct.mulEquivSubgroup hcomp).symm.trans (SemidirectProduct.congr eN eK hagree)
  obtain ⟨model⟩ := pairAffine_model
  exact ⟨e.trans model⟩

end CFSG.Quasithin.Chapter15.Section03.WreathRecognition

module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Rigidity
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.SixLetterRadicalDisplacement.PermutationQuotients.TranspositionRank
public import Theory.Representation.SixLetterRadicalDisplacement.PermutationQuotients.Faithfulness
public import Theory.Representation.SixLetterTransvections
import Mathlib.Tactic

/-!
# Incompatible transvections in the two marked section actions

For a nonidentity involution with natural displacement at most one, rigidity
of the cyclic elementary actor gives a conjugate of a single-transposition
group. Thus this same permutation is a transposition in the specified natural
marking. On every noncentral quotient of the correspondingly marked syntheme
module its displacement is at least two. The augmentation cover passes through
the canonical surjection onto the natural module without changing the actor.
For A₆, faithfulness of the noncentral syntheme quotient and the general
faithful-transvection obstruction suffice.

The nonidentity hypothesis is essential: Lean's transvection set includes the
identity. The source critical-pair symmetry and 13.8.9–10 must still produce
this actor and both displacement bounds on the actual endpoint sections.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 13.8.34(1), printed p.968 (PDF p.985).
This proves the linear contradiction, not the source line containments.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineObstruction
open ComponentSieve.SixAndG2.NaturalSix
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six

/-- Rigidity identifies the actual actor as a transposition in the chosen
natural marking, not just in an unspecified outer-related representation. -/
theorem isSwap_of_natural_displacement (t : Symmetric) (hne : t ≠ 1)
    (hsq : t ^ 2 = 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (symmetricAction t - LinearMap.id)) ≤ 1) :
    t.IsSwap := by
  have hel : IsElementaryTwo (zpowers t) :=
    ⟨fun h => hne (zpowers_eq_bot.mp h), IsElementaryAbelian.zpowers_of_pow_eq_one hsq⟩
  have hc : fixedCodim symmetricAction (zpowers t) ≤ 1 := by
    rwa [fixedCodim_zpowers_eq_displacement_rank]
  obtain ⟨g, hg⟩ := natural_small_codim_conjugate hel hc
  have ht : t ∈ (disjointTranspositions 6 1).map (MulAut.conj g).toMonoidHom :=
    hg ▸ mem_zpowers t
  obtain ⟨a, ha, hea⟩ := ht
  have hane : a ≠ 1 := by
    intro h
    apply hne
    rw [h, map_one] at hea
    exact hea.symm
  have haswap : a.IsSwap := by
    obtain ⟨i, rfl⟩ := (mem_disjointTranspositions_iff (1 : Fin 4) a).mp ha
    fin_cases i
    · exact (hane (by decide)).elim
    · exact ⟨0, 1, by decide, by decide⟩
  obtain ⟨i, j, hij, rfl⟩ := haswap
  rw [← hea]
  change (g * Equiv.swap i j * g⁻¹).IsSwap
  rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right]
  exact ⟨g i, g j, g.injective.ne hij, rfl⟩

private theorem displacement_image {A U W : Type*} [Group A]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) A U) (σ : Representation (ZMod 2) A W)
    (q : U →ₗ[ZMod 2] W) (hq : Function.Surjective q)
    (heq : ∀ a v, q (τ a v) = σ a (q v)) (a : A) :
    (LinearMap.range (τ a - LinearMap.id)).map q = LinearMap.range (σ a - LinearMap.id) := by
  ext w
  constructor
  · rintro ⟨u, ⟨v, rfl⟩, rfl⟩
    exact ⟨q v, by simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, heq]⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := hq w
    exact ⟨τ a v - v, ⟨v, rfl⟩, by simp only [map_sub, heq, LinearMap.sub_apply, LinearMap.id_apply]⟩

open Representation.SixLetterRadicalDisplacement.PermutationQuotients

/-- A nonidentity involution moving at most a line on a module which maps
onto the specified natural action moves at least a plane on every noncentral
syntheme quotient with the same actor marking. The map to the natural module
also covers the five-dimensional augmentation model. -/
theorem symmetric_quotient_rank_ge_two {A U Q : Type*} [Group A]
    [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U]
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (e : A ≃* Symmetric) (τ : Representation (ZMod 2) A U)
    (q : U →ₗ[ZMod 2] Natural) (hq : Function.Surjective q)
    (heq : ∀ a v, q (τ a v) = symmetricAction (e a) (q v))
    (σ : Representation (ZMod 2) A Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (hfe : ∀ a v, f (rho (e a) v) = σ a (f v))
    (hnc : ∃ a v, σ a v ≠ v) (t : A) (hne : t ≠ 1) (hsq : t ^ 2 = 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (τ t - LinearMap.id)) ≤ 1) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) := by
  have hnat : Module.finrank (ZMod 2)
      (LinearMap.range (symmetricAction (e t) - LinearMap.id)) ≤ 1 := by
    have himage : (LinearMap.range (τ t - LinearMap.id)).map q =
        LinearMap.range (symmetricAction (e t) - LinearMap.id) :=
      displacement_image τ (symmetricAction.comp e.toMonoidHom) q hq heq t
    have hd := (LinearEquiv.ofEq _ _ himage).finrank_eq
    exact hd ▸ (Submodule.finrank_map_le q _).trans hr
  have ht := isSwap_of_natural_displacement (e t)
    (fun h => hne (e.injective (h.trans e.map_one.symm)))
    (by rw [← map_pow, hsq, map_one]) hnat
  exact TranspositionRank.actor_rank_ge_two e σ f hf hfe hnc t ht

/-- Both earlier module alternatives provide the required surjection onto
the same marked natural action. In the cover case the canonical quotient
`coreToNatural` is used, so the actor is unchanged. -/
theorem symmetric_natural_or_cover_rank_ge_two {A U Q : Type*} [Group A]
    [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U]
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (e : A ≃* Symmetric) (τ : Representation (ZMod 2) A U)
    (model : (∃ q : U ≃ₗ[ZMod 2] Natural,
        ∀ a v, q (τ a v) = symmetricAction (e a) (q v)) ∨
      (∃ q : U ≃ₗ[ZMod 2] Augmentation,
        ∀ a v, q (τ a v) = BinaryPermutation.coreRepresentation (Fin 6) (e a) (q v)))
    (σ : Representation (ZMod 2) A Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (hfe : ∀ a v, f (rho (e a) v) = σ a (f v))
    (hnc : ∃ a v, σ a v ≠ v) (t : A) (hne : t ≠ 1) (hsq : t ^ 2 = 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (τ t - LinearMap.id)) ≤ 1) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) := by
  rcases model with ⟨q, he⟩ | ⟨q, he⟩
  · exact symmetric_quotient_rank_ge_two e τ q.toLinearMap q.surjective he
      σ f hf hfe hnc t hne hsq hr
  · apply symmetric_quotient_rank_ge_two e τ
      ((BinaryPermutation.coreToNatural (Fin 6)).comp q.toLinearMap)
      (BinaryPermutation.coreToNatural_surjective.comp q.surjective) _
      σ f hf hfe hnc t hne hsq hr
    intro a v
    change BinaryPermutation.coreToNatural (Fin 6) (q (τ a v)) = _
    rw [he, BinaryPermutation.coreToNatural_equivariant]
    rfl

/-- The two source actions cannot both have displacement at most one for
the same genuinely nonidentity involution. -/
theorem symmetric_not_both_small {A U Q : Type*} [Group A]
    [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U]
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (e : A ≃* Symmetric) (τ : Representation (ZMod 2) A U)
    (q : U →ₗ[ZMod 2] Natural) (hq : Function.Surjective q)
    (heq : ∀ a v, q (τ a v) = symmetricAction (e a) (q v))
    (σ : Representation (ZMod 2) A Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (hfe : ∀ a v, f (rho (e a) v) = σ a (f v))
    (hnc : ∃ a v, σ a v ≠ v) (t : A) (hne : t ≠ 1) (hsq : t ^ 2 = 1)
    (hτ : Module.finrank (ZMod 2) (LinearMap.range (τ t - LinearMap.id)) ≤ 1)
    (hσ : Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) ≤ 1) : False := by
  have h := symmetric_quotient_rank_ge_two e τ q hq heq σ f hf hfe hnc t hne hsq hτ
  omega

/-- In the alternating case the faithful-action theorem alone excludes a
nonidentity actor with displacement at most one. -/
theorem alternating_not_small {A U : Type*} [Group A]
    [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U]
    (e : A ≃* Alternating) (τ : Representation (ZMod 2) A U)
    (hfaith : Function.Injective τ) (t : A) (hne : t ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (τ t - LinearMap.id)) ≤ 1) : False := by
  have heq : ∀ v, (LinearEquiv.refl (ZMod 2) U)
      ((τ.comp e.symm.toMonoidHom) (e t) v) =
      τ t ((LinearEquiv.refl (ZMod 2) U) v) := by
    intro v
    change τ (e.symm (e t)) v = τ t v
    rw [e.symm_apply_apply]
  have hd := TranspositionRank.displacement_finrank_eq (LinearEquiv.refl (ZMod 2) U)
    ((τ.comp e.symm.toMonoidHom) (e t)) (τ t) heq
  have h := Representation.SixLetterTransvections.alternating_eq_one_of_displacement_le_one
    (τ.comp e.symm.toMonoidHom) (hfaith.comp e.symm.injective) (e t) (hd.symm ▸ hr)
  exact hne (e.injective (h.trans e.map_one.symm))

/-- For the alternating endpoint the actual noncentral syntheme quotient
itself is faithful; no extra faithfulness hypothesis is needed. -/
theorem alternating_quotient_not_small {A Q : Type*} [Group A]
    [AddCommGroup Q] [Module (ZMod 2) Q] [Module.Finite (ZMod 2) Q]
    (e : A ≃* Alternating) (σ : Representation (ZMod 2) A Q)
    (f : P →ₗ[ZMod 2] Q) (hf : Function.Surjective f)
    (hfe : ∀ a v, f (rhoA (e a) v) = σ a (f v))
    (hnc : ∃ a v, σ a v ≠ v) (t : A) (hne : t ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) ≤ 1) : False :=
  alternating_not_small e σ
    (alternating_actor_faithful_of_noncentral_quotient e σ f hf hfe hnc) t hne hr

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineObstruction

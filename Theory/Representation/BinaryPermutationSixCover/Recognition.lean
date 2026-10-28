module

public import Theory.Representation.BinaryPermutationSixCover.Universal
public import Theory.Representation.ElementaryPerfectSplit
public import Mathlib.FieldTheory.Finiteness

/-!
# Recognition of the order-32 marked augmentation cover

The universal augmentation cover surjects onto a perfect central cover of the
natural A6 module. When the target has order 32, this surjection is bijective.
The resulting equivalence retains the specified alternating actor, the map to
the natural module, and its constant-line kernel. For a perfect split elementary
extension, commutator generation follows from perfectness of the whole group.

Source: Aschbacher–Smith, I.1.5–6 and I.2.2(6), printed pp.408 and 412,
combined manuscript of 1 March 2004.
-/

@[expose] public section

open Representation Representation.OneCohomology
namespace BinaryPermutation.SixCover
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

theorem core_equiv_of_card_thirtyTwo
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) U)
    (P : σ.IntertwiningMap (alternatingNaturalRepresentation (Fin 6)))
    (hP : IsCover P) (hcard : Nat.card U = 32) :
    ∃ E : U ≃ₗ[ZMod 2] core (Fin 6),
      (∀ g u, E (σ g u) = coreRepresentation (Fin 6) g.val (E u)) ∧
      (∀ u, coreToNatural (Fin 6) (E u) = P u) ∧
      (∀ u, P u = 0 ↔ (E u).val ∈ constants (Fin 6)) := by
  obtain ⟨f, hf, heq, hpf⟩ := core_quotient_of_alternating_cover σ P hP
  have hcore : Nat.card (core (Fin 6)) = 32 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_core]
    norm_num
  have hfin : Function.Bijective f :=
    (Nat.bijective_iff_surjective_and_card f).mpr ⟨hf, hcore.trans hcard.symm⟩
  let F : core (Fin 6) ≃ₗ[ZMod 2] U := LinearEquiv.ofBijective f hfin
  have hp (u : U) : coreToNatural (Fin 6) (F.symm u) = P u := by
    rw [← hpf, show f (F.symm u) = u from F.apply_symm_apply u]
  refine ⟨F.symm, ?_, hp, ?_⟩
  · intro g u
    apply F.injective
    rw [F.apply_symm_apply]
    exact (heq g (F.symm u)).trans (congrArg (σ g) (F.apply_symm_apply u)) |>.symm
  · intro u
    rw [← hp]
    rw [← Subtype.val_inj]
    exact Submodule.Quotient.mk_eq_zero _
end BinaryPermutation.SixCover

open scoped IsMulCommutative
namespace BinaryPermutation.SixCover
open Representation Representation.OneCohomology
variable {R : Type*} [Group R] [Finite R] [IsElementaryAbelian 2 R]

/-- Recognize a perfect split elementary extension from its marked natural
quotient. Both the action and the original quotient map are retained. -/
theorem core_mulEquiv_of_perfect_split
    (φ : alternatingGroup (Fin 6) →* MulAut R)
    [Group.IsPerfect (R ⋊[φ] alternatingGroup (Fin 6))]
    (q : R →* Multiplicative (natural (Fin 6)))
    (hqsur : Function.Surjective q)
    (hq : ∀ a r, (q (φ a r)).toAdd =
      naturalRepresentation (Fin 6) a.val (q r).toAdd)
    (hfix : ∀ r ∈ q.ker, ∀ a, φ a r = r)
    (hcard : Nat.card R = 32) :
    ∃ E : R ≃* Multiplicative (core (Fin 6)),
      (∀ a r, (E (φ a r)).toAdd =
        coreRepresentation (Fin 6) a.val (E r).toAdd) ∧
      (∀ r, coreToNatural (Fin 6) (E r).toAdd = (q r).toAdd) ∧
      (∀ r, r ∈ q.ker ↔ (E r).toAdd.val ∈ constants (Fin 6)) := by
  let σ := elementaryRepresentation (p := 2) φ
  let P : σ.IntertwiningMap (alternatingNaturalRepresentation (Fin 6)) :=
    (q.toAdditiveLeft.toZModLinearMap 2).intertwiningMap_of_isIntertwiningMap σ _
      (fun a r => hq a r.toMul)
  have hP : IsCover P := by
    refine ⟨?_, ?_, elementary_coinvariants_eq_top_of_perfect φ⟩
    · intro v
      obtain ⟨r, hr⟩ := hqsur (Multiplicative.ofAdd v)
      exact ⟨Additive.ofMul r, congrArg Multiplicative.toAdd hr⟩
    · intro r hr a
      exact congrArg Additive.ofMul (hfix r.toMul hr a)
  obtain ⟨E, hE, hqE, hkE⟩ := core_equiv_of_card_thirtyTwo σ P hP hcard
  exact ⟨E.toAddEquiv.toMultiplicativeRight, hE, hqE, hkE⟩
end BinaryPermutation.SixCover

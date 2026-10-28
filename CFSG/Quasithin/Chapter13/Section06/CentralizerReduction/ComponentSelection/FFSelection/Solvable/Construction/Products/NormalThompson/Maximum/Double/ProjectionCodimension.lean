module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double.Reduction
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.GeneralLinearNatural
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Coordinate codimensions in the native double S₃ case

In B.5.6(3), the two invariant summands split the quotient by the global
fixed space. For an S₃ factor, the S₅ and SL₃ alternatives are impossible;
the remaining natural action is faithful and its summand is the image of
the literal moved space. The other factor fixes this summand: each of its
displacements lies in both disjoint quotient summands.

Thus the action on each summand factors through the literal internal-product
projection. An elementary abelian subgroup of S₃ has rank at most one, and
faithfulness makes each nontrivial coordinate cost at least one fixed
codimension. These costs add on the quotient and are bounded by the fixed
codimension on the original module.

The final application supplies exactly the projection bound in
`minimalSolvable_twoFactor_maxima_of_projection_bound`, yielding the two
maximum-elementary intersection witnesses for the actual star action.
No separate support cardinalities or support-product equivalence are needed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(3),
printed p.105, and B.2.4, pp.75–76, as used in 13.6.13, p.929.
The model exclusions follow the native clauses, adapting the argument in
Chapter15's `SolvableProduct.Rank.Models` to `SourceFactorCase`.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.SourceInduction CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double.ProjectionCodimension
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

private theorem no_sl3 {F : Type*} [Field F]
    (e : SL(3,F) ≃* Equiv.Perm (Fin 3)) : False := by
  let := Atlas.sl_perfect (F := F) 3 (by decide)
  let : Group.IsPerfect (Equiv.Perm (Fin 3)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have h := Abelianization.commutator_subset_ker
    (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ)
  rw [Group.IsPerfect.commutator_eq_top] at h
  have hx := h (mem_top (Equiv.swap (0 : Fin 3) 1))
  have hn : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) ≠ 1 := by decide
  exact hn hx

private theorem natural_faithful (F : BinaryField) (d : ℕ)
    (e : ActionEquiv ρ (linearNatural F d)) : Function.Injective ρ := by
  intro g h he
  apply e.groupEquiv.injective
  apply specialLinearNatural_injective d
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := e.linearEquiv.surjective w
  change linearNatural F d (e.groupEquiv g) (e.linearEquiv v) =
    linearNatural F d (e.groupEquiv h) (e.linearEquiv v)
  rw [← e.intertwines, ← e.intertwines]
  exact congrArg e.linearEquiv (LinearMap.congr_fun he v)

private theorem factor_faithful {B : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ B U) (e : B ≃* Equiv.Perm (Fin 3)) :
    U.toSubmodule = moved ρ B ∧
      Function.Injective (((fixed ρ).quotientImage U).toRepresentation.comp B.subtype) := by
  cases h with
  | natural hm h =>
    refine ⟨hm, ?_⟩
    cases h with
    | linearTwo F h => exact natural_faithful _ F 2 h.some
    | symmetricFive h =>
      have hc := Nat.card_congr (h.some.groupEquiv.symm.trans e).toEquiv
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
        Nat.factorial] at hc
    | linearThree F _ h => exact (no_sl3 (h.some.groupEquiv.symm.trans e)).elim
  | doubleNatural F _ _ h => exact (no_sl3 (h.some.groupEquiv.symm.trans e)).elim
  | exceptional _ h => exact (no_sl3 (h.natural.groupEquiv.symm.trans e)).elim

private theorem elementary_rank_le_one [Finite D] (e : D ≃* Equiv.Perm (Fin 3))
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A) : rank A ≤ 1 := by
  let := hA
  obtain ⟨S, hS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  have hc : Nat.card D = 6 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hSc : Nat.card (S : Subgroup D) = 2 := by
    rw [S.card_eq_multiplicity, hc]
    change 2 ^ (Nat.factorization (2 * 3)) 2 = 2
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have hAc : Nat.card A ≤ 2 := (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hS)).trans_eq hSc
  exact (Nat.log_mono_right hAc).trans (by decide : Nat.log 2 2 ≤ 1)

private theorem rank_le_codim [Finite D] [FiniteDimensional (ZMod 2) V]
    (e : D ≃* Equiv.Perm (Fin 3)) (hf : Function.Injective ρ)
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A) : rank A ≤ fixedCodim ρ A := by
  by_cases h : A = ⊥
  · simp only [h, Representation.BinaryOffender.rank_bot, Nat.zero_le]
  · exact (elementary_rank_le_one e A hA).trans
      (fixedCodim_pos_of_faithful ρ hf h)

private theorem other_fixes_quotient {B : Subgroup D} {U W : Subrepresentation ρ}
    (hW : W.toSubmodule = moved ρ B)
    (hd : Disjoint ((fixed ρ).quotientImage U).toSubmodule
      ((fixed ρ).quotientImage W).toSubmodule)
    (b : B) (w : ((fixed ρ).quotientImage U).toSubmodule) :
    ((fixed ρ).quotientImage U).toRepresentation (b : D) w = w := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply Submodule.disjoint_def.mp hd
  · exact ((fixed ρ).quotientImage U).toSubmodule.sub_mem
      (((fixed ρ).quotientImage U).apply_mem_toSubmodule b w.property) w.property
  · obtain ⟨v, hv⟩ := (fixed ρ).toSubmodule.mkQ_surjective (w : V ⧸ (fixed ρ).toSubmodule)
    change (fixed ρ).quotientRepresentation b w.val - w.val ∈
      W.toSubmodule.map (fixed ρ).toSubmodule.mkQ
    rw [← hv, Subrepresentation.quotientRepresentation_mk]
    refine ⟨ρ b v - v, ?_, map_sub _ _ _⟩
    rw [hW]
    exact Submodule.subset_span ⟨b, b.property, v, Submodule.mem_top, rfl⟩

private theorem codim_sum [FiniteDimensional (ZMod 2) V]
    (U W : Subrepresentation ρ) (hc : IsCompl U.toSubmodule W.toSubmodule)
    (A : Subgroup D) :
    fixedCodim U.toRepresentation A + fixedCodim W.toRepresentation A = fixedCodim ρ A := by
  let e := U.toSubmodule.prodEquivOfIsCompl W.toSubmodule hc
  have he := fixedCodim_map_equivariant (U.toRepresentation.prod W.toRepresentation) ρ
    (MonoidHom.id D) e (fun g x => by
      change ρ g x.1.val + ρ g x.2.val = ρ g (x.1.val + x.2.val)
      exact (map_add _ _ _).symm) A
  simpa only [Subgroup.map_id, fixedCodim_prod] using he

/-- The additive bound on the original module, derived from all the native
quotient-module clauses and the actual S₃ identifications. -/
theorem projection_rank_le_fixedCodim [Finite D] [FiniteDimensional (ZMod 2) V]
    (c : SourceTwoFactorCase ρ)
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A) :
    rank (A.map c.product.fst) + rank (A.map c.product.snd) ≤ fixedCodim ρ A := by
  let U := (fixed ρ).quotientImage c.firstSpace
  let W := (fixed ρ).quotientImage c.secondSpace
  have h₁ := factor_faithful ρ c.firstCase e₁
  have h₂ := factor_faithful ρ c.secondCase e₂
  have hx₁ : ∀ (g : D) (w : U.toSubmodule),
      U.toRepresentation g w = U.toRepresentation (c.product.fst g : D) w := by
    intro g w
    have hg : g = (c.product.fst g : D) * (c.product.snd g : D) :=
      (c.product.equiv.apply_symm_apply g).symm.trans
        (c.product.apply_eq _ _)
    conv_lhs => rw [hg, map_mul, Module.End.mul_apply]
    rw [other_fixes_quotient ρ h₂.1 c.decomposition.disjoint]
  have hx₂ : ∀ (g : D) (w : W.toSubmodule),
      W.toRepresentation g w = W.toRepresentation (c.product.snd g : D) w := by
    intro g w
    have hg : g = (c.product.fst g : D) * (c.product.snd g : D) :=
      (c.product.equiv.apply_symm_apply g).symm.trans
        (c.product.apply_eq _ _)
    conv_lhs => rw [hg, map_mul, Module.End.mul_apply]
    exact other_fixes_quotient ρ h₁.1 c.decomposition.disjoint.symm _ _
  have hb₁ := rank_le_codim (U.toRepresentation.comp c.first.subtype) e₁ h₁.2
    (A.map c.product.fst) (hA.map c.product.fst)
  have hb₂ := rank_le_codim (W.toRepresentation.comp c.second.subtype) e₂ h₂.2
    (A.map c.product.snd) (hA.map c.product.snd)
  have he₁ := fixedCodim_map_equivariant U.toRepresentation
    (U.toRepresentation.comp c.first.subtype) c.product.fst (LinearEquiv.refl _ _) hx₁ A
  have he₂ := fixedCodim_map_equivariant W.toRepresentation
    (W.toRepresentation.comp c.second.subtype) c.product.snd (LinearEquiv.refl _ _) hx₂ A
  rw [← he₁] at hb₁
  rw [← he₂] at hb₂
  have hs := codim_sum (fixed ρ).quotientRepresentation U W c.decomposition A
  have hq := fixedCodim_quotient_add_subrepresentation_le ρ (fixed ρ) A
  omega
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double.ProjectionCodimension

open Stellmacher
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double
variable {G : Type*} [Group G] [Finite G]

/-- The literal restricted star representation satisfies the parent's
coordinate bound, with no support or splitting premise on the original U_v. -/
theorem star_twoFactor_projection_rank_le_fixedCodim (z v : G)
    [IsElementaryAbelian 2 (Uv z v)]
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (A : Subgroup (FFFactors.offenderActor (starRepresentation z v)))
    (hA : IsElementaryAbelian 2 A) :
    rank (A.map c.product.fst) + rank (A.map c.product.snd) ≤
      fixedCodim (FFFactors.offenderRepresentation (starRepresentation z v)) A := by
  exact ProjectionCodimension.projection_rank_le_fixedCodim _ c e₁ e₂ A hA

/-- Discharge the representation-theoretic premise of the double-factor
maximum-elementary reduction. The residual and minimal-solvable inputs are
exactly those of that reduction. -/
theorem minimalSolvable_twoFactor_maxima
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      pResidual 2 (FFFactors.offenderActor (starRepresentation z v))) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H₁ := c.first.map I.subtype
    let H₂ := c.second.map I.subtype
    ∃ E₁ E₂ : Subgroup (Gv v),
      E₁ ∈ elementaryAbelianMaxSubgroups (I.comap (starMk z v)) ∧
      E₂ ∈ elementaryAbelianMaxSubgroups (I.comap (starMk z v)) ∧
      E₁.map (starMk z v) ⊓ H₁ ≠ ⊥ ∧ E₂.map (starMk z v) ⊓ H₂ ≠ ⊥ := by
  exact minimalSolvable_twoFactor_maxima_of_projection_bound L T z v hz S hS hX c e₁ e₂ hF
    (star_twoFactor_projection_rank_le_fixedCodim z v c e₁ e₂)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double
end

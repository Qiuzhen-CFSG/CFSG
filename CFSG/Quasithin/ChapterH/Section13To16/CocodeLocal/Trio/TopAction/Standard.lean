module
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.Spaces
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Affine
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Full action on the standard trio's cocode top quotient

Summing coordinates on the three octads maps the even core into the binary
even core on three letters. Its kernel is the pair-generated space. The map
therefore descends through Golay and identifies the actual two-dimensional
cocode quotient with that three-letter core. The checked native affine
coordinate formula intertwines this map with the first quotient factor S₃.
Its action is faithful and GL₂(2) has order six, giving the full linear image.

Source: Aschbacher–Smith, H.15.6(2), printed p.401, top-quotient clause;
Aschbacher, *Sporadic Groups*, Chapter 7, §20.
-/

@[expose] public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode
open scoped BigOperators
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.TrioTop
noncomputable section

abbrev Two := BinaryPermutation.core (Fin 3)

def parityCore : Core →ₗ[ZMod 2] Two where
  toFun v := ⟨fun i => ∑ w : Vector, v.val (point (i,w)), by
    change (∑ i : Fin 3, ∑ w : Vector, v.val (point (i,w))) = 0
    rw [← Fintype.sum_prod_type']
    rw [Equiv.sum_comp point]
    exact v.property⟩
  map_add' v w := by ext i; simp [Finset.sum_add_distrib]
  map_smul' a v := by ext i; simp [Finset.mul_sum]

lemma parityCore_ker : parityCore.ker = TrioCalculation.pairCore standardTrio := by
  ext v
  rw [TrioCalculation.mem_pairCore_iff]
  change parityCore v = 0 ↔ _
  rw [Subtype.ext_iff, funext_iff]
  constructor
  · intro h B hB
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hB
    rw [← point_image i, Finset.sum_image]
    · exact h i
    · intro a _ b _ he
      exact (Prod.mk.inj (point.injective he)).2
  · intro h i
    have hi := h (standardTrioOctad i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [← point_image i, Finset.sum_image] at hi
    · exact hi
    · intro a _ b _ he
      exact (Prod.mk.inj (point.injective he)).2

def parityCocode : Cocode →ₗ[ZMod 2] Two :=
  codeInCore.liftQ parityCore (by
    rw [parityCore_ker]
    exact TrioCalculation.codeInCore_le_pairCore standardTrio)

lemma parityCocode_ker : parityCocode.ker = trioPairSpace standardTrio := by
  rw [parityCocode, Submodule.ker_liftQ, parityCore_ker,
    TrioCalculation.pairCore_quotient_image]
  rfl

def parityTop : (Cocode ⧸ trioPairSpace standardTrio) →ₗ[ZMod 2] Two :=
  (trioPairSpace standardTrio).liftQ parityCocode parityCocode_ker.ge

lemma parityTop_injective : Function.Injective parityTop := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ parityCocode_ker.le

def parityEquiv : (Cocode ⧸ trioPairSpace standardTrio) ≃ₗ[ZMod 2] Two :=
  LinearEquiv.ofBijective parityTop ⟨parityTop_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [finrank_trioPairQuotient, BinaryPermutation.finrank_core]
      rfl)).mp parityTop_injective⟩

lemma parityCore_equivariant (g : trioStabilizer standardTrio) (v : Core) :
    parityCore (coreRepresentation g.val v) =
      BinaryPermutation.coreRepresentation (Fin 3)
        (TrioCalculation.standardAffineHom g).1 (parityCore v) := by
  obtain ⟨t,ht⟩ := affineQuotient_spec affineCoverage g
  ext i
  let σ := (TrioCalculation.standardAffineHom g).1
  let A := Matrix.SpecialLinearGroup.toLin' (TrioCalculation.standardAffineHom g).2
  let e : Vector ≃ Vector := A.toEquiv.trans (Equiv.addRight (t (σ.symm i)))
  change (∑ w : Vector, v.val (g.val.val.symm (point (i,w)))) =
    ∑ w : Vector, v.val (point (σ.symm i,w))
  rw [← Equiv.sum_comp e (fun w => v.val (g.val.val.symm (point (i,w))))]
  apply Finset.sum_congr rfl
  intro w _
  have hh := ht (σ.symm i) w
  change g.val.val (point (σ.symm i,w)) = point (σ (σ.symm i), e w) at hh
  rw [σ.apply_symm_apply] at hh
  rw [← hh, Equiv.symm_apply_apply]

lemma parityEquiv_equivariant (g : trioStabilizer standardTrio)
    (v : Cocode ⧸ trioPairSpace standardTrio) :
    parityEquiv (trioTopRepresentation standardTrio g v) =
      BinaryPermutation.coreRepresentation (Fin 3)
        (TrioCalculation.standardAffineHom g).1 (parityEquiv v) := by
  induction v using Submodule.Quotient.induction_on with | _ v =>
  induction v using Submodule.Quotient.induction_on with | _ v =>
  exact parityCore_equivariant g v

lemma two_action_injective :
    Function.Injective (BinaryPermutation.coreRepresentation (Fin 3)).asGroupHom := by
  intro σ τ he
  have hh : ∀ v : Two, BinaryPermutation.coreRepresentation (Fin 3) σ v =
      BinaryPermutation.coreRepresentation (Fin 3) τ v :=
    fun v => congrArg (fun f : (Two →ₗ[ZMod 2] Two)ˣ => f.val v) he
  apply (show ∀ σ τ : Equiv.Perm (Fin 3),
    (∀ v : Fin 3 → ZMod 2, ∑ i, v i = 0 →
      ∀ i, v (σ.symm i) = v (τ.symm i)) → σ = τ by decide +kernel) σ τ
  intro v hv i
  exact congrArg (fun w : Two => w.val i) (hh ⟨v,hv⟩)

lemma two_action_surjective :
    Function.Surjective (BinaryPermutation.coreRepresentation (Fin 3)).asGroupHom := by
  let : Finite (Two →ₗ[ZMod 2] Two) :=
    Finite.of_injective (fun f : Two →ₗ[ZMod 2] Two => (f : Two → Two)) DFunLike.coe_injective
  let : Finite (Two →ₗ[ZMod 2] Two)ˣ := Finite.of_injective Units.val Units.val_injective
  apply (two_action_injective.bijective_of_nat_card_le ?_).2
  let b : Module.Basis (Fin 2) (ZMod 2) Two :=
    Module.finBasisOfFinrankEq (ZMod 2) Two (by simp [Two, BinaryPermutation.finrank_core])
  rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv, Matrix.card_GL_field]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, ZMod.card, Fin.prod_univ_succ]

/-- The native standard stabilizer induces every linear automorphism of its top quotient. -/
lemma standard_surjective : Function.Surjective
    (trioTopRepresentation standardTrio).asGroupHom := by
  intro f
  let E := LinearMap.GeneralLinearGroup.congrLinearEquiv parityEquiv
  obtain ⟨σ,hσ⟩ := two_action_surjective (E f)
  obtain ⟨g,hg⟩ := TrioCalculation.standardAffineHom_surjective (σ,1)
  refine ⟨g, E.injective ?_⟩
  rw [← hσ]
  apply Units.ext
  apply LinearMap.ext
  intro w
  change parityEquiv (trioTopRepresentation standardTrio g (parityEquiv.symm w)) =
    BinaryPermutation.coreRepresentation (Fin 3) σ w
  rw [parityEquiv_equivariant, hg, LinearEquiv.apply_symm_apply]

end
end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.TrioTop

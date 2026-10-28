module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Affine
public import Theory.Representation.Quotient
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility
public import Theory.Representation.BinaryPermutation.ThreeTensor

/-!
# Irreducibility of the standard trio tensor target

The even core on three letters turns a tensor into a pair of three-vectors.
The two transpositions swap the pair and add the second coordinate to the
first. Thus every nonzero invariant subspace contains a nonzero vector in
the first summand. Irreducibility of the literal natural SL₃(2) action fills
that summand, and a swap fills the other. Pullback along the proved native
affine quotient preserves irreducibility. No natural/dual identification or
cocode section calculation enters this argument.

Source: the middle chief factor in Aschbacher–Smith H.15.6(1,3), printed
p.401; the concrete quotient factors are those of H.14.1(3), printed p.396.
-/

public section

open scoped TensorProduct
open Representation
open BinaryPermutation
namespace MathieuCode.TrioCalculation.TensorIrreducibility
private abbrev F := ZMod 2
private abbrev G := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
private abbrev P := Equiv.Perm (Fin 3)
private abbrev V := BinaryLinearThree.Vector
private abbrev W := BinaryLinearThree.W
private abbrev C := BinaryPermutation.core (Fin 3)
private abbrev T := V ⊗[F] C

private lemma core_swap02 (n : C) :
    BinaryPermutation.coreRepresentation (Fin 3) (Equiv.swap 0 2) n =
      ⟨![n.val 2, n.val 1, n.val 0], by
        rw [BinaryPermutation.mem_core]
        have hn := n.property
        rw [BinaryPermutation.mem_core] at hn
        rw [Fin.sum_univ_three] at hn
        simp only [Fin.sum_univ_three, Matrix.cons_val_zero]
        simpa [add_comm, add_left_comm, add_assoc] using hn⟩ := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [BinaryPermutation.coreRepresentation,
    BinaryPermutation.representation_apply, Equiv.swap_apply_def]

private lemma core_swap01 (n : C) :
    BinaryPermutation.coreRepresentation (Fin 3) (Equiv.swap 0 1) n =
      ⟨![n.val 1, n.val 0, n.val 2], by
        rw [BinaryPermutation.mem_core]
        have hn := n.property
        rw [BinaryPermutation.mem_core] at hn
        rw [Fin.sum_univ_three] at hn
        simp only [Fin.sum_univ_three, Matrix.cons_val_zero]
        simpa [add_comm, add_left_comm, add_assoc] using hn⟩ := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [BinaryPermutation.coreRepresentation,
    BinaryPermutation.representation_apply, Equiv.swap_apply_def]

private lemma pairEquiv_swap02 (x : T) :
    BinaryPermutation.ThreeTensor.pairEquiv (V := V)
      (BinaryPermutation.ThreeTensor.action W (1, Equiv.swap 0 2) x) =
      ((x |> BinaryPermutation.ThreeTensor.pairEquiv).1 +
          (x |> BinaryPermutation.ThreeTensor.pairEquiv).2,
      (x |> BinaryPermutation.ThreeTensor.pairEquiv).2) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      apply Prod.ext <;> simp
  | tmul v n =>
      rw [BinaryPermutation.ThreeTensor.action_tmul,
        BinaryPermutation.ThreeTensor.pairEquiv_tmul]
      rw [core_swap02]
      simp [BinaryPermutation.ThreeTensor.pairEquiv_tmul]
      have hn := n.property
      rw [BinaryPermutation.mem_core] at hn
      rw [Fin.sum_univ_three] at hn
      have he : n.val 2 = n.val 0 + n.val 1 := by
        have hz : n.val 2 + (n.val 0 + n.val 1) = 0 := by
          simpa [add_assoc, add_comm, add_left_comm] using hn
        have hz' := (add_eq_zero_iff_eq_neg.mp hz)
        simpa [add_comm] using hz'
      rw [he]
      simp [add_smul]
  | add x y hx hy =>
      rw [map_add]
      have hp := (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).map_add x y
      have hpa := (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).map_add
        ((BinaryPermutation.ThreeTensor.action W (1, Equiv.swap 0 2)) x)
        ((BinaryPermutation.ThreeTensor.action W (1, Equiv.swap 0 2)) y)
      rw [hpa, hp, hx, hy]
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add]; abel

private lemma pairEquiv_swap01 (x : T) :
    BinaryPermutation.ThreeTensor.pairEquiv (V := V)
      (BinaryPermutation.ThreeTensor.action W (1, Equiv.swap 0 1) x) =
      ((x |> BinaryPermutation.ThreeTensor.pairEquiv).2,
      (x |> BinaryPermutation.ThreeTensor.pairEquiv).1) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      apply Prod.ext <;> simp
  | tmul v n =>
      rw [BinaryPermutation.ThreeTensor.action_tmul,
        BinaryPermutation.ThreeTensor.pairEquiv_tmul]
      rw [core_swap01]
      simp [BinaryPermutation.ThreeTensor.pairEquiv_tmul]
  | add x y hx hy =>
      rw [map_add]
      have hp := (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).map_add x y
      have hpa := (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).map_add
        ((BinaryPermutation.ThreeTensor.action W (1, Equiv.swap 0 1)) x)
        ((BinaryPermutation.ThreeTensor.action W (1, Equiv.swap 0 1)) y)
      rw [hpa, hp, hx, hy]
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add]

end MathieuCode.TrioCalculation.TensorIrreducibility
namespace MathieuCode.TrioCalculation.TensorIrreducibility
open BinaryPermutation.ThreeTensor

private noncomputable def firstSubrep : Subrepresentation (BinaryPermutation.ThreeTensor.action W) → Subrepresentation W := fun S =>
  { toSubmodule := S.toSubmodule.comap
      ((BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm.toLinearMap.comp
        (LinearMap.inl F V V))
    apply_mem_toSubmodule := by
      intro g v hv
      change (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (W g v, 0) ∈ S
      have hmem : (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (v, 0) ∈ S := hv
      have hstable := S.apply_mem_toSubmodule (g, 1) hmem
      have he := BinaryPermutation.ThreeTensor.pairEquiv_equivariant W g
        ((BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (v, 0))
      have he' : BinaryPermutation.ThreeTensor.pairEquiv (V := V)
          (BinaryPermutation.ThreeTensor.action W (g, 1)
            ((BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (v, 0))) =
          (W g v, 0) := by
        rw [he]
        simp
      have hvect : BinaryPermutation.ThreeTensor.action W (g, 1)
            ((BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (v, 0)) =
          (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (W g v, 0) := by
        apply (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).injective
        simpa using he'
      rw [← hvect]
      exact hstable }

private lemma action_irreducible : Representation.IsIrreducible (BinaryPermutation.ThreeTensor.action W) := by
  let : Representation.IsIrreducible W := BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  constructor
  · refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    let z := (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm ((![1,0,0] : V), 0)
    have hz : z ≠ 0 := by
      intro hz0
      have := congrArg (BinaryPermutation.ThreeTensor.pairEquiv (V := V)) hz0
      simp [z] at this
    apply hz
    have hsub := congrArg Subrepresentation.toSubmodule h
    have hztop : z ∈ (⊤ : Subrepresentation (BinaryPermutation.ThreeTensor.action W)).toSubmodule := by
      trivial
    have hzmem : z ∈ (⊥ : Subrepresentation (BinaryPermutation.ThreeTensor.action W)).toSubmodule :=
      hsub.symm ▸ hztop
    exact (Submodule.mem_bot F).mp hzmem
  · intro S
    by_cases hS : S = ⊥
    · exact Or.inl hS
    · right
      have hSsub : S.toSubmodule ≠ ⊥ := by
        intro hbot
        exact hS (Subrepresentation.ext hbot)
      obtain ⟨x, hxS, hx0⟩ := (Submodule.ne_bot_iff S.toSubmodule).mp hSsub
      let p := BinaryPermutation.ThreeTensor.pairEquiv (V := V) x
      have hp0 : p ≠ (0,0) := by
        intro h
        apply hx0
        apply (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).injective
        calc
          (BinaryPermutation.ThreeTensor.pairEquiv (V := V)) x = (0,0) := by simpa [p] using h
          _ = (BinaryPermutation.ThreeTensor.pairEquiv (V := V)) 0 := by simp
      let A := firstSubrep S
      have hAne : A.toSubmodule ≠ ⊥ := by
        by_cases hv : p.2 ≠ 0
        · apply (Submodule.ne_bot_iff A.toSubmodule).mpr ⟨p.2, ?_, hv⟩
          change (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (p.2, 0) ∈ S
          have hs := S.apply_mem_toSubmodule (1, Equiv.swap 0 2) hxS
          have he := pairEquiv_swap02 x
          have he' := (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).map_sub
            (BinaryPermutation.ThreeTensor.action W (1, Equiv.swap 0 2) x) x
          have hcoord : (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm
              (p.2, 0) = BinaryPermutation.ThreeTensor.action W (1, Equiv.swap 0 2) x - x := by
            apply (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).injective
            simp only [LinearEquiv.apply_symm_apply]
            calc
              (p.2, 0) = (BinaryPermutation.ThreeTensor.pairEquiv (V := V))
                  (BinaryPermutation.ThreeTensor.action W (1, Equiv.swap 0 2) x) -
                    (BinaryPermutation.ThreeTensor.pairEquiv (V := V)) x := by
                rw [he]
                dsimp [p]
                apply Prod.ext <;>
                  simp [sub_eq_add_neg, add_assoc]
              _ = (BinaryPermutation.ThreeTensor.pairEquiv (V := V))
                  (BinaryPermutation.ThreeTensor.action W (1, Equiv.swap 0 2) x - x) := he'.symm
          rw [hcoord]
          exact S.toSubmodule.sub_mem hs hxS
        · have hv0 : p.2 = 0 := by simpa using not_ne_iff.mp hv
          have hu : p.1 ≠ 0 := by
            intro hu
            apply hp0
            exact Prod.ext hu hv0
          apply (Submodule.ne_bot_iff A.toSubmodule).mpr ⟨p.1, ?_, hu⟩
          change (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (p.1, 0) ∈ S
          rw [show (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (p.1, 0) = x by
            apply (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).injective
            simp only [LinearEquiv.apply_symm_apply]
            change (p.1, 0) = p
            exact Prod.ext rfl hv0.symm]
          exact hxS
      let : Representation.IsIrreducible W := BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
      have hAne' : A ≠ ⊥ := by
        intro hbot
        apply hAne
        exact congrArg Subrepresentation.toSubmodule hbot
      have hAtop : A = ⊤ := (inferInstance : Representation.IsIrreducible W).eq_bot_or_eq_top A
        |>.resolve_left hAne'
      apply top_unique
      intro y hy
      let q := BinaryPermutation.ThreeTensor.pairEquiv (V := V) y
      have hfirst (w : V) : (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (w, 0) ∈ S := by
        have hm : w ∈ A := by rw [hAtop]; trivial
        exact hm
      have hsecond : (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (0, q.2) ∈ S := by
        have hs := S.apply_mem_toSubmodule (1, Equiv.swap 0 1) (hfirst q.2)
        have he := pairEquiv_swap01 ((BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (q.2, 0))
        have hcoord : BinaryPermutation.ThreeTensor.action W (1, Equiv.swap 0 1)
              ((BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (q.2, 0)) =
            (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (0, q.2) := by
          apply (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).injective
          rw [he]
          simp
        rw [← hcoord]
        exact hs
      have hsum := S.toSubmodule.add_mem (hfirst q.1) hsecond
      have hyEq : (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (q.1, 0) +
          (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).symm (0, q.2) = y := by
        apply (BinaryPermutation.ThreeTensor.pairEquiv (V := V)).injective
        simp [q]
      rw [hyEq] at hsum
      exact hsum

noncomputable section
open MathieuCode.TrioCalculation
private abbrev QModel := Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction.QuotientModel
private noncomputable def prodCommQ : (G × P) ≃* QModel := MulEquiv.prodComm
private lemma action_eq : quotientTensorRepresentation.comp prodCommQ.toMonoidHom =
    BinaryPermutation.ThreeTensor.action W := by
  ext g v
  rfl
private lemma quotient_irreducible : Representation.IsIrreducible quotientTensorRepresentation := by
  apply (Representation.irreducible_comp_surjective_iff prodCommQ.toMonoidHom
    prodCommQ.surjective quotientTensorRepresentation).mp
  rw [action_eq]
  exact action_irreducible
private lemma standard_irreducible : Representation.IsIrreducible standardTensorRepresentation :=
  (Representation.irreducible_comp_surjective_iff standardAffineHom
    standardAffineHom_surjective quotientTensorRepresentation).mpr quotient_irreducible
end
end MathieuCode.TrioCalculation.TensorIrreducibility

namespace MathieuCode.TrioCalculation

/-- The actual natural three-space tensor the even three-letter core is simple. -/
theorem quotientTensorRepresentation_irreducible :
    Representation.IsIrreducible quotientTensorRepresentation :=
  TensorIrreducibility.quotient_irreducible

/-- Irreducibility after pullback along the actual standard affine quotient. -/
theorem standardTensorRepresentation_irreducible :
    Representation.IsIrreducible standardTensorRepresentation :=
  TensorIrreducibility.standard_irreducible

end MathieuCode.TrioCalculation

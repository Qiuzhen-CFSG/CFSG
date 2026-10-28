module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.AlternatingCopies
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Source523

/-!
# Restricting the source A₅ sum on the whole reduced layer

The rank-one source alternative gives a marked sum of at most two copies
on the moved part of the whole R₂(KT). Every original chosen Irr⁺ subgroup
lies in that moved layer because U = [U,K]. The coordinate restriction
therefore identifies U itself with one natural A₅ module.

The source's five-letter core coordinates are transferred to the natural
coordinates using the actual equivariant odd-degree equivalence. This
supplies the original module required in 13.3.2(3), without first assuming
T-invariance or reducedness of U. The earlier global theorems 5.2.3 and
6.2.19 still have to supply the marked sum; this is their restriction step,
not an unconditional proof of AlternatingFiveModules1332.
Source: Aschbacher--Smith, 5.2.3(1), 12.2.2(3d), and 13.3.2(3),
printed pp.649,795,885. The exceptional module alternative in 5.2.3 is retained.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource
open Chapter12.Section02
open Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
variable {G : Type*} [Group G] {T : Sylow 2 G} {K U W : Subgroup G}

/-- Restrict the literal source module-sum coordinates to an original chosen module. -/
theorem chosen_model_of_source_sum (D : ChosenModule T K U) (hUW : U ≤ W)
    (hW : Source523.A5ModuleSum K W) :
    Chapter6.Source.IsConjugationModel K U Chapter6.Source.a5Module := by
  obtain ⟨c, _, e, f, hf, hr, ha⟩ := hW
  let N := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let P := (LinearEquiv.piCongrRight (fun _ : Fin c => N.symm)).toAddEquiv.toMultiplicative
  let j := f.comp P.toMonoidHom
  apply D.a5_model_of_embedded_copies e j (hf.comp P.injective)
  · intro u hu
    obtain ⟨v, hv⟩ := hr ▸ hUW hu
    exact ⟨P.symm v, by change f (P (P.symm v)) = u; rwa [P.apply_symm_apply]⟩
  · intro k v
    have he : P (Multiplicative.ofAdd (fun i => Chapter6.Source.a5Module
        (e (QuotientGroup.mk' (pCore 2 K) k)) (v i))) =
        Multiplicative.ofAdd (fun i => BinaryPermutation.coreRepresentation (Fin 5)
          (e (QuotientGroup.mk' (pCore 2 K) k)).val ((P (Multiplicative.ofAdd v)).toAdd i)) := by
      apply Multiplicative.toAdd.injective
      funext i
      apply N.injective
      change N (N.symm (Chapter6.Source.a5Module _ (v i))) =
        N (BinaryPermutation.coreRepresentation (Fin 5)
          (e (QuotientGroup.mk' (pCore 2 K) k)).val (N.symm (v i)))
      rw [N.apply_symm_apply, BinaryPermutation.coreEquivNatural_equivariant,
        N.apply_symm_apply]
      rfl
    change f (P _) = (k : G) * f (P _) * (k : G)⁻¹
    rw [he]
    exact (ha k (P (Multiplicative.ofAdd v)).toAdd).symm

/-- The earlier rank-one theorem may act on the whole reduced subgroup;
its module conclusion restricts to the original choice without assuming
that choice is already T-invariant. -/
theorem chosen_model_of_reduced_layer_sum (D : ChosenModule T K U)
    (hW : Source523.A5ModuleSum K
      ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map (K ⊔ (T : Subgroup G)).subtype, K⁆) :
    Chapter6.Source.IsConjugationModel K U Chapter6.Source.a5Module := by
  apply chosen_model_of_source_sum D _ hW
  rw [D.eq_commutator]
  exact commutator_mono D.le_reduced le_rfl

end CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource

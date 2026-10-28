module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.ModelCases
public import Theory.Alternating.Aut


/-!
# Orthogonal coordinates in the original alternating-group marking

Every automorphism of A₈ is induced by a permutation of its eight points.
Comparing a classifier's component isomorphism with the original star marking
therefore gives a permutation whose action on the deleted permutation module
intertwines the two representations. Composing the quotient projection with
this linear automorphism preserves surjectivity and its exact fixed-space
kernel. The result is the published orthogonal cover with the original marking.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(1)(i)
and 15.3.32(1), printed pp.99 and 1132; the automorphism theorem is
GLS3, Theorem 5.2.1, proved in `Theory.Alternating.Aut`.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

private noncomputable def naturalActionEquiv (a : Equiv.Perm (Fin 8)) :
    BinaryPermutation.natural (Fin 8) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8) :=
  LinearEquiv.ofLinearMap (BinaryPermutation.naturalRepresentation (Fin 8) a)
    (BinaryPermutation.naturalRepresentation (Fin 8) a⁻¹)
    (by change BinaryPermutation.naturalRepresentation (Fin 8) a *
          BinaryPermutation.naturalRepresentation (Fin 8) a⁻¹ = _
        rw [← map_mul, mul_inv_cancel, map_one]; rfl)
    (by change BinaryPermutation.naturalRepresentation (Fin 8) a⁻¹ *
          BinaryPermutation.naturalRepresentation (Fin 8) a = _
        rw [← map_mul, inv_mul_cancel, map_one]; rfl)

/-- Any orthogonal quotient can be expressed in the original star marking. -/
noncomputable def OrthogonalQuotient.markedCover {ρ : Representation (ZMod 2) K V}
    {L : Subgroup K} (h : OrthogonalQuotient ρ L)
    (e : K ≃* Equiv.Perm (Fin 8))
    (he : L.map e.toMonoidHom = alternatingGroup (Fin 8))
    (hfull : Representation.Coinvariants.ker (ρ.comp L.subtype) = ⊤) :
    Models.OrthogonalCover ρ L e := by
  let m : L ≃* alternatingGroup (Fin 8) :=
    (e.subgroupMap L).trans (MulEquiv.subgroupCongr he)
  have hex := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    8 (by decide) (by decide)).surjective (h.model.symm.trans m)
  let a := Classical.choose hex
  have ha := Classical.choose_spec hex
  have hm (l : L) : e l = a * (h.model l).val * a⁻¹ := by
    have hh := congrArg (fun f : MulAut (alternatingGroup (Fin 8)) => (f (h.model l)).val) ha
    change a * (h.model l).val * a⁻¹ = e (h.model.symm (h.model l)) at hh
    simpa only [MulEquiv.symm_apply_apply] using hh.symm
  refine {
    projection := (naturalActionEquiv a).toLinearMap.comp h.projection
    onto := (naturalActionEquiv a).surjective.comp h.projection_surjective
    equivariant := ?_
    kernel := (LinearEquiv.ker_comp _ _).trans h.projection_ker
    generated := hfull }
  intro l v
  change BinaryPermutation.naturalRepresentation (Fin 8) a
    (h.coordinates ((fixedSpace ρ L).mkQ (ρ l v))) =
    BinaryPermutation.naturalRepresentation (Fin 8) (e l)
      (BinaryPermutation.naturalRepresentation (Fin 8) a
        (h.coordinates ((fixedSpace ρ L).mkQ v)))
  rw [h.equivariant, hm, map_mul, map_mul]
  change _ = BinaryPermutation.naturalRepresentation (Fin 8) a
    (BinaryPermutation.naturalRepresentation (Fin 8) (h.model l).val
      (BinaryPermutation.naturalRepresentation (Fin 8) a⁻¹
        (BinaryPermutation.naturalRepresentation (Fin 8) a
          (h.coordinates ((fixedSpace ρ L).mkQ v)))))
  congr 2
  have hi := congrArg (fun f : Module.End (ZMod 2) (BinaryPermutation.natural (Fin 8)) =>
    f (h.coordinates ((fixedSpace ρ L).mkQ v)))
    ((BinaryPermutation.naturalRepresentation (Fin 8)).map_mul a⁻¹ a).symm
  simpa only [inv_mul_cancel, map_one, Module.End.one_apply, Module.End.mul_apply] using hi.symm
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization

end

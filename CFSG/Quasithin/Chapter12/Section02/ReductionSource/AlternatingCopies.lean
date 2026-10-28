module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenSimpleAction
public import Theory.Representation.BinaryOffender.IrreducibleSection.Copies
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.NormalInvariants

/-!
# Restricting an alternating-five module sum to an original choice

A chosen Irr⁺ module inside a sum of natural A₅ modules is itself one natural
module. Pull back the actual subgroup inclusion to a linear embedding, then
use a nonzero coordinate projection. Irreducibility makes it surjective;
the Irr⁺ condition and absence of fixed vectors make it injective. The final
conjugation model uses the same original L/O₂(L) marking.

This permits the earlier rank-one reduction to be applied to the whole
reduced subgroup R₂(LT), whose reducedness is known before choosing V.
No T-invariance or reducedness of the chosen V is assumed to perform the
restriction. The earlier global rank-one alternatives remain to be proved.
Source: Aschbacher--Smith, 12.2.2(3d), printed p.795, using the module
conclusion of 5.2.3/6.2.20 and A.1.40.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem a5_fixed_eq_zero (v : BinaryPermutation.natural (Fin 5))
    (hv : ∀ a, Chapter6.Source.a5Module a v = v) : v = 0 := by
  let ρ := Chapter6.Source.a5Module
  let : IsIrreducible ρ := BinaryPermutation.alternatingNatural_isIrreducible (by decide)
  have hf : Function.Injective ρ :=
    (BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide)).comp
      (alternatingGroup (Fin 5)).subtype_injective
  have hz : invariants (ρ.comp (⊤ : Subgroup (alternatingGroup (Fin 5))).subtype) = ⊥ := by
    by_contra h
    have hk := ρ.le_ker_of_normal_invariants_ne_bot ⊤ h
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    exact ha (hf ((hk (mem_top a)).trans (map_one ρ).symm))
  exact hz.le (fun a => hv a)

include D in
omit [Finite G] in
set_option backward.isDefEq.respectTransparency false in
private theorem a5_model_of_linear_copies {ι : Type*}
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (E : D.space →ₗ[ZMod 2] (ι → BinaryPermutation.natural (Fin 5)))
    (hE : Function.Injective E)
    (ha : ∀ (l : L) (v : D.space) i, E (D.chosenAction l v) i =
      Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l)) (E v i)) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  let X := L.subgroupOf (L ⊔ (T : Subgroup G))
  let a : X →* alternatingGroup (Fin 5) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 L)).comp
      (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
  have haS : Function.Surjective a := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (subgroupOfEquivOfLe le_sup_left).surjective)
  have hact (x : X) (v : D.space) i :
      E ((invariantSubspace _ X D.space D.irrPlus.isIrrPlus.choose).toRepresentation x v) i =
        Chapter6.Source.a5Module (a x) (E v i) :=
    ha ((subgroupOfEquivOfLe le_sup_left) x) v i
  obtain ⟨F, hF⟩ := D.irrPlus.isIrrPlus.linearEquiv_of_embedding_copies
    (reducedRepresentation (L ⊔ (T : Subgroup G))) Chapter6.Source.a5Module
    (BinaryPermutation.alternatingNatural_isIrreducible (by decide))
    a5_fixed_eq_zero a haS E hE hact
  refine ⟨e, D.spaceEquiv.symm.trans F.toAddEquiv.toMultiplicative, ?_⟩
  intro l v
  let x : X := (subgroupOfEquivOfLe
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm l
  let v' : D.space := (D.spaceEquiv.symm v).toAdd
  have h := hF x v'
  have hh : a x = e (QuotientGroup.mk' (pCore 2 L) l) := by
    change e (QuotientGroup.mk' (pCore 2 L) ((subgroupOfEquivOfLe le_sup_left)
      ((subgroupOfEquivOfLe le_sup_left).symm l))) = _
    rw [MulEquiv.apply_symm_apply]
  rw [hh] at h
  change (D.spaceEquiv (Multiplicative.ofAdd
    (F.symm (Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l))
      (F v')))) : G) = _
  rw [← h, F.symm_apply_apply, D.spaceEquiv_apply]
  have hv : (v'.val.toMul.val : G) = (v : G) :=
    (D.spaceEquiv_apply v').symm.trans
      (congrArg (fun w : V => (w : G)) (D.spaceEquiv.apply_symm_apply v))
  change (l : G) * (v'.val.toMul.val : G) * (l : G)⁻¹ = _
  rw [hv]

include D in
omit [Finite G] in
set_option backward.isDefEq.respectTransparency false in
/-- Any original choice contained in an equivariantly embedded sum of natural
A₅ modules is one natural copy, with the original quotient marking. -/
theorem a5_model_of_embedded_copies {ι : Type*}
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (f : Multiplicative (ι → BinaryPermutation.natural (Fin 5)) →* G)
    (hf : Function.Injective f) (hV : V ≤ f.range)
    (ha : ∀ (l : L) (v : ι → BinaryPermutation.natural (Fin 5)),
      f (Multiplicative.ofAdd (fun i => Chapter6.Source.a5Module
        (e (QuotientGroup.mk' (pCore 2 L) l)) (v i))) =
        (l : G) * f (Multiplicative.ofAdd v) * (l : G)⁻¹) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  let j : Multiplicative D.space →* Multiplicative (ι → BinaryPermutation.natural (Fin 5)) :=
    (MonoidHom.ofInjective hf).symm.toMonoidHom.comp
      ((inclusion hV).comp D.spaceEquiv.toMonoidHom)
  let eA : D.space →+ (ι → BinaryPermutation.natural (Fin 5)) := {
    toFun v := (j (Multiplicative.ofAdd v)).toAdd
    map_zero' := j.map_one
    map_add' v w := j.map_mul (Multiplicative.ofAdd v) (Multiplicative.ofAdd w) }
  let E : D.space →ₗ[ZMod 2] (ι → BinaryPermutation.natural (Fin 5)) :=
    { eA with map_smul' := ZMod.map_smul eA }
  have hE : Function.Injective E :=
    (MonoidHom.ofInjective hf).symm.injective.comp
      ((inclusion_injective hV).comp D.spaceEquiv.injective)
  have hfE (v : D.space) : f (Multiplicative.ofAdd (E v)) =
      (D.spaceEquiv (Multiplicative.ofAdd v) : G) :=
    MonoidHom.apply_ofInjective_symm hf _
  apply D.a5_model_of_linear_copies e E hE
  intro l v i
  apply congrFun (a := i)
  apply Multiplicative.ofAdd.injective
  apply hf
  have hc : (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l v)) : G) =
      (l : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (l : G)⁻¹ := by
    rw [D.spaceEquiv_apply, D.spaceEquiv_apply]
    rfl
  calc
    f (Multiplicative.ofAdd (E (D.chosenAction l v))) =
        (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l v)) : G) := hfE _
    _ = (l : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (l : G)⁻¹ := hc
    _ = (l : G) * f (Multiplicative.ofAdd (E v)) * (l : G)⁻¹ := by rw [hfE]
    _ = _ := (ha l (E v)).symm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

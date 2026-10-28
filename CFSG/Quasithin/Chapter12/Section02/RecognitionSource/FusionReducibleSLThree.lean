module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Irreducibility
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionSLThree
public import Theory.Representation.BinaryFullLinearRecognition
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Recovering the natural quotient in reducible row (b)

The literal fixed space in a four-dimensional chosen SL₃(2) module is
nonzero. Its quotient has dimension at most three and is faithful by
simplicity. The order 168 cannot embed in the endomorphism algebra of a
binary space of dimension at most two, so the quotient has dimension three.
Full binary linear recognition then gives natural coordinates, allowing
an automorphism of the actor as required for the natural/dual alternatives.

Transport through the original chosen-space inclusion constructs every
field of SLThreeExtension on V. The existing off-fixed-line fusion theorem
therefore proves global TI in source row (b), without an extra natural
marking, orbit assertion or Sylow-centralizer premise.

Source: Aschbacher–Smith, 12.2.2(3b) and 12.2.16, pp.795,799–800,
using the natural-extension calculation B.4.8(2), p.91.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal central quotient in reducible row (b) has dimension three. -/
theorem slThree_centralQuotient_finrank (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hd : Module.finrank (ZMod 2) D.space = 4)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    Module.finrank (ZMod 2) D.chosenCentralQuotient = 3 := by
  let C := (fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype
  have hC : C ≠ ⊥ := by
    obtain ⟨z,hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hz := z.property
    have hz1 : (z : G) ≠ 1 := fun he => hzne (Subtype.ext he)
    let v := (D.spaceEquiv.symm ⟨z,hz.1⟩).toAdd
    have hv : (v.val.toMul.val : G) = z :=
      (D.spaceEquiv_apply v).symm.trans
        (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply ⟨z,hz.1⟩))
    have hvC : v ∈ C := by
      intro l
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      change (l.val.val : G) * (v.val.toMul.val : G) * (l.val.val : G)⁻¹ = (v.val.toMul.val : G)
      rw [hv]
      exact mul_inv_eq_iff_eq_mul.mpr (hz.2 _ l.property)
    intro he
    have hv0 : v = 0 := (Submodule.mem_bot (R := ZMod 2)).mp (he ▸ hvC)
    exact hz1 (hv.symm.trans (congrArg (fun w : D.space => (w.val.toMul.val : G)) hv0))
  have hpos : 0 < Module.finrank (ZMod 2) C :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hC)
  have hsum := C.finrank_quotient_add_finrank
  rw [hd] at hsum
  have hup : Module.finrank (ZMod 2) D.chosenCentralQuotient ≤ 3 := by
    change Module.finrank (ZMod 2) (D.space ⧸ C) ≤ 3
    omega
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)).symm.isSimpleGroup
  have hf := D.centralQuotientAction_injective e.isSimpleGroup
  let : Finite D.chosenCentralQuotient := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) D.chosenCentralQuotient) :=
    Finite.of_injective (fun f => (f : D.chosenCentralQuotient → D.chosenCentralQuotient)) DFunLike.coe_injective
  have hc := Nat.card_le_card_of_injective D.centralQuotientAction hf
  rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_SL,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Module.finrank_linearMap] at hc
  interval_cases hh : Module.finrank (ZMod 2) D.chosenCentralQuotient <;> norm_num [hh] at *

open Section04.SmallFusion Representation.OneCohomology

private def chosenAdditiveEquiv (D : ChosenModule T L V) :
    letI := D.elementary
    Additive V ≃ₗ[ZMod 2] D.space := by
  letI := D.elementary
  let a : Additive V ≃+ D.space := {
    toFun := fun v => (D.spaceEquiv.symm v.toMul).toAdd
    invFun := fun w => Additive.ofMul (D.spaceEquiv (Multiplicative.ofAdd w))
    left_inv := fun v => congrArg Additive.ofMul (D.spaceEquiv.apply_symm_apply v.toMul)
    right_inv := fun w => congrArg Multiplicative.toAdd (D.spaceEquiv.symm_apply_apply _)
    map_add' := fun v w => congrArg Multiplicative.toAdd (map_mul D.spaceEquiv.symm v.toMul w.toMul) }
  exact { a with map_smul' := ZMod.map_smul a }

/-- Recover the natural quotient and its original action from the printed row (b). -/
theorem slThreeExtension_of_four_dimensional (D : ChosenModule T L V)
    (e₀ : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hd : Module.finrank (ZMod 2) D.space = 4)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) : Nonempty (SLThreeExtension D) := by
  classical
  let := D.elementary
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)).symm.isSimpleGroup
  obtain ⟨e,b,hb⟩ := BinaryFullLinearRecognition.exists_natural_equiv
    D.centralQuotientAction (D.centralQuotientAction_injective e₀.isSimpleGroup) e₀
    (slThree_centralQuotient_finrank D e₀ hd hne)
  let a := chosenAdditiveEquiv D
  let C := (fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype
  let ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (Additive V) :=
    a.symm.conjRingEquiv.toMonoidHom.comp (D.quotientAction.comp e.symm.toMonoidHom)
  have hρ (q : L ⧸ pCore 2 L) (v : Additive V) :
      ρ (e q) v = a.symm (D.quotientAction q (a v)) := by
    change a.symm (D.quotientAction (e.symm (e q)) (a v)) = _
    rw [e.symm_apply_apply]
  let p : ρ.IntertwiningMap (specialLinearNatural (k := ZMod 2) 3) :=
    (b.toLinearMap.comp (C.mkQ.comp a.toLinearMap)).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      obtain ⟨q,rfl⟩ := e.surjective g
      change b (C.mkQ (a (ρ (e q) v))) = _
      rw [hρ, a.apply_symm_apply]
      obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
      exact hb (QuotientGroup.mk' (pCore 2 L) l) (C.mkQ (a v)))
  have hC (w : D.space) : w ∈ C ↔ ∀ q, D.quotientAction q w = w := by
    constructor
    · intro hw q
      obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
      exact Subtype.ext (hw ((subgroupOfEquivOfLe
        (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm l))
    · intro hw l
      exact congrArg Subtype.val (hw (QuotientGroup.mk' (pCore 2 L) ⟨l.val.val,l.property⟩))
  refine ⟨{
    quotientEquiv := e
    action := ρ
    conjugation := ?_
    projection := p
    surjective := b.surjective.comp ((Submodule.mkQ_surjective C).comp a.surjective)
    kernel := ?_
    indecomposable := ?_ }⟩
  · intro l v
    rw [hρ]
    have hv : ((a v).val.toMul.val : G) = (v.toMul : G) :=
      (D.spaceEquiv_apply (a v)).symm.trans
        (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v.toMul))
    change (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l (a v))) : G) = _
    rw [D.spaceEquiv_apply]
    change (l : G) * ((a v).val.toMul.val : G) * (l : G)⁻¹ = _
    rw [hv]
  · ext v
    change b (C.mkQ (a v)) = 0 ↔ ∀ g, ρ g v = v
    rw [b.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hC]
    constructor
    · intro hv g
      obtain ⟨q,rfl⟩ := e.surjective g
      rw [hρ, hv q, a.symm_apply_apply]
    · intro hv q
      have hh := congrArg a (hv (e q))
      rwa [hρ, a.apply_symm_apply] at hh
  · intro A B hA hB hab
    let pull (N : Submodule (ZMod 2) (Additive V))
        (hN : ∀ g v, v ∈ N → ρ g v ∈ N) : Subrepresentation D.quotientAction := {
      toSubmodule := N.comap a.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro q w hw
        have hh := hN (e q) (a.symm w) hw
        rwa [hρ, a.apply_symm_apply] at hh }
    have hc : IsCompl (pull A hA).toSubmodule (pull B hB).toSubmodule :=
      (Submodule.orderIsoMapComap a.symm).symm.isCompl hab
    have hz (N : Submodule (ZMod 2) (Additive V))
        (hN : ∀ g v, v ∈ N → ρ g v ∈ N)
        (hh : pull N hN = ⊥) : N = ⊥ := by
      apply bot_unique
      intro v hv
      have hw : a v ∈ pull N hN := by
        change a.symm (a v) ∈ N
        rwa [a.symm_apply_apply]
      rw [hh] at hw
      have he : a v = 0 := hw
      exact a.injective (he.trans (map_zero a).symm)
    exact (D.quotientAction_indecomposable.2 _ _ hc).imp (hz A hA) (hz B hB)

open ChapterI.Section06To08

/-- Reducible source row (b) supplies global TI without an extra marking premise. -/
theorem globalTI_of_slThree_four_dimensional
    {K : GroupClass} (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hd : Module.finrank (ZMod 2) D.space = 4)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) : IsTISubgroup V := by
  obtain ⟨E⟩ := slThreeExtension_of_four_dimensional D e hd hne
  exact globalTI_of_slThree_extension h D structural hnone E hne

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

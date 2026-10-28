module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At.Module
public import Theory.Representation.PSL3Two.IrreducibleCatalogue
public import Theory.Representation.PSL3Two.SmallModuleProperties
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeNonsplit

/-!
# The natural quotient of every original L₃ choice at G,T

The seven module rows and the order 168 bound the chosen space below dimension
eight. Its faithful irreducible central quotient is therefore natural or dual
natural by H.6.1. Binary full-linear recognition supplies a compatible marking,
and transport along the original chosen-space equivalence gives SLThreeExtension
on V, including when its fixed subgroup is trivial. The subsequent naturality
application uses the independently proved fusion contradiction to remove the
kernel; this construction itself asserts no fixed-space vanishing.

Source: Aschbacher–Smith, 12.2.2(3), p.795; H.6.1, pp.385–387.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At
open Section02 Section02.RecognitionSource SmallFusion
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The original quotient marking, with the actual field transported to F₂. -/
theorem quotient_marking (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) :
    Nonempty ((L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hmodel
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hc)
  exact ⟨(e.trans (Atlas.fieldEquivPSL 3 eF)).trans Matrix.PSL3Two.equiv.symm⟩

/-- No eight-dimensional row occurs for the literal order-168 actor. -/
theorem chosen_finrank_lt_eight (D : ChosenModule T L V)
    (rows : ModuleAlternatives1222 D)
    (e₀ : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    Module.finrank (ZMod 2) D.space < 8 := by
  have hc : Nat.card (L ⧸ pCore 2 L) = 168 :=
    (Nat.card_congr e₀.toEquiv).trans Matrix.PSL3Two.card_SL
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup BinaryLinearThree.Group :=
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)).symm.isSimpleGroup
  let := D.actionCentralizer_normal
  have hfaith : Nat.card (L ⧸ (centralizer (V : Set G)).subgroupOf L) = 168 :=
    (Nat.card_congr (D.coreToFaithfulEquiv e₀.isSimpleGroup).symm.toEquiv).trans hc
  have hfive (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : False := by
    let f := (e.trans (BinaryLinear.OuterCyclic.slEquivLinear 5)).trans
      (BinaryLinear.OuterCyclic.matrixEquivLinear 5).symm
    have he := (Nat.card_congr f.toEquiv).symm.trans hc
    rw [Matrix.card_GL_field] at he
    norm_num [Fin.prod_univ_succ] at he
  have halt (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 8)
      (e : (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin n)) : False := by
    have he := (Nat.card_congr e.toEquiv).symm.trans hfaith
    interval_cases n <;>
      rw [nat_card_alternatingGroup, Nat.card_fin] at he <;>
      norm_num [Nat.factorial] at he
  cases rows with
  | linear n hn e =>
      have hd := e.linearEquiv.finrank_eq
      rw [Module.finrank_fin_fun] at hd
      omega
  | linearThreeExtension _ hd _ => omega
  | linearFiveExterior e _ _ => exact (hfive e).elim
  | alternating n hlo hhi e => exact (halt n hlo hhi e.groupEquiv).elim
  | alternatingSevenFour e _ => exact (halt 7 (by decide) (by decide) e).elim
  | g2 e =>
      have he := (Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc
      rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at he
      norm_num at he
  | tripleSix e _ _ _ =>
      have he := (Nat.card_congr e.toEquiv).symm.trans hc
      rw [Atlas.Codes.hexEven_card] at he
      norm_num at he

/-- H.6.1 identifies the faithful irreducible central quotient in dimension three. -/
theorem centralQuotient_finrank_three (D : ChosenModule T L V)
    (rows : ModuleAlternatives1222 D)
    (e₀ : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) :
    Module.finrank (ZMod 2) D.chosenCentralQuotient = 3 := by
  let ρ := D.centralQuotientAction.comp e₀.symm.toMonoidHom
  let : IsIrreducible ρ :=
    (irreducible_comp_surjective_iff _ e₀.symm.surjective _).mpr
      D.centralQuotientAction_irreducible
  have hmove : ∃ g v, ρ g v ≠ v := by
    by_contra! hh
    apply D.centralAction_ne_one
    apply MonoidHom.ext
    intro l
    apply LinearMap.ext
    intro v
    have he := hh (e₀ (QuotientGroup.mk' (pCore 2 L) l)) v
    change D.centralQuotientAction
      (e₀.symm (e₀ (QuotientGroup.mk' (pCore 2 L) l))) v = v at he
    rw [e₀.symm_apply_apply] at he
    exact he
  have hd := chosen_finrank_lt_eight D rows e₀
  have hle : Module.finrank (ZMod 2) D.chosenCentralQuotient ≤
      Module.finrank (ZMod 2) D.space := Submodule.finrank_quotient_le _
  rcases BinaryLinearThree.IrreducibleCatalogue.classify_nontrivial ρ hmove with
    he | he | he
  · obtain ⟨e⟩ := he
    exact e.toLinearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))
  · obtain ⟨e⟩ := he
    exact e.toLinearEquiv.finrank_eq.trans
      (Subspace.dual_finrank_eq.trans (Module.finrank_fin_fun (ZMod 2)))
  · obtain ⟨e⟩ := he
    have hd' := e.toLinearEquiv.finrank_eq
    rw [BinaryLinearThree.finrank_steinberg] at hd'
    omega

open Representation.OneCohomology

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

/-- Recover the natural quotient on the whole chosen V from the original rows. -/
theorem extension_of_source_rows (D : ChosenModule T L V)
    (e₀ : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (rows : ModuleAlternatives1222 D) : Nonempty (SLThreeExtension D) := by
  classical
  let := D.elementary
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)).symm.isSimpleGroup
  obtain ⟨e,b,hb⟩ := BinaryFullLinearRecognition.exists_natural_equiv
    D.centralQuotientAction (D.centralQuotientAction_injective e₀.isSimpleGroup) e₀
    (centralQuotient_finrank_three D rows e₀)
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

/-- The precise marked natural quotient from the same-G,T module producer. -/
theorem extension_of_modules
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) :
    Nonempty (SLThreeExtension D) := by
  obtain ⟨e⟩ := quotient_marking hmodel
  exact extension_of_source_rows D e (modules L V h D)

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At

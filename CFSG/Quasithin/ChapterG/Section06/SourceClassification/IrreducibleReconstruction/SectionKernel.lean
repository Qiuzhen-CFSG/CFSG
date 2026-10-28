module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.RankOneRows.LinearClosure
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.TwoFactorReconstruction.FixedKernel
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction

/-!
# Recovering the original binary linear action from its moved section

The projection here is the literal central quotient of the B.5 moved section.
A vanishing central kernel lifts its action model to the original space. For
SL3(2), three conjugate involutions bound the original moved dimension by
three. For SL4(2) and SL5(2), the proved dual cohomology calculation makes
the same kernel zero. The final applications retain the original G.6 actor
and discharge its full conclusion through the natural linear normal closure.

Source: Aschbacher–Smith, G.6.4, printed pp.345–346, and B.5.1(2), p.99.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
universe u v w z
namespace IrreducibleReconstruction
open ChapterB.QuasisimpleSource
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {L : Subgroup D}

/-- The original moved space is identified with the whole space only when
the source has proved that equality. -/
noncomputable def topSpaceEquiv (s : MovedSection ρ L)
    (hs : s.space.toSubmodule = ⊤) : V ≃ₗ[ZMod 2] s.space.toSubmodule where
  toFun v := ⟨v, hs.symm ▸ Submodule.mem_top⟩
  invFun v := v.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem central_eq_bot_of_isCompl (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L)) :
    s.central.toSubmodule = ⊥ := by
  apply bot_unique
  intro v hv
  change v = 0
  apply Subtype.ext
  apply Submodule.disjoint_def.mp hc.disjoint v v.property
  rw [s.central_eq] at hv
  intro g
  exact congrArg Subtype.val (hv g)

variable {E : Type w} [Group E] {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) E W}

/-- The action equivalence uses the actual quotient map, with its proved
zero kernel, and therefore preserves the source's group marking. -/
noncomputable def liftTopModel (s : MovedSection ρ L)
    (hs : s.space.toSubmodule = ⊤) (hc : s.central.toSubmodule = ⊥)
    (e : ActionEquiv s.action σ) : ActionEquiv ρ σ where
  groupEquiv := e.groupEquiv
  linearEquiv := (topSpaceEquiv s hs).trans
    ((LinearEquiv.ofBijective s.central.toSubmodule.mkQ
      ⟨by rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ, hc],
        Submodule.mkQ_surjective _⟩).trans e.linearEquiv)
  intertwines g v := e.intertwines g (s.central.toSubmodule.mkQ (topSpaceEquiv s hs v))

/-- Extending an action equivalence along an equality with the full actor. -/
noncomputable def actionOfTop (hL : L = ⊤)
    (e : ActionEquiv (ρ.comp L.subtype) σ) : ActionEquiv ρ σ where
  groupEquiv := (topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)).trans e.groupEquiv
  linearEquiv := e.linearEquiv
  intertwines g v := e.intertwines ⟨g, hL.symm ▸ mem_top g⟩ v

theorem central_eq_bot_of_dimension [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L)
    (hd : Module.finrank (ZMod 2) s.space.toSubmodule ≤
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule)) :
    s.central.toSubmodule = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  have he := Submodule.finrank_quotient_add_finrank s.central.toSubmodule
  omega

end IrreducibleReconstruction

open IrreducibleReconstruction ChapterB.QuasisimpleSource
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.conclusion_of_linearThree_section
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (s : MovedSection (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (Theory.GroupTheory.generalizedFitting (normalClosure ({a} : Set G))))
    (hs : s.space.toSubmodule = ⊤)
    (e : ActionEquiv s.action (linearNatural BinaryField.two 3)) : Conclusion ρ a := by
  let := h.finite_module
  let K := normalClosure ({a} : Set G)
  let t : K := ⟨a, subset_normalClosure (Set.mem_singleton a)⟩
  have hb := SmallNaturalMovedDimension.linearThree (ρ.comp K.subtype) e.groupEquiv t
    (fun he => h.nonidentity (congrArg Subtype.val he))
    (show t * t = 1 from Subtype.ext (by change a * a = 1; simpa only [pow_two] using h.involution))
  rw [← subspaceCommutator_top_eq_coinvariants, lemma_G_6_2_1 ρ a h.generated] at hb
  have hd : Module.finrank (ZMod 2) s.space.toSubmodule ≤ 3 := by
    rw [hs]
    change Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) ≤ 3
    change Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) ≤
      3 * Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) at hb
    simpa only [hr, mul_one] using hb
  have he := e.linearEquiv.finrank_eq
  change Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) =
    Module.finrank (ZMod 2) (Fin 3 → ZMod 2) at he
  rw [Module.finrank_fin_fun] at he
  exact h.conclusion_of_binary_linear_normalClosure (by decide) (by decide)
    (liftTopModel s hs (central_eq_bot_of_dimension s (by omega)) e)

theorem Hypotheses.conclusion_of_binaryLinear_section
    (h : Hypotheses κ ρ a q)
    (s : MovedSection (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (Theory.GroupTheory.generalizedFitting (normalClosure ({a} : Set G))))
    (hs : s.space.toSubmodule = ⊤)
    (hi : IsIrrPlus (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (Theory.GroupTheory.generalizedFitting (normalClosure ({a} : Set G))) s.space.toSubmodule)
    (hL : Theory.GroupTheory.generalizedFitting (normalClosure ({a} : Set G)) = ⊤)
    {n : ℕ} (hn : 4 ≤ n) (hn5 : n ≤ 5)
    (e : ActionEquiv (s.action.comp
      (Theory.GroupTheory.generalizedFitting (normalClosure ({a} : Set G))).subtype)
      (linearNatural BinaryField.two n)) : Conclusion ρ a := by
  let := h.finite_group
  let := h.finite_module
  have hc := ChapterB.QuasisimpleSource.ExtensionConsequences.binaryLinear_isCompl s hi hn e
  exact h.conclusion_of_binary_linear_normalClosure (by omega) hn5
    (liftTopModel s hs (central_eq_bot_of_isCompl s hc) (actionOfTop hL e))

end CFSG.Quasithin.ChapterG.Section06

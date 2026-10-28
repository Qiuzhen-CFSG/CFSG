module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Definitions
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Irreducibility
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionTransitive
public import Theory.Representation.PSL3Two.IrreducibleCatalogue
public import Theory.Representation.G2NaturalTransitivity
public import Theory.Representation.BinaryPermutation.SixTransitivity

/-!
# The transitive and impossible fixed-free rows of 12.2.16

When C_V(L)=1, the literal quotient map V → V/C_V(L) is an
equivariant isomorphism. This supplies global TI in the natural A₆ and
derived G₂(2) rows by their proved nonzero-vector transitivity. Irr⁺ is
then irreducible on V itself; the binary SL₃ catalogue excludes the
four-dimensional indecomposable row.

All markings retain the original quotient projection and chosen V.
Source: Aschbacher--Smith 12.2.2(3b,d,f) and 12.2.16, pp.795,799--800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal central-quotient projection is an isomorphism when its kernel is trivial. -/
@[expose] def fixedFreeQuotientEquiv (D : ChosenModule T L V)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    D.space ≃ₗ[ZMod 2] D.chosenCentralQuotient := by
  let C := (fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype
  have hC : C = ⊥ := by
    have hh := D.seed_fixedSpace_eq_bot hc
    rwa [fixedSpace_restrictedSubgroup _ _ _ D.irrPlus.invariant] at hh
  exact LinearEquiv.ofBijective C.mkQ
    ⟨LinearMap.ker_eq_bot.mp ((Submodule.ker_mkQ C).trans hC),
      Submodule.mkQ_surjective C⟩

omit [Finite G] in
/-- The quotient comparison intertwines the original L-action. -/
theorem fixedFreeQuotientEquiv_action (D : ChosenModule T L V)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) (l : L) (v : D.space) :
    fixedFreeQuotientEquiv D hc (D.chosenAction l v) =
      D.chosenCentralAction l (fixedFreeQuotientEquiv D hc v) := rfl

/-- Complete natural A₆ row under C_V(L)=1. -/
theorem globalTI_of_alternating_six_fixedFree
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (a : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulCentralAction (alternatingNatural 6)) :
    IsTISubgroup V := by
  let := D.actionCentralizer_normal
  let e := (fixedFreeQuotientEquiv D hc).trans a.linearEquiv
  apply globalTI_of_chosenAction_transitive h D structural hnone
  intro v w hv hw
  obtain ⟨s,hs⟩ := BinaryPermutation.alternatingSix_natural_nonzero_transitive
    (e v) (e w) (by simpa using hv) (by simpa using hw)
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective
    ((centralizer (V : Set G)).subgroupOf L) (a.groupEquiv.symm s)
  refine ⟨l,e.injective ?_⟩
  change a.linearEquiv (fixedFreeQuotientEquiv D hc (D.chosenAction l v)) = e w
  rw [fixedFreeQuotientEquiv_action]
  change a.linearEquiv (D.faithfulCentralAction
    (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l)
    (fixedFreeQuotientEquiv D hc v)) = e w
  rw [a.intertwines,hl,a.groupEquiv.apply_symm_apply]
  exact hs

/-- Complete derived G₂(2) natural row under C_V(L)=1. -/
theorem globalTI_of_g2_fixedFree
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (a : ActionEquiv D.centralQuotientAction
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype)) :
    IsTISubgroup V := by
  let e := (fixedFreeQuotientEquiv D hc).trans a.linearEquiv
  apply globalTI_of_chosenAction_transitive h D structural hnone
  intro v w hv hw
  obtain ⟨s,hs⟩ := Atlas.G2.Natural.derivedAction_transitive
    (ZMod 2) (e v) (e w) (by simpa using hv) (by simpa using hw)
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (a.groupEquiv.symm s)
  refine ⟨l,e.injective ?_⟩
  change a.linearEquiv (fixedFreeQuotientEquiv D hc (D.chosenAction l v)) = e w
  rw [fixedFreeQuotientEquiv_action]
  change a.linearEquiv (D.centralQuotientAction (QuotientGroup.mk' (pCore 2 L) l)
    (fixedFreeQuotientEquiv D hc v)) = e w
  rw [a.intertwines,hl,a.groupEquiv.apply_symm_apply]
  exact hs

/-- Irr⁺ becomes irreducible on the original V when C_V(L)=1. -/
theorem quotientAction_irreducible_fixedFree (D : ChosenModule T L V)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    IsIrreducible D.quotientAction := by
  let : Nontrivial D.space := Submodule.nontrivial_iff_ne_bot.mpr
    (D.irrPlus.isIrrPlus.ne_bot _)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance,fun S => ?_⟩
  have hS : (⊤ : Subgroup (L ⧸ pCore 2 L)) ≤
      subspaceStabilizer D.quotientAction S.toSubmodule :=
    le_subspaceStabilizer _ _ (fun g _ v hv => S.apply_mem_toSubmodule g hv)
  rcases D.quotientAction_irrPlus.eq_or_le_fixedSpace D.quotientAction hS le_top with ht | hf
  · exact Or.inr (Subrepresentation.toSubmodule_injective ht)
  · left
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    have hh : ∀ l : L, D.chosenAction l v = v := fun l =>
      hf hv ⟨QuotientGroup.mk' (pCore 2 L) l,mem_top _⟩
    have hz : fixedFreeQuotientEquiv D hc v = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      intro l
      exact congrArg Subtype.val (hh ((subgroupOfEquivOfLe le_sup_left) l))
    exact (fixedFreeQuotientEquiv D hc).map_eq_zero_iff.mp hz

/-- The indecomposable four-space row cannot have C_V(L)=1. -/
theorem not_linear_three_four_fixedFree (D : ChosenModule T L V)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hd : Module.finrank (ZMod 2) D.space = 4) : False := by
  let : IsIrreducible D.quotientAction := quotientAction_irreducible_fixedFree D hc
  let ρ := D.quotientAction.comp e.symm.toMonoidHom
  let : IsIrreducible ρ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr inferInstance
  rcases BinaryLinearThree.IrreducibleCatalogue.classify ρ with ht | hn | hdv | hs
  · obtain ⟨a⟩ := ht
    have hh := a.toLinearEquiv.finrank_eq
    rw [hd,Module.finrank_self] at hh
    omega
  · obtain ⟨a⟩ := hn
    have hh := a.toLinearEquiv.finrank_eq
    change Module.finrank (ZMod 2) D.space = Module.finrank (ZMod 2) (Fin 3 → ZMod 2) at hh
    simp [hd] at hh
  · obtain ⟨a⟩ := hdv
    have hh := a.toLinearEquiv.finrank_eq
    change Module.finrank (ZMod 2) D.space =
      Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) at hh
    simp [hd] at hh
  · obtain ⟨a⟩ := hs
    have hh := a.toLinearEquiv.finrank_eq
    rw [hd,BinaryLinearThree.finrank_steinberg] at hh
    omega

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

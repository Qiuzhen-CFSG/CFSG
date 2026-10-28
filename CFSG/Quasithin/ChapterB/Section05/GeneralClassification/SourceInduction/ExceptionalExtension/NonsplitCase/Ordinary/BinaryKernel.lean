module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Ordinary.BinaryKernel.LowerCohomology
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Ordinary.Cohomology
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Descent
/-!
# Fixed kernels of the binary second moved module

The actual ambient commutator module D=[V,G₂] lies in V₂=C_V(G₁).
An offender on V₂ restricts to D, and perfectness makes D fully moving.
The intrinsic binary SL₃ FF bound therefore gives dim D ≤ 6. In the doubled
natural branch the literal fixed quotient already has dimension six, so its
fixed kernel is zero.

For a single natural quotient the checked dual H¹ bound gives a fixed kernel
of dimension at most one. A nonzero kernel therefore makes D a lower
four-dimensional extension. The lower-four cohomology theorem gives
vanishing H¹ on that extension, supplying an ambient fixed supplement through
the actual inclusion D≤V₂. The proper-supplement hypothesis excludes it, so
the fixed kernel vanishes in both the single and doubled natural branches.

The single branch uses only the published earlier-source input EarlierB48Four;
the doubled branch uses no earlier-source implication. No ambient offender generation is transferred
from V₂ to V.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(1),(4),
printed p.91, B.5.1(5), printed pp.99,103, and the endgame of B.5.6,
printed p.110, lines 5733–5744 of the source text.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
open ComponentReduction
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

private theorem isFF_of_embedding {D U T : Type*} [Group D]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    [AddCommGroup T] [Module (ZMod 2) T]
    (α : Representation (ZMod 2) D U) (β : Representation (ZMod 2) D T)
    (j : T →ₗ[ZMod 2] U) (hj : Function.Injective j)
    (he : ∀ g v, j (β g v) = α g (j v)) (hFF : IsFFModule α) : IsFFModule β := by
  let N : Subrepresentation α :=
    { toSubmodule := j.range
      apply_mem_toSubmodule g v hv := by
        obtain ⟨w,rfl⟩ := hv
        exact ⟨β g w,he g w⟩ }
  let e : T ≃ₗ[ZMod 2] N.toSubmodule := LinearEquiv.ofInjective j hj
  obtain ⟨A,hA,hb⟩ := hFF
  have hN : IsFFModule N.toRepresentation :=
    ⟨A,hA,(fixedCodim_subrepresentation_le α N A).trans hb⟩
  apply hN.map_equivariant N.toRepresentation β (MonoidHom.id D) Function.injective_id e.symm
  intro g v
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change (α g v : U) = j (β g (e.symm v))
  rw [he]
  exact congrArg (α g) (congrArg Subtype.val (e.apply_symm_apply v)).symm

/-- The actual ambient moving module inherits FF from V₂ by its inclusion. -/
theorem secondMoved_isFF [Finite G] {K : CFSG.Quasithin.GroupClass.{u}}
    (hyp : FFHypothesis K ρ) (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space) [Nontrivial (second c)] :
    IsFFModule ((secondMoved c).toRepresentation.comp (second c).subtype) := by
  let := hyp.finite_module
  let j : (secondMoved c).toSubmodule →ₗ[ZMod 2] c.productConfiguration.fixed.toSubmodule :=
    Submodule.inclusion (second_moved_le_fixed c he)
  have hdesc : FFHypothesis K (secondAction c) :=
    hyp.on_second ρ c.productConfiguration.product c.sectionData.space
      c.productConfiguration.fixed (first_fixed_by_second c) c.productConfiguration.fixed_eq.le
      (Or.inr (by rw [c.productConfiguration.fixed_eq]; exact he.2))
  exact isFF_of_embedding (secondAction c) _ j
    (Submodule.inclusion_injective _) (fun _ _ => rfl) (hdesc.isFFModule _)

private theorem moved_comp_subtype (H : Subgroup G) :
    moved (ρ.comp H.subtype) ⊤ = moved ρ H := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    exact Submodule.subset_span ⟨g,g.property,v,Submodule.mem_top,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    exact Submodule.subset_span ⟨⟨g,hg⟩,Subgroup.mem_top _,v,Submodule.mem_top,rfl⟩

private noncomputable def secondMovingEquiv (c : Conclusion ρ) (E : second c ≃* SL) :
    ActionEquiv
      (CentralAttachments.moving ((ρ.comp (second c).subtype).comp E.symm.toMonoidHom)).toRepresentation
      ((secondMoved c).toRepresentation.comp (second c).subtype) := by
  have hm : (CentralAttachments.moving
      ((ρ.comp (second c).subtype).comp E.symm.toMonoidHom)).toSubmodule =
      (secondMoved c).toSubmodule := by
    rw [CentralAttachments.moving_eq]
    change moved ((ρ.comp (second c).subtype).comp E.symm.toMonoidHom) ⊤ = _
    rw [moved_relabel, moved_comp_subtype]
    rfl
  exact ⟨E.symm,LinearEquiv.ofEq _ _ hm,fun _ _ => Subtype.ext rfl⟩

/-- The descended offender and actual commutator action give the six-dimensional bound. -/
theorem secondMoved_finrank_le_six [Finite G] {K : CFSG.Quasithin.GroupClass.{u}}
    (hyp : FFHypothesis K ρ) (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space) [Nontrivial (second c)]
    (E : second c ≃* SL) : Module.finrank (ZMod 2) (secondMoved c).toSubmodule ≤ 6 := by
  let := hyp.finite_module
  let e := secondMovingEquiv c E
  have hFF := secondMoved_isFF hyp c he
  have hFF' := hFF.map_equivariant _ _ e.groupEquiv.symm.toMonoidHom
    e.groupEquiv.symm.injective e.linearEquiv.symm (fun g v => by
      apply e.linearEquiv.injective
      rw [e.intertwines, e.linearEquiv.apply_symm_apply,
        e.linearEquiv.apply_symm_apply]
      simp only [MulEquiv.coe_toMonoidHom, e.groupEquiv.apply_symm_apply])
  rw [← e.linearEquiv.finrank_eq]
  exact ExtensionControl.finrank_le_six _ (CentralAttachments.moving_full _) hFF'


/-- Perfectness is used on the literal ambient commutator module. -/
theorem secondMoved_full (c : Conclusion ρ) (E : second c ≃* SL) :
    moved ((secondMoved c).toRepresentation.comp (second c).subtype) ⊤ = ⊤ := by
  let e := secondMovingEquiv c E
  have hh := subspaceCommutator_map_embedding _ _ e.groupEquiv.symm.toMonoidHom
    e.linearEquiv.toLinearMap (fun g v => by
      have h := (e.intertwines (e.groupEquiv.symm g) v).symm
      rw [e.groupEquiv.apply_symm_apply] at h
      exact h) ⊤ ⊤
  simpa only [Submodule.map_top, LinearEquiv.range,
    Subgroup.map_top_of_surjective e.groupEquiv.symm.toMonoidHom e.groupEquiv.symm.surjective,
    CentralAttachments.moving_full] using hh

private def composeAction {A B C X Y Z : Type*} [Group A] [Group B] [Group C]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    {α : Representation (ZMod 2) A X} {β : Representation (ZMod 2) B Y}
    {γ : Representation (ZMod 2) C Z}
    (e : ActionEquiv α β) (f : ActionEquiv β γ) : ActionEquiv α γ :=
  ⟨e.groupEquiv.trans f.groupEquiv, e.linearEquiv.trans f.linearEquiv,
    fun g v => (congrArg f.linearEquiv (e.intertwines g v)).trans (f.intertwines _ _)⟩

/-- The doubled natural quotient exhausts the bound, leaving no fixed kernel. -/
theorem binary_double_secondMoved_fixed_eq_bot [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hyp : FFHypothesis K ρ) (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space) [Nontrivial (second c)]
    (f : FactorModuleConclusion (secondAction c))
    (hm : f.space.toSubmodule = moved (secondAction c) ⊤)
    (hn : IsRepeatedLinearNatural (secondFactorAction c f) BinaryField.two 3 2) :
    Representation.invariants ((secondMoved c).toRepresentation.comp (second c).subtype) = ⊥ := by
  let := hyp.finite_module
  obtain ⟨n⟩ := hn
  let e := composeAction (secondMovedFactorEquiv c he f hm) n
  have hb := secondMoved_finrank_le_six hyp c he e.groupEquiv
  let τ : Representation (ZMod 2) (second c) (secondMoved c).toSubmodule :=
    (secondMoved c).toRepresentation.comp (second c).subtype
  have hd : Module.finrank (ZMod 2) ((secondMoved c).toSubmodule ⧸ τ.invariants) = 6 := by
    exact e.linearEquiv.finrank_eq.trans (by
      simp [Module.finrank_pi_fintype, BinaryField.two])
  have hr := Submodule.finrank_quotient_add_finrank τ.invariants
  change τ.invariants = ⊥
  apply Submodule.finrank_eq_zero.mp
  omega

/-- The one-copy natural quotient has at most one dimension of fixed kernel. -/
theorem binary_natural_fixed_finrank_le_one
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (τ : Representation (ZMod 2) D U)
    (hfull : moved τ ⊤ = ⊤)
    (hn : IsLinearNatural (reducedAction τ) BinaryField.two 3) :
    Module.finrank (ZMod 2) τ.invariants ≤ 1 := by
  obtain ⟨e⟩ := hn
  let E : D ≃* SL := e.groupEquiv
  let σ := τ.comp E.symm.toMonoidHom
  let p : U →ₗ[ZMod 2] (Fin 1 → Fin 3 → ZMod 2) :=
    LinearMap.pi (fun _ => e.linearEquiv.toLinearMap.comp (fixed τ).toSubmodule.mkQ)
  let q : ModuleQuotient σ 1 :=
    { marking := MulEquiv.refl SL
      projection := p
      surjective := by
        intro v
        obtain ⟨x,hx⟩ := e.linearEquiv.surjective (v 0)
        obtain ⟨w,rfl⟩ := (fixed τ).toSubmodule.mkQ_surjective x
        refine ⟨w,?_⟩
        funext i
        simpa only [p, hx, Subsingleton.elim i 0]
      kernel := by
        rw [fixedSpace_top, invariants_relabel]
        ext v
        constructor
        · intro hv
          have hz : e.linearEquiv (τ.invariants.mkQ v) = 0 := congrFun hv 0
          exact (Submodule.Quotient.mk_eq_zero _).mp (e.linearEquiv.map_eq_zero_iff.mp hz)
        · intro hv
          change (fun _ : Fin 1 => e.linearEquiv ((fixed τ).toSubmodule.mkQ v)) = 0
          rw [show (fixed τ).toSubmodule.mkQ v = 0 from
            (Submodule.Quotient.mk_eq_zero _).mpr hv, map_zero]
          rfl
      equivariant := by
        intro g v i
        have h := e.intertwines (E.symm g) ((fixed τ).toSubmodule.mkQ v)
        change e.linearEquiv ((fixed τ).toSubmodule.mkQ (τ (E.symm g) v)) =
          specialLinearNatural 3 (E (E.symm g))
            (e.linearEquiv ((fixed τ).toSubmodule.mkQ v)) at h
        rw [E.apply_symm_apply] at h
        exact h }
  have hf : subspaceCommutator σ ⊤ ⊤ = ⊤ := by
    change moved (τ.comp E.symm.toMonoidHom) ⊤ = ⊤
    rw [moved_relabel, hfull]
  have hb := oneCopy_kernel_card_le_two σ hf q
  rw [q.kernel, fixedSpace_top, invariants_relabel,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hb
  by_contra h
  have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    (show 2 ≤ Module.finrank (ZMod 2) τ.invariants by omega)
  norm_num at hh
  omega

/-- A nonzero single-natural fixed kernel forces a four-dimensional lower extension. -/
theorem binary_single_secondMoved_dimension [FiniteDimensional (ZMod 2) V]
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (hm : f.space.toSubmodule = moved (secondAction c) ⊤)
    (hn : IsLinearNatural (secondFactorAction c f) BinaryField.two 3)
    (hz : Representation.invariants
      ((secondMoved c).toRepresentation.comp (second c).subtype) ≠ ⊥) :
    Module.finrank (ZMod 2) (secondMoved c).toSubmodule = 4 := by
  obtain ⟨n⟩ := hn
  let e := composeAction (secondMovedFactorEquiv c he f hm) n
  let τ : Representation (ZMod 2) (second c) (secondMoved c).toSubmodule :=
    (secondMoved c).toRepresentation.comp (second c).subtype
  have hb := binary_natural_fixed_finrank_le_one τ (secondMoved_full c e.groupEquiv) ⟨e⟩
  have hpos : Module.finrank (ZMod 2) τ.invariants ≠ 0 :=
    fun h => hz (Submodule.finrank_eq_zero.mp h)
  have hd : Module.finrank (ZMod 2) ((secondMoved c).toSubmodule ⧸ τ.invariants) = 3 := by
    exact e.linearEquiv.finrank_eq.trans (by simp [BinaryField.two])
  have hr := Submodule.finrank_quotient_add_finrank τ.invariants
  omega

open Representation.OneCohomology
/-- H¹ vanishing on the literal moved module supplies fixed lifts in the ambient module. -/
theorem second_fixed_supplement_of_moved_H1 (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    [Subsingleton (H1 ((secondMoved c).toRepresentation.comp (second c).subtype))] :
    fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule = ⊤ := by
  let U : Subrepresentation (ρ.comp (second c).subtype) :=
    { toSubmodule := (secondMoved c).toSubmodule
      apply_mem_toSubmodule g v hv := (secondMoved c).apply_mem_toSubmodule g hv }
  let : Subsingleton (H1 U.toRepresentation) :=
    ‹Subsingleton (H1 ((secondMoved c).toRepresentation.comp (second c).subtype))›
  have ht : HasTrivialQuotient U := by
    intro g v
    exact Submodule.subset_span ⟨g,g.property,v,Submodule.mem_top,rfl⟩
  apply top_unique
  intro v _
  have hv := (extensionClass_eq_zero_iff U ht v).mp (Subsingleton.elim _ _)
  change v ∈ (secondMoved c).toSubmodule ⊔ fixedSpace ρ (second c) at hv
  exact (sup_le le_sup_left ((second_moved_le_fixed c he).trans le_sup_right))
    (show v ∈ fixedSpace ρ (second c) ⊔ (secondMoved c).toSubmodule by rwa [sup_comm])

/-- In the single-natural branch, a nonzero fixed kernel would be a lower
four-space. Its vanishing H¹ supplies the ambient fixed supplement excluded
by `hproper`. The sole earlier-source input is the published B.4.8(4). -/
theorem binary_single_secondMoved_fixed_eq_bot [Finite G] [FiniteDimensional (ZMod 2) V]
    (h48 : EarlierB48Four.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (hm : f.space.toSubmodule = moved (secondAction c) ⊤)
    (hproper : fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule ≠ ⊤)
    (hn : IsLinearNatural (secondFactorAction c f) BinaryField.two 3) :
    Representation.invariants ((secondMoved c).toRepresentation.comp (second c).subtype) = ⊥ := by
  by_contra hz
  have hdim := binary_single_secondMoved_dimension c he f hm hn hz
  obtain ⟨n⟩ := hn
  let e := composeAction (secondMovedFactorEquiv c he f hm) n
  let τ : Representation (ZMod 2) (second c) (secondMoved c).toSubmodule :=
    (secondMoved c).toRepresentation.comp (second c).subtype
  let : Subsingleton (H1 τ) :=
    lower_four_H1 τ h48 hdim (secondMoved_full c e.groupEquiv) ⟨e⟩
  exact hproper (second_fixed_supplement_of_moved_H1 c he)

/-- The fixed kernel vanishes for either binary SL₃ row of the ordinary
nonsplit endgame. This discharges the kernel premise consumed by the parent's
`binary_secondCase_of_fixed_eq_bot`, retaining both one and two natural copies.
The only earlier-source parameter is the published B.4.8(4). -/
theorem binary_secondMoved_fixed_eq_bot [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hyp : FFHypothesis K ρ)
    (h48 : EarlierB48Four.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    [Nontrivial (second c)]
    (f : FactorModuleConclusion (secondAction c))
    (hm : f.space.toSubmodule = moved (secondAction c) ⊤)
    (_hns : ¬ SplitAtSecond c)
    (hproper : fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule ≠ ⊤)
    (hn : IsLinearNatural (secondFactorAction c f) BinaryField.two 3 ∨
      IsRepeatedLinearNatural (secondFactorAction c f) BinaryField.two 3 2) :
    Representation.invariants ((secondMoved c).toRepresentation.comp (second c).subtype) = ⊥ := by
  let := hyp.finite_module
  rcases hn with hn | hn
  · exact binary_single_secondMoved_fixed_eq_bot h48 c he f hm hproper hn
  · exact binary_double_secondMoved_fixed_eq_bot hyp c he f hm hn

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit

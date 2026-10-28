module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Statement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Theory.Representation.GeneralLinearNatural

/-!
# The chosen four-space in the exceptional B.5.6 endgame

For the literal B.5.10 configuration, exceptionality forces the first factor
to equal the selected component. Its moved space is the natural three-space W,
disjoint from V₂=C_V(G₁). Any vector x outside their hyperplane gives the
complement U₁=W+⟨x⟩. Displacements prove G₁-invariance; the irreducible moved
space and zero invariants prove indecomposability. The restriction is faithful,
and the natural quotient map gives U₁ ≅ V/V₂ as G₁-modules.

`first_extension` establishes every premise of the complete universal
B.4.8(3) implication and retains all its conclusions. `EarlierB48Three` is
an explicit earlier-source input for discharge by the B.5.6 assembly owner,
with producer qt-b-04-natural-extensions. No G-invariance of U₁ is claimed.
The splitting and cohomological branches on p.110 remain separate proofs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.8(3), printed p.91; final proof of B.5.6, printed p.110, first paragraph.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension
open ComponentReduction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

theorem first_dimension (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space) :
    Module.finrank (ZMod 2) c.sectionData.space.toSubmodule = 3 := by
  obtain ⟨e⟩ := he.1
  exact e.linearEquiv.finrank_eq.trans (show
      Module.finrank (ZMod 2) (Fin 3 → BinaryField.two.Carrier) = 3 from
        Module.finrank_fin_fun (ZMod 2))

private theorem case_first_eq_component {A L H : Subgroup G} {s : MovedSection ρ L}
    (hc : ComponentActionCase ρ A L s H)
    (hn : IsLinearNatural (s.space.toRepresentation.comp H.subtype) BinaryField.two 3) :
    H = L := by
  obtain ⟨e⟩ := hn
  have hd : Module.finrank (ZMod 2) s.space.toSubmodule = 3 := by
    exact e.linearEquiv.finrank_eq.trans (show
      Module.finrank (ZMod 2) (Fin 3 → BinaryField.two.Carrier) = 3 from
        Module.finrank_fin_fun (ZMod 2))
  cases hc with
  | symmetricFive action ho hs =>
    have hd' := action.action.linearEquiv.finrank_eq
    have hn := BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)
    rw [hn] at hd'
    simp only [Fintype.card_fin] at hd'
    omega
  | linearTwo => rfl
  | doubleThree => rfl
  | naturalThree => rfl
  | fourCover => rfl

theorem first_eq_component (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space) : c.first = c.component :=
  case_first_eq_component c.actionCase he.1

theorem first_moved (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space) :
    moved ρ c.first = c.sectionData.space.toSubmodule := by
  rw [first_eq_component c he, c.sectionData.space_eq]

theorem natural_disjoint_fixed {H : Subgroup G} {W : Subrepresentation ρ}
    (hn : IsLinearNatural (W.toRepresentation.comp H.subtype) BinaryField.two 3) :
    Disjoint W.toSubmodule (fixedSpace ρ H) := by
  obtain ⟨e⟩ := hn
  have hz := invariants_of_equiv e (linearNatural_invariants BinaryField.two (by decide : 2 ≤ 3))
  apply Submodule.disjoint_def.mpr
  intro v hv hc
  have ht : (⟨v,hv⟩ : W.toSubmodule) ∈ Representation.invariants (W.toRepresentation.comp H.subtype) :=
    fun g => Subtype.ext (hc g)
  rw [hz] at ht
  exact congrArg Subtype.val ht

def chosenSpace (W : Submodule (ZMod 2) V) (x : V) : Submodule (ZMod 2) V :=
  W ⊔ Submodule.span (ZMod 2) {x}

theorem chosenSpace_isCompl [FiniteDimensional (ZMod 2) V]
    {W C : Submodule (ZMod 2) V} (hd : Disjoint W C)
    (hh : Module.finrank (ZMod 2) (V ⧸ (W ⊔ C)) = 1)
    {x : V} (hx : x ∉ W ⊔ C) : IsCompl (chosenSpace W x) C := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro v hv hc
    obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hz
    have ha : a = 0 := by
      by_contra ha
      apply hx
      apply (Submodule.smul_mem_iff _ ha).mp
      have ht : w + a • x ∈ W ⊔ C := Submodule.mem_sup_right hc
      have hw' : w ∈ W ⊔ C := Submodule.mem_sup_left hw
      simpa using (W ⊔ C).sub_mem ht hw'
    simp only [ha, zero_smul, add_zero] at hc ⊢
    exact Submodule.disjoint_def.mp hd w hw hc
  · apply codisjoint_iff.mpr
    have hs := (Submodule.sup_span_singleton_eq_top_iff hx).mpr hh
    simpa only [chosenSpace, sup_assoc, sup_left_comm, sup_comm] using hs

def chosenModule {H : Subgroup G} (W : Subrepresentation ρ)
    (hm : moved ρ H ≤ W.toSubmodule) (x : V) : Subrepresentation (ρ.comp H.subtype) where
  toSubmodule := chosenSpace W.toSubmodule x
  apply_mem_toSubmodule g v hv := by
    have hm' : ρ (g : G) v - v ∈ W.toSubmodule :=
      hm (Submodule.subset_span ⟨g, g.property, v, Submodule.mem_top, rfl⟩)
    have ht := (chosenSpace W.toSubmodule x).add_mem (Submodule.mem_sup_left hm') hv
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, sub_add_cancel] using ht

private theorem chosenModule_invariants {H : Subgroup G} (W : Subrepresentation ρ)
    (hm : moved ρ H ≤ W.toSubmodule) (x : V)
    (hc : Disjoint (chosenSpace W.toSubmodule x) (fixedSpace ρ H)) :
    (chosenModule W hm x).toRepresentation.invariants = ⊥ := by
  apply bot_unique
  intro v hv
  apply Subtype.ext
  exact Submodule.disjoint_def.mp hc v v.property (fun g => congrArg Subtype.val (hv g))

private theorem chosenModule_dimension [FiniteDimensional (ZMod 2) V] {H : Subgroup G}
    (W : Subrepresentation ρ) (hm : moved ρ H ≤ W.toSubmodule)
    (hn : IsLinearNatural (W.toRepresentation.comp H.subtype) BinaryField.two 3)
    {x : V} (hx : x ∉ W.toSubmodule ⊔ fixedSpace ρ H) :
    Module.finrank (ZMod 2) (chosenModule W hm x).toSubmodule = 4 := by
  obtain ⟨e⟩ := hn
  have hd : Module.finrank (ZMod 2) W.toSubmodule = 3 := by exact e.linearEquiv.finrank_eq.trans (show
      Module.finrank (ZMod 2) (Fin 3 → BinaryField.two.Carrier) = 3 from
        Module.finrank_fin_fun (ZMod 2))
  have hxW : x ∉ W.toSubmodule := fun h => hx (Submodule.mem_sup_left h)
  change Module.finrank (ZMod 2) ↥(W.toSubmodule ⊔ Submodule.span (ZMod 2) {x}) = 4
  rw [Submodule.finrank_sup_span_singleton hxW, hd]


private def chosenNatural {H : Subgroup G} (W : Subrepresentation ρ)
    (hm : moved ρ H ≤ W.toSubmodule) (x : V) :
    Subrepresentation (chosenModule W hm x).toRepresentation where
  toSubmodule := W.toSubmodule.comap (chosenModule W hm x).toSubmodule.subtype
  apply_mem_toSubmodule g _v hv := W.apply_mem_toSubmodule (g : G) hv

private noncomputable def chosenNaturalEquiv {H : Subgroup G} (W : Subrepresentation ρ)
    (hm : moved ρ H ≤ W.toSubmodule) (x : V) :
    ActionEquiv (chosenNatural W hm x).toRepresentation
      (W.toRepresentation.comp H.subtype) where
  groupEquiv := MulEquiv.refl H
  linearEquiv := Submodule.comapSubtypeEquivOfLe le_sup_left
  intertwines _ _ := rfl

private theorem chosenModule_moved_map {H : Subgroup G} (W : Subrepresentation ρ)
    (hm : moved ρ H = W.toSubmodule) (x : V)
    (hs : chosenSpace W.toSubmodule x ⊔ fixedSpace ρ H = ⊤) :
    (moved (chosenModule W hm.le x).toRepresentation ⊤).map
      (chosenModule W hm.le x).toSubmodule.subtype = W.toSubmodule := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    exact hm.le (Submodule.subset_span ⟨g, g.property, v, Submodule.mem_top, rfl⟩)
  · apply hm.ge.trans
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    have hv : v ∈ chosenSpace W.toSubmodule x ⊔ fixedSpace ρ H :=
      hs.symm ▸ Submodule.mem_top
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hv
    let av : (chosenModule W hm.le x).toSubmodule := ⟨a,ha⟩
    refine ⟨(chosenModule W hm.le x).toRepresentation ⟨g,hg⟩ av - av,
      Submodule.subset_span ⟨⟨g,hg⟩, Subgroup.mem_top _, av, Submodule.mem_top, rfl⟩, ?_⟩
    change ρ g a - a = ρ g (a+b) - (a+b)
    rw [map_add, show ρ g b = b from hb ⟨g,hg⟩, add_sub_add_right_eq_sub]

private theorem chosenNatural_moved {H : Subgroup G} (W : Subrepresentation ρ)
    (hm : moved ρ H = W.toSubmodule) (x : V)
    (hs : chosenSpace W.toSubmodule x ⊔ fixedSpace ρ H = ⊤) :
    (chosenNatural W hm.le x).toSubmodule = moved (chosenModule W hm.le x).toRepresentation ⊤ := by
  apply Submodule.map_injective_of_injective (chosenModule W hm.le x).toSubmodule.subtype_injective
  rw [chosenModule_moved_map W hm x hs]
  change (W.toSubmodule.comap (chosenModule W hm.le x).toSubmodule.subtype).map _ = _
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr le_sup_left]

private theorem eq_bot_of_disjoint_moved {D U : Type*} [Group D]
    [AddCommGroup U] [Module (ZMod 2) U] {σ : Representation (ZMod 2) D U}
    (hz : σ.invariants = ⊥) (A : Subrepresentation σ)
    (hd : Disjoint (moved σ ⊤) A.toSubmodule) : A = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  apply bot_unique
  intro a ha
  have hf : a ∈ σ.invariants := by
    intro g
    apply sub_eq_zero.mp
    exact Submodule.disjoint_def.mp hd (σ g a - a)
      (Submodule.subset_span ⟨g,Subgroup.mem_top _,a,Submodule.mem_top,rfl⟩)
      (A.toSubmodule.sub_mem (A.apply_mem_toSubmodule g ha) ha)
  rwa [hz] at hf

private theorem indecomposable_of_natural_moved {D U : Type*} [Group D]
    [AddCommGroup U] [Module (ZMod 2) U] {σ : Representation (ZMod 2) D U}
    (hz : σ.invariants = ⊥) (N : Subrepresentation σ)
    (hm : N.toSubmodule = moved σ ⊤)
    (e : ActionEquiv N.toRepresentation (linearNatural BinaryField.two 3)) :
    IsIndecomposable σ := by
  let := irreducible_of_equiv e (linearNatural_irreducible BinaryField.two (by decide : 2 ≤ 3))
  let : Nontrivial N.toSubmodule := Subrepresentation.irreducible_module_nontrivial N.toRepresentation
  let : Nontrivial U := Function.Injective.nontrivial N.toSubmodule.subtype_injective
  have hn : IsAtom N := Subrepresentation.irreducible_iff_isAtom N |>.mp inferInstance
  refine ⟨inferInstance, fun A B hc => ?_⟩
  by_cases hA : N ≤ A
  · right
    apply eq_bot_of_disjoint_moved hz B
    rw [← hm]
    exact hc.disjoint.mono_left hA
  · left
    apply eq_bot_of_disjoint_moved hz A
    rw [← hm]
    have hd := hn.not_le_iff_disjoint.mp hA
    rw [disjoint_iff] at hd ⊢
    exact congrArg Subrepresentation.toSubmodule hd

private theorem faithful_of_natural_submodule {D U : Type*} [Group D]
    [AddCommGroup U] [Module (ZMod 2) U] {σ : Representation (ZMod 2) D U}
    (N : Subrepresentation σ)
    (e : ActionEquiv N.toRepresentation (linearNatural BinaryField.two 3)) :
    Function.Injective σ := by
  intro g h he
  apply e.groupEquiv.injective
  apply specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := e.linearEquiv.surjective v
  have hw : N.toRepresentation g w = N.toRepresentation h w := by
    apply Subtype.ext
    exact LinearMap.congr_fun he w
  exact (e.intertwines g w).symm.trans ((congrArg e.linearEquiv hw).trans (e.intertwines h w))


/-- Full universal B.4.8(3), retaining the marked natural action and every
conclusion. This is an earlier-source input, not a classification assumption. -/
def EarlierB48Three : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (U : Type v) [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (σ : Representation (ZMod 2) D U),
    Function.Injective σ → IsIndecomposable σ → Module.finrank (ZMod 2) U = 4 →
    ∀ N : Subrepresentation σ, N.toSubmodule = moved σ ⊤ →
    ∀ e : ActionEquiv N.toRepresentation (linearNatural BinaryField.two 3),
      (∀ A, IsBestOffender σ A ↔
        IsFullAxisGroup BinaryField.two 3 (A.map e.groupEquiv.toMonoidHom)) ∧
      quadraticRatio σ = 1 ∧
      (∀ a : D, orderOf a = 2 → moved σ (zpowers a) = fixedSpace σ (zpowers a) ∧
        Module.finrank (ZMod 2) (fixedSpace σ (zpowers a)) = 2 ∧
        fixedSpace σ (zpowers a) ≤ N.toSubmodule)

theorem chosenModule_source [Finite G] [FiniteDimensional (ZMod 2) V]
    (h48 : EarlierB48Three.{u,v}) {H : Subgroup G} (W : Subrepresentation ρ)
    (hm : moved ρ H = W.toSubmodule)
    (he : IsExceptional ρ H W) {x : V}
    (hx : x ∉ W.toSubmodule ⊔ fixedSpace ρ H) :
    Nonempty (FourDimensionalSource (chosenModule W hm.le x).toRepresentation) := by
  have hc := chosenSpace_isCompl (natural_disjoint_fixed he.1) he.2 hx
  have hz := chosenModule_invariants W hm.le x hc.disjoint
  let N := chosenNatural W hm.le x
  obtain ⟨e⟩ := he.1
  let q := chosenNaturalEquiv W hm.le x
  let e' : ActionEquiv N.toRepresentation (linearNatural BinaryField.two 3) :=
    ⟨q.groupEquiv.trans e.groupEquiv, q.linearEquiv.trans e.linearEquiv,
      fun g v => (congrArg e.linearEquiv (q.intertwines g v)).trans
        (e.intertwines (q.groupEquiv g) (q.linearEquiv v))⟩
  have hN := chosenNatural_moved W hm x hc.sup_eq_top
  have hi := indecomposable_of_natural_moved hz N hN e'
  have hf := faithful_of_natural_submodule N e'
  have hd := chosenModule_dimension W hm.le he.1 hx
  obtain ⟨ho,hq,ha⟩ := h48 H _ _ hf hi hd N hN e'
  exact ⟨⟨hd,hi,N,hN,e',ho,hq,ha⟩⟩

noncomputable def chosenQuotientEquiv {H : Subgroup G} (W C : Subrepresentation ρ)
    (hm : moved ρ H ≤ W.toSubmodule) (x : V)
    (hc : IsCompl (chosenSpace W.toSubmodule x) C.toSubmodule) :
    ActionEquiv (chosenModule W hm x).toRepresentation
      (C.quotientRepresentation.comp H.subtype) where
  groupEquiv := MulEquiv.refl H
  linearEquiv := (C.toSubmodule.quotientEquivOfIsCompl
    (chosenModule W hm x).toSubmodule hc.symm).symm
  intertwines _ _ := rfl

theorem exists_outside {H : Subgroup G} {W : Subrepresentation ρ}
    (he : IsExceptional ρ H W) : ∃ x : V, x ∉ W.toSubmodule ⊔ fixedSpace ρ H := by
  by_contra! hn
  have ht : W.toSubmodule ⊔ fixedSpace ρ H = ⊤ := by
    apply top_unique
    intro x _
    exact hn x
  have hd := he.2
  rw [ht] at hd
  have hz : Module.finrank (ZMod 2) (V ⧸ (⊤ : Submodule (ZMod 2) V)) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [hz] at hd
  omega

/-- The first sentence of p.110 on the literal component configuration.
The only invariance asserted for the chosen four-space is under G₁. -/
theorem first_extension [Finite G] [FiniteDimensional (ZMod 2) V]
    (h48 : EarlierB48Three.{u,v}) (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space) :
    ∃ x : V, x ∉ c.sectionData.space.toSubmodule ⊔ c.productConfiguration.fixed.toSubmodule ∧
      IsCompl (chosenSpace c.sectionData.space.toSubmodule x)
        c.productConfiguration.fixed.toSubmodule ∧
      Nonempty (FourDimensionalSource
        (chosenModule c.sectionData.space (first_moved c he).le x).toRepresentation) := by
  obtain ⟨x,hx⟩ := exists_outside he
  refine ⟨x, ?_, ?_, chosenModule_source h48 c.sectionData.space (first_moved c he) he hx⟩
  · simpa only [c.productConfiguration.fixed_eq] using hx
  · simpa only [c.productConfiguration.fixed_eq] using
      chosenSpace_isCompl (natural_disjoint_fixed he.1) he.2 hx

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension

module
public import CFSG.Quasithin.ChapterD.Section02.Inheritance
public import Theory.Representation.BinaryOffender.NonStrongMovedSection
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.IsotypicQuotient
public import Theory.Representation.BinaryOffender.FaithfulComponentPair
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent

/-!
# Strict cubic-ratio descent to an invariant constituent

A starred cubic actor acting nontrivially on a normal component admits the
D.2.7 restriction alternative. If the component moves the whole module,
equality forces the chosen invariant constituent to be the whole module.
Thus every proper invariant constituent gives a strict ratio decrease.

For an isotypic restriction, odd-copy selection constructs the invariant
constituent for the actual elementary actor. In an irreducible action with
a commuting perfect supplement, the type is isotypic and every constituent
is proper, so neither constituent selection nor properness is an extra input.
The original Chapter 10 tensor seed is the consumer.

Source: Aschbacher--Smith D.3.7, component-preserving actor branch,
printed pp.198--199, using A.1.42(2) and D.2.7--8.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MonoidAlgebra
namespace CFSG.Quasithin.ChapterD
open Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

theorem constituent_ratio_strict_drop
    (A : Subgroup G) (hA : A ∈ QhatStar ρ)
    (hgen : ⁅L,A⁆ = L) (hm : subspaceCommutator ρ ⊤ L = ⊤)
    (hfix : fixedSpace ρ L = ⊥)
    (U : Subrepresentation (ρ.comp L.subtype)) (hi : U.toRepresentation.IsIrreducible)
    (hproper : U.toSubmodule ≠ ⊤)
    (hst : A ≤ subspaceStabilizer ρ U.toSubmodule) :
    restrictedSubgroup ρ U.toSubmodule A ∈ Qhat (subspaceImageRepresentation ρ U.toSubmodule) ∧
    actionRatio (subspaceImageRepresentation ρ U.toSubmodule)
      (restrictedSubgroup ρ U.toSubmodule A) < cubicRatio ρ := by
  have hLU : L ≤ subspaceStabilizer ρ U.toSubmodule :=
    le_subspaceStabilizer ρ _ (fun l hl v hv => U.apply_mem_toSubmodule ⟨l,hl⟩ hv)
  have hne : U.toSubmodule ≠ ⊥ := fun he =>
    ((Subrepresentation.irreducible_iff_isAtom U).mp hi).ne_bot
      (Subrepresentation.toSubmodule_injective he)
  have hn : ¬ U.toSubmodule ≤ fixedSpace ρ A := by
    intro hf
    have hh := le_fixedSpace_commutator_of_invariant ρ hLU hf
    rw [hgen,hfix] at hh
    exact hne (bot_unique hh)
  obtain ⟨_,_,hd | ⟨_,hs⟩⟩ := QhatStar.restriction_alternatives ρ hA U.toSubmodule hst hn
  · exact hd
  · have hh := subspaceCommutator_le_of_fixed_span ρ hgen hLU hst hs
    rw [hm] at hh
    exact (hproper (top_unique hh)).elim

theorem exists_constituent_ratio_strict_drop [L.Normal] [Nontrivial V]
    {E : Type*} [AddCommGroup E] [Module (ZMod 2)[L] E]
    [IsSemisimpleModule (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype))]
    (htype : IsIsotypicOfType (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype)) E)
    (hred : ¬ IsIrreducible (ρ.comp L.subtype))
    (hm : subspaceCommutator ρ ⊤ L = ⊤) (hfix : fixedSpace ρ L = ⊥)
    (A : Subgroup G) (hA : A ∈ QhatStar ρ) (hgen : ⁅L,A⁆ = L) :
    ∃ U : Subrepresentation (ρ.comp L.subtype), U.toRepresentation.IsIrreducible ∧
      A ≤ subspaceStabilizer ρ U.toSubmodule ∧
      restrictedSubgroup ρ U.toSubmodule A ∈ Qhat (subspaceImageRepresentation ρ U.toSubmodule) ∧
      actionRatio (subspaceImageRepresentation ρ U.toSubmodule)
        (restrictedSubgroup ρ U.toSubmodule A) < cubicRatio ρ := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  let : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨U,hi,_,hst⟩ := exists_invariant_simple_of_isotypic ρ L htype A
    (IsElementaryAbelian.isPGroup 2 A)
  have hstable : A ≤ subspaceStabilizer ρ U.toSubmodule := by
    intro a ha
    exact (subspace_map_eq_iff ρ U.toSubmodule a).mp (hst ⟨a,ha⟩)
  have hproper : U.toSubmodule ≠ ⊤ := by
    intro he
    apply hred
    have hh : U = ⊤ := Subrepresentation.toSubmodule_injective he
    exact isSimpleOrder_iff_isAtom_top.mpr
      (hh ▸ (Subrepresentation.irreducible_iff_isAtom U).mp hi)
  exact ⟨U,hi,hstable,constituent_ratio_strict_drop ρ L A hA hgen hm hfix U hi hproper hstable⟩
/-- A commuting perfect supplement supplies both isotypy and properness;
no invariant constituent is assumed. -/
theorem exists_constituent_drop_of_commuting_supplement [L.Normal]
    [IsQuasisimple L] (hi : IsIrreducible ρ) (hf : Function.Injective ρ)
    (hsup : L ⊔ centralizer (L : Set G) = ⊤)
    (K : Subgroup G) [Group.IsPerfect K] [Nontrivial K]
    (hK : K ≤ centralizer (L : Set G))
    (A : Subgroup G) (hA : A ∈ QhatStar ρ)
    (hmove : ¬ A ≤ centralizer (L : Set G)) :
    ∃ U : Subrepresentation (ρ.comp L.subtype), U.toRepresentation.IsIrreducible ∧
      A ≤ subspaceStabilizer ρ U.toSubmodule ∧
      restrictedSubgroup ρ U.toSubmodule A ∈ Qhat (subspaceImageRepresentation ρ U.toSubmodule) ∧
      actionRatio (subspaceImageRepresentation ρ U.toSubmodule)
        (restrictedSubgroup ρ U.toSubmodule A) < cubicRatio ρ := by
  let := hi
  let := Subrepresentation.irreducible_module_nontrivial ρ
  let := NormalConstituentDisplacement.restriction_semisimple ρ hi L
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hLn : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance
  let σ : Representation (ZMod 2) L V := ρ.comp L.subtype
  let : Nontrivial σ.asModule := σ.asModuleEquiv.toEquiv.nontrivial
  obtain ⟨S,hS⟩ := IsSemisimpleModule.exists_simple_submodule (ZMod 2)[L] σ.asModule
  let U := Subrepresentation.ofSubmodule' S
  have hU : U.toRepresentation.IsIrreducible := by
    rw [Subrepresentation.irreducible_iff_isAtom]
    exact Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff U |>.mp
      (isSimpleModule_iff_isAtom.mp hS)
  have ht : (normalTypeAction ρ L).inertia U = ⊤ := by
    apply top_unique
    rw [←hsup]
    exact sup_le (normal_le_typeInertia ρ L U) (centralizer_le_typeInertia ρ L U)
  have htype := restriction_isotypic_of_typeInertia_top ρ L U hU ht
  have hgen : ⁅L,A⁆ = L :=
    IsComponent.commutator_eq_self_of_normalizes
      (show IsComponent G L from ⟨(inferInstance : L.Normal).isSubnormal,inferInstance⟩)
      (by rw [normalizer_eq_top]; exact le_top) (by
        intro he
        exact hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)))
  exact exists_constituent_ratio_strict_drop ρ L htype
    (not_irreducible_of_faithful_commuting_perfect ρ hf L K hK)
    (subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hf hi L hLn)
    (fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi L hLn)
    A hA hgen
end CFSG.Quasithin.ChapterD

namespace CFSG.Quasithin.ChapterD
variable {S V : Type*} [Group S] [Finite S] [IsQuasisimple S]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Every starred actor on a faithful irreducible square has a proper invariant
constituent for a factor it moves, with strictly smaller ratio. -/
theorem square_actor_constituent_drop
    (hZ : center S = ⊥)
    (ρ : Representation (ZMod 2) (S × S) V) (hi : IsIrreducible ρ)
    (hf : Function.Injective ρ) (A : Subgroup (S × S)) (hA : A ∈ QhatStar ρ) :
    ∃ J : Subgroup (S × S),
      (J = (⊤ : Subgroup S).prod ⊥ ∨ J = (⊥ : Subgroup S).prod ⊤) ∧
      ∃ U : Subrepresentation (ρ.comp J.subtype), U.toRepresentation.IsIrreducible ∧
        A ≤ subspaceStabilizer ρ U.toSubmodule ∧
        restrictedSubgroup ρ U.toSubmodule A ∈ Qhat (subspaceImageRepresentation ρ U.toSubmodule) ∧
        actionRatio (subspaceImageRepresentation ρ U.toSubmodule)
          (restrictedSubgroup ρ U.toSubmodule A) < cubicRatio ρ := by
  let J : Subgroup (S × S) := (⊤ : Subgroup S).prod ⊥
  let K : Subgroup (S × S) := (⊥ : Subgroup S).prod ⊤
  let eJ : J ≃* S := {
    toFun x := x.val.1
    invFun x := ⟨(x,1),mem_top x,rfl⟩
    left_inv x := Subtype.ext (Prod.ext rfl (mem_bot.mp x.property.2).symm)
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let eK : K ≃* S := {
    toFun x := x.val.2
    invFun x := ⟨(1,x),rfl,mem_top x⟩
    left_inv x := Subtype.ext (Prod.ext (mem_bot.mp x.property.1).symm rfl)
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let : IsQuasisimple J := IsQuasisimple.of_mulEquiv eJ.symm
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv eK.symm
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  let : Nontrivial J := eJ.surjective.nontrivial
  let : Nontrivial K := eK.surjective.nontrivial
  have hc : K ≤ centralizer (J : Set (S × S)) := by
    intro k hk j hj
    apply Prod.ext
    · simp only [Prod.fst_mul,mem_bot.mp hk.1,mul_one,one_mul]
    · simp only [Prod.snd_mul,mem_bot.mp hj.2,mul_one,one_mul]
  have hs : J ⊔ K = ⊤ := by
    apply top_unique
    intro x _
    have he : x = (x.1,1)*(1,x.2) := by simp
    rw [he]
    exact (J ⊔ K).mul_mem (mem_sup_left ⟨mem_top _,rfl⟩)
      (mem_sup_right ⟨rfl,mem_top _⟩)
  have hmove : ¬ A ≤ centralizer (J : Set (S × S)) ∨
      ¬ A ≤ centralizer (K : Set (S × S)) := by
    by_contra! hn
    apply hA.1.2.1.1
    apply bot_unique
    intro a ha
    have hx : a.1 ∈ center S := by
      apply mem_center_iff.mpr
      intro x
      exact congrArg Prod.fst (hn.1 ha (x,1) ⟨mem_top _,rfl⟩)
    have hy : a.2 ∈ center S := by
      apply mem_center_iff.mpr
      intro y
      exact congrArg Prod.snd (hn.2 ha (1,y) ⟨rfl,mem_top _⟩)
    exact mem_bot.mpr (Prod.ext (mem_bot.mp (hZ ▸ hx)) (mem_bot.mp (hZ ▸ hy)))
  rcases hmove with hmove | hmove
  · refine ⟨J,Or.inl rfl,?_⟩
    exact exists_constituent_drop_of_commuting_supplement ρ J hi hf
      (top_unique (hs ▸ sup_le_sup_left hc J)) K hc A hA hmove
  · refine ⟨K,Or.inr rfl,?_⟩
    have hc' := le_centralizer_iff.mp hc
    exact exists_constituent_drop_of_commuting_supplement ρ K hi hf
      (top_unique ((sup_comm K J).trans hs ▸ sup_le_sup_left hc' K)) J hc' A hA hmove
end CFSG.Quasithin.ChapterD


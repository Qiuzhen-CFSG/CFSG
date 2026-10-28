module
public import CFSG.Quasithin.KnownSimpleSectionTransport
public import CFSG.Quasithin.ChapterD.Section03.PreservingConstituent
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SQTKSectionImage
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition
public import Theory.Representation.BinaryOffender.QuasisimpleRestrictionFitting
public import Theory.Representation.BinaryOffender.CubicSection

/-!
# Recognition of even-linear constituents under cubic actors

For a faithful action irreducible on a normal quasisimple component, adjoining
an elementary cubic actor gives a two-group quotient with trivial two-core.
Its generalized Fitting subgroup is exactly that component; the SQTK property
comes from the actual component and the two-group extension. This establishes
the precise Chapter K domain without imposing hypotheses on the entire
ambient normalizer.

The proved rank-one classifier gives a natural or Hermitian intertwiner and
binary degree twice the field degree. Descent to an invariant constituent
retains the original component marking. For an irreducible commuting pair,
odd-copy selection and strict ratio descent construct a proper constituent
for whichever factor the actor moves. The even square and original Chapter10
seed applications consume this result, including ambient outer actors.
Source: Aschbacher--Smith D.3.7, A.1.42 and K.3.1,
printed pp.197--199,32,453--454.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem normal_component_actor_source
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (hi : IsIrreducible (ρ.comp L.subtype))
    (A : Subgroup G) (hA : IsElementaryTwo A) (hc : IsCubic ρ A)
    (hsmall : actionRatio ρ A ≤ 2) :
    ChapterK.RankOne.SourceHypotheses (ρ.comp (L ⊔ A).subtype)
      (L.subgroupOf (L ⊔ A)) := by
  let : IsElementaryAbelian 2 A := hA.2
  let : IsIrreducible (ρ.comp L.subtype) := hi
  let := Subrepresentation.irreducible_module_nontrivial (ρ.comp L.subtype)
  let H := L ⊔ A
  let N := L.subgroupOf H
  let C := A.subgroupOf H
  let eN : N ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  let : IsQuasisimple N := IsQuasisimple.of_mulEquiv eN.symm
  let τ : Representation (ZMod 2) H V := ρ.comp H.subtype
  have hτ : Function.Injective τ := hf.comp H.subtype_injective
  have hirr : IsIrreducible (τ.comp N.subtype) :=
    (irreducible_comp_surjective_iff eN.toMonoidHom eN.surjective (ρ.comp L.subtype)).mpr hi
  have hquot : IsPGroup 2 (H ⧸ N) :=
    quotient_isPGroup_of_sup_eq_top C N
      ((IsElementaryAbelian.isPGroup 2 A).of_injective
        (subgroupOfEquivOfLe (show A ≤ H from le_sup_right)).toMonoidHom
        (subgroupOfEquivOfLe (show A ≤ H from le_sup_right)).injective)
      ((sup_comm C N).trans (codisjoint_subgroupOf_sup L A).eq_top)
  have hcore : pCore 2 H = ⊥ := by
    let : τ.IsIrreducible := irreducible_of_subgroup_restriction τ N hirr
    have hk := normal_p_subgroup_le_ker τ (pCore 2 H) pCore_isPGroup
    exact bot_unique (hk.trans (τ.ker_eq_bot_iff.mpr hτ).le)
  have hN : IsSQTK KnownSimple.IsKnownSimple N := (IsSQTK.equiv eN).mpr hL
  have hH : IsSQTK KnownSimple.IsKnownSimple H :=
    ChapterB.QuasisimpleSource.IrreducibleBranch.sqtk_of_twoGroup_quotient
      ChapterB.ComponentRecognition.SQTKSectionImage.knownSimple_containsSimpleTwoGroups N hquot hN
  have hC : IsElementaryTwo C := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf (show A ≤ H from le_sup_right)⟩
    intro he
    change A.subgroupOf H = ⊥ at he
    exact hA.1 (by rw [←map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right),he,Subgroup.map_bot])
  have hratio : actionRatio τ C = actionRatio ρ A := by
    unfold actionRatio
    rw [fixedCodim_subgroupOf ρ (show A ≤ H from le_sup_right),
      rank_subgroupOf (show A ≤ H from le_sup_right)]
  have hbound : cubicRatio τ ≤ actionRatio ρ A := by
    rw [←hratio]
    exact iInf_le_of_le C (iInf_le_of_le ⟨hC,fun a ha b hb c hc' v => hc a ha b hb c hc' v⟩ le_rfl)
  have hs : ChapterK.RankOne.SourceHypotheses τ N :=
    ⟨hH,generalizedFitting_eq_of_quasisimple_two_quotient N hquot hcore,
      inferInstance,hτ,hirr,hbound.trans hsmall⟩
  exact hs

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance evenConstituentAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2

theorem even_component_actor_recognition
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (hi : IsIrreducible (ρ.comp L.subtype))
    (e : L ≃* SL(2,F)) (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hc : IsCubic ρ A)
    (hsmall : actionRatio ρ A ≤ 2) :
    let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
    Module.finrank (ZMod 2) V = 2*n ∧
      (SL2.BinarySmall.IsNatural σ ∨ ∃ s : ℕ, n = 2*s ∧
        ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩; SL2.BinarySmall.IsHermitian σ s) := by
  let H := L ⊔ A
  let N := L.subgroupOf H
  let τ : Representation (ZMod 2) H V := ρ.comp H.subtype
  let eN : N ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  have h := normal_component_actor_source ρ hf L hL hi A hA hc hsmall
  have hd := h.psl2_degree_window (eN.trans e) hn hF
  have halts := h.binary_module_alternatives (eN.trans e) n hn hF hd
  change let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom; _
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  have he : (τ.comp N.subtype).comp (eN.trans e).symm.toMonoidHom = σ := by
    ext g v
    rfl
  change _ ∨ _ ∨ _ at halts
  rw [he] at halts
  rcases halts with hh | hh | hh
  · exact ⟨hh.1,Or.inl hh.2⟩
  · obtain ⟨s,hs,hn,hd,hs',hh⟩ := hh
    exact ⟨hd,Or.inr ⟨s,hn,hs',hh⟩⟩
  · have hx := h.psl2_not_isTriple_of_card_eight (eN.trans e) (by simpa [hh.1] using hF)
    rw [he] at hx
    exact (hx hh.2.2.1).elim

/-- Recognition on the literal invariant subspace retains the original layer marking. -/
theorem even_subspace_actor_recognition
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (e : L ≃* SL(2,F)) (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (U : Subrepresentation (ρ.comp L.subtype)) (hi : U.toRepresentation.IsIrreducible)
    (hf : Function.Injective U.toRepresentation)
    (C : Subgroup (subspaceActionImage ρ U.toSubmodule))
    (hC : C ∈ Qhat (subspaceImageRepresentation ρ U.toSubmodule)) :
    let σ := U.toRepresentation.comp e.symm.toMonoidHom
    Module.finrank (ZMod 2) U.toSubmodule = 2*n ∧
      (SL2.BinarySmall.IsNatural σ ∨ ∃ s : ℕ, n = 2*s ∧
        ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩; SL2.BinarySmall.IsHermitian σ s) := by
  let f := subgroupActionHom ρ U.toSubmodule L (le_constituent_stabilizer ρ L U)
  have hfi : Function.Injective f := by
    intro x y h
    apply hf
    exact congrArg (subspaceImageRepresentation ρ U.toSubmodule) h
  let N := restrictedSubgroup ρ U.toSubmodule L
  let eN : L ≃* N := (MonoidHom.ofInjective hfi).trans
    (MulEquiv.subgroupCongr (subgroupActionHom_range ρ U.toSubmodule L _))
  let : N.Normal := Normal.map inferInstance (subspaceActionHom ρ U.toSubmodule)
    (stabilizerRepresentation ρ U.toSubmodule).asGroupHom.rangeRestrict_surjective
  let : IsQuasisimple N := IsQuasisimple.of_mulEquiv eN
  have hN : IsSQTK KnownSimple.IsKnownSimple N := hL.knownSimple_of_equiv eN
  have hirr : IsIrreducible ((subspaceImageRepresentation ρ U.toSubmodule).comp N.subtype) := by
    apply (irreducible_comp_surjective_iff eN.toMonoidHom eN.surjective _).mp
    exact hi
  exact even_component_actor_recognition (subspaceImageRepresentation ρ U.toSubmodule)
    (subspaceImageRepresentation_injective ρ U.toSubmodule) N hN hirr
    (eN.symm.trans e) n hn hF C hC.1 hC.2.1 hC.2.2

/-- A moved member of an irreducible even-linear pair has a proper constituent
with a genuine natural or Hermitian marking and strictly smaller actor ratio. -/
theorem even_pair_moved_constituent
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (L K : Subgroup G) [L.Normal] [IsSimpleGroup L] [IsQuasisimple L]
    [Group.IsPerfect K] [Nontrivial K]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (e : L ≃* SL(2,F)) (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (hi : IsIrreducible (ρ.comp (L ⊔ K).subtype))
    (hc : K ≤ centralizer (L : Set G))
    (A : Subgroup G) (hA : A ∈ QhatStar ρ)
    (hmove : ¬ A ≤ centralizer (L : Set G)) :
    ∃ U : Subrepresentation (ρ.comp L.subtype), U.toRepresentation.IsIrreducible ∧
      Function.Injective U.toRepresentation ∧ U.toSubmodule ≠ ⊤ ∧
      A ≤ subspaceStabilizer ρ U.toSubmodule ∧
      restrictedSubgroup ρ U.toSubmodule A ∈ Qhat (subspaceImageRepresentation ρ U.toSubmodule) ∧
      actionRatio (subspaceImageRepresentation ρ U.toSubmodule)
        (restrictedSubgroup ρ U.toSubmodule A) < cubicRatio ρ ∧
      Module.finrank (ZMod 2) U.toSubmodule = 2*n ∧
      (SL2.BinarySmall.IsNatural (U.toRepresentation.comp e.symm.toMonoidHom) ∨
        ∃ s : ℕ, n = 2*s ∧ ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩;
          SL2.BinarySmall.IsHermitian (U.toRepresentation.comp e.symm.toMonoidHom) s) := by
  let : IsIrreducible ρ := irreducible_of_subgroup_restriction ρ (L ⊔ K) hi
  obtain ⟨U,hU,hst,hC,hd⟩ := exists_constituent_drop_of_irreducible_pair ρ L K hi hf hc A hA hmove
  have hLn : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance
  have hfix : Representation.invariants (ρ.comp L.subtype) = ⊥ :=
    fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf inferInstance L hLn
  have hfaith := simple_subrepresentation_faithful_of_fixed_eq_bot (ρ.comp L.subtype)
    hfix U ((Subrepresentation.irreducible_iff_isAtom U).mp hU).ne_bot
  have hproper : U.toSubmodule ≠ ⊤ := by
    intro ht
    have hu : U = ⊤ := Subrepresentation.toSubmodule_injective ht
    have hh := isSimpleOrder_iff_isAtom_top.mpr
      (hu ▸ (Subrepresentation.irreducible_iff_isAtom U).mp hU)
    exact not_irreducible_of_faithful_commuting_perfect ρ hf L K hc hh
  exact ⟨U,hU,hfaith,hproper,hst,hC,hd,
    even_subspace_actor_recognition ρ L hL e n hn hF U hU hfaith _ hC⟩
end CFSG.Quasithin.ChapterD

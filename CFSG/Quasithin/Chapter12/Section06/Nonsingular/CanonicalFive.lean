module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalSevenModule

/-!
# The canonical SL5(2) moved fixed space

B.5.1 gives natural, repeated-natural, natural-plus-dual, or exterior
alternatives on the literal canonical module. The proved cohomology
calculations split the central attachment in the irreducible rows; the
other rows have zero invariants directly. Thus [U,K_v] has no nonidentity
K_v-fixed vector, retaining the actual quotient action and ambient maps.

Since the original V_v lies in [U,K_v], its fixed line is moved by K_v.
The unchanged central projection forces the original C_V(L) nontrivial.
CanonicalFixedSpace supplies the fixed-free source application. FF remains
explicit; no exterior-square coordinate recognition is assumed.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.18, printed p.827, B.5.1, pp.99--103, and I.1.6, p.408.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem five_moved_disjoint
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {ρ : Representation (ZMod 2) A W} {K : Subgroup A}
    (s : MovedSection ρ K) (h : SourceCompletion.BinaryActor.ActionCase ρ K s 5) :
    Disjoint s.space.toSubmodule (fixedSpace ρ K) := by
  cases h with
  | naturalDual _ hn =>
    obtain ⟨e⟩ := hn
    exact ExtensionConsequences.moved_disjoint_fixed s
      (ExtensionConsequences.invariants_of_equiv e
        (ExtensionConsequences.naturalDual_invariants (by decide)))
  | repeatedNatural r _ _ _ hn =>
    obtain ⟨e⟩ := hn
    exact ExtensionConsequences.moved_disjoint_fixed s
      (ExtensionConsequences.invariants_of_equiv e
        (ExtensionConsequences.repeated_invariants r
          (ExtensionConsequences.linearNatural_invariants BinaryField.two (by decide))))
  | irreducible hi hf hir hs he =>
    cases hs with
    | natural _ e _ => exact (ExtensionConsequences.binaryLinear_isCompl s hi (by decide) e).disjoint
    | orthogonal hd _ _ _ _ _ => omega
    | symmetricEight hd _ _ _ => omega
    | exterior _ hg hw e hdim ho hr =>
      exact (ExtensionConsequences.exteriorFive_isCompl s
        ⟨hi,hf,hir,.exteriorFive hg hw e hdim ho hr,he⟩ e hdim).disjoint

private theorem canonical_moved_fixed_eq_bot_of_disjoint
    {A : Type*} [Group A]
    (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E] (K : Subgroup A)
    (hBO : K.map (ChapterB.InternalThompsonAction.actionMk E) ≤
      offenderSubgroup (ChapterB.InternalThompsonAction.action E))
    (s : MovedSection ((ChapterB.InternalThompsonAction.action E).comp
      (offenderSubgroup (ChapterB.InternalThompsonAction.action E)).subtype)
      ((K.map (ChapterB.InternalThompsonAction.actionMk E)).subgroupOf
        (offenderSubgroup (ChapterB.InternalThompsonAction.action E))))
    (hs : Disjoint s.space.toSubmodule
      (fixedSpace ((ChapterB.InternalThompsonAction.action E).comp
        (offenderSubgroup (ChapterB.InternalThompsonAction.action E)).subtype)
        ((K.map (ChapterB.InternalThompsonAction.actionMk E)).subgroupOf
          (offenderSubgroup (ChapterB.InternalThompsonAction.action E))))) :
    (⁅E,K⁆ : Subgroup A) ⊓ centralizer (K : Set A) = ⊥ := by
  let q := ChapterB.InternalThompsonAction.actionMk E
  let ρ := ChapterB.InternalThompsonAction.action E
  let B := K.map q
  let O := offenderSubgroup ρ
  let C := B.subgroupOf O
  have hspace : s.space.toSubmodule = subspaceCommutator ρ ⊤ B := by
    rw [s.space_eq]
    change subspaceCommutator (ρ.comp O.subtype) ⊤ C = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hBO]
  apply bot_unique
  intro x hx
  let u : Additive E := Additive.ofMul ⟨x,commutator_le_left E K hx.1⟩
  have hu : u ∈ s.space.toSubmodule := by
    rw [hspace]
    change u ∈ subspaceCommutator (NormalElementaryQuotient.representation E q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ (K.map q)
    rw [←NormalElementaryQuotient.commutatorSpace_eq E q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K]
    exact hx.1
  have hf : u ∈ fixedSpace (ρ.comp O.subtype) C := by
    intro c
    obtain ⟨k,hk,hkc⟩ := c.property
    change q k = c.val.val at hkc
    change ρ c.val.val u = u
    rw [←hkc]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [ChapterB.InternalThompsonAction.action_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hx.2 k hk)
  exact congrArg (fun z : Additive E => (z.toMul : A))
    (show u = 0 from (disjoint_iff.mp hs).le ⟨hu,hf⟩)

/-- Every canonical SL5(2) FF row has zero fixed subgroup in its whole
moved space, including the ten-dimensional exterior row. -/
theorem SourceHypothesis.nonsingular_canonical_five_moved_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (S : Sylow 2 (Gv (v : G)))
    (hfive : Nonempty (Star (Kv (v : G)) ≃* SL(5,ZMod 2)))
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
        (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hker : centralizer (reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G) :
      Set (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) =
        pCore 2 (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) :
    let J := Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    let E := reducedTwoSubgroup J
    letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
    IsFFModule (ChapterB.InternalThompsonAction.action E) →
      (⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆ : Subgroup G) ⊓ centralizer (Kv (v : G) : Set G) = ⊥ := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ S₀
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let K := (Kv (v : G)).subgroupOf J
  let q := ChapterB.InternalThompsonAction.actionMk E
  let ρ := ChapterB.InternalThompsonAction.action E
  let B := K.map q
  let O := offenderSubgroup ρ
  let C := B.subgroupOf O
  dsimp only
  intro hff
  obtain ⟨_,_,hBO,⟨c⟩⟩ := H.nonsingular_canonical_quasisimple_of_ff D v hv
    S₀ (map_subtype_le _) (S.isPGroup'.map _) hker hff
  obtain ⟨b⟩ := H.nonsingular_canonical_component_image D v hv S₀ (map_subtype_le _) hker
  obtain ⟨e₅⟩ := hfive
  let e : C ≃* SL(5,ZMod 2) := (subgroupOfEquivOfLe hBO).trans (b.trans e₅)
  let s := c.sectionData
  have hcase := SourceCompletion.BinaryActor.actionCase (ρ.comp O.subtype) (Or.inr rfl) e c.clause_one
  have hc := canonical_moved_fixed_eq_bot_of_disjoint E K hBO s (five_moved_disjoint s hcase)
  have hm := congrArg (Subgroup.map J.subtype) hc
  rw [←map_inf_centralizer_of_injective J.subtype J.subtype_injective,
    map_commutator,map_subgroupOf_eq_of_le (show Kv (v : G) ≤ J from le_sup_left),
    ←hred,Subgroup.map_bot] at hm
  exact hm

/-- The original local fixed line excludes the canonical SL5(2) FF case
when the original global fixed space is trivial. -/
theorem SourceHypothesis.fixed_ne_bot_of_canonical_five
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (S : Sylow 2 (Gv (v : G)))
    (hfive : Nonempty (Star (Kv (v : G)) ≃* SL(5,ZMod 2)))
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
        (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hm : Vv L V (v : G) ≤ ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆)
    (hker : centralizer (reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G) :
      Set (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) =
        pCore 2 (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) :
    let J := Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    let E := reducedTwoSubgroup J
    letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
    IsFFModule (ChapterB.InternalThompsonAction.action E) →
      ZV L V ≠ ⊥ := by
  dsimp only
  intro hff
  have hc := H.nonsingular_canonical_five_moved_fixed D v hv S hfive hred hker hff
  apply D.fixed_ne_bot_of_local_line_moved H.chosen v hv
  intro hline
  have hz : ZV (Lv L (v : G)) (Vv L V (v : G)) = ⊥ :=
    bot_unique ((le_inf (inf_le_left.trans hm) hline).trans hc.le)
  have hh := D.nonsingular_moved_fixed_card H.chosen v hv
  rw [hz,card_bot] at hh
  norm_num at hh

end CFSG.Quasithin.Chapter12.Section06

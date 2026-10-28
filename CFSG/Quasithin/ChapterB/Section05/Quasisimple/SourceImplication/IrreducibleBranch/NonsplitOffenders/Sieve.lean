module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.EasyCases
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction
public import Theory.Representation.BinaryLinearRecognition
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The nonsplit, small-ratio catalogue sieve in B.5.1

The complete corrected B.4.2 catalogue, with J(LT,S)=L and q(LT,S)<1,
leaves the natural L3(2) and Sp4(2^n), n>1, modules. Genuine H1-vanishing
eliminates the larger-field SL3 and binary higher-linear rows. The marked
Sp4(2) and S8 rows cannot have equal marked component and offender group.
The ratio-one rows, including the corrected triple cover, are excluded by
their ratios without constructing any legacy offender witness.

For the binary three-dimensional row, the proved faithfulness of LT on S
puts LT inside GL3(2). Its component already fills that group, so T lies
in L. Source observation alpha then gives G=L. This avoids any appeal to
an already completed outer-extension alternative or to extension splitting.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.5.1,
last irreducible-branch paragraph, printed p.100; the cohomology calculation
is I.1.6(4), printed p.408. The Sp4 natural-cover offender calculation is
still required to complete the paragraph.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
open ExtensionConsequences
universe u v w z
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

private theorem central_eq_bot_of_isCompl (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L)) : s.central.toSubmodule = ⊥ := by
  apply bot_unique
  intro v hv
  rw [s.central_eq] at hv
  have hf : (v : V) ∈ fixedSpace ρ L := fun g => congrArg Subtype.val (hv g)
  exact Subtype.ext (Submodule.disjoint_def.mp hc.disjoint _ v.property hf)

private noncomputable def unrestrictActionEquiv {H : Type w} [Group H]
    {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {τ : Representation (ZMod 2) H W} {D : Subgroup G} (hLD : L ≤ D)
    (e : ActionEquiv ((ρ.comp D.subtype).comp (L.subgroupOf D).subtype) τ) :
    ActionEquiv (ρ.comp L.subtype) τ where
  groupEquiv := (subgroupOfEquivOfLe hLD).symm.trans e.groupEquiv
  linearEquiv := e.linearEquiv
  intertwines g v := e.intertwines ((subgroupOfEquivOfLe hLD).symm g) v

private theorem marked_same_eq_top {H : Type w} [Group H]
    {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {τ : Representation (ZMod 2) H W} {M : Subgroup H}
    (e : MarkedActionEquiv ρ L L τ M) : M = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨l, rfl⟩ := e.action.groupEquiv.surjective g
  have hh := e.compatible l
  change e.action.groupEquiv l = (e.subgroupEquiv l : H) at hh
  rw [hh]
  exact (e.subgroupEquiv l).property

private theorem alternating_ne_top (n : ℕ) (hn : 2 ≤ n) :
    alternatingGroup (Fin n) ≠ ⊤ := by
  intro he
  have hs : Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ∈ alternatingGroup (Fin n) := by
    rw [he]; exact mem_top _
  simp at hs

private theorem symplecticTwo_commutator_ne_top :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≠ ⊤ := by
  intro he
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  have hh := congrArg (Subgroup.map e.toMonoidHom) he
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective,
    ← commutator_def, Subgroup.map_top_of_surjective _ e.surjective] at hh
  rw [alternatingGroup.commutator_perm_eq (by simp : 5 ≤ Nat.card (Fin 6))] at hh
  exact alternating_ne_top 6 (by decide) hh

/-- Source sieve on the complete corrected local catalogue. -/
theorem nonsplit_small_ratio_natural [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule) (T : Sylow 2 G)
    (hc : SourceInduction.ProjectiveLine.IrreducibleActionCase
      (s.action.comp (L ⊔ (T : Subgroup G)).subtype)
      (generalizedFitting ↥(L ⊔ (T : Subgroup G)))
      (offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype)))
    (hJ : offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype) =
      L.subgroupOf (L ⊔ (T : Subgroup G)))
    (hz : s.central.toSubmodule ≠ ⊥)
    (hq : quadraticRatio (s.action.comp (L ⊔ (T : Subgroup G)).subtype) < 1) :
    IsLinearNatural (s.action.comp L.subtype) BinaryField.two 3 ∨
      ∃ F : BinaryField, 1 < F.degree ∧
        Nonempty (ActionEquiv (s.action.comp L.subtype) (binarySymplectic F)) ∧
        quadraticRatio (s.action.comp (L ⊔ (T : Subgroup G)).subtype) = 2 / 3 := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  have hn : ¬ IsCompl s.space.toSubmodule (fixedSpace ρ L) :=
    fun hs => hz (central_eq_bot_of_isCompl s hs)
  rw [local_generalizedFitting L T h.fitting h.twoCore T.isPGroup', hJ] at hc
  cases hc with
  | linearThree F _ e _ =>
    let a := unrestrictActionEquiv (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) e
    by_cases hF : 1 < F.degree
    · exact (hn (linearThree_large_isCompl s hi F hF a)).elim
    · have hdeg : F.degree = 1 := by have hp := F.degree_pos; omega
      let q := degreeOneNaturalEquiv F hdeg 3
      exact Or.inl ⟨⟨a.groupEquiv.trans q.groupEquiv, a.linearEquiv.trans q.linearEquiv,
        fun g v => (congrArg q.linearEquiv (a.intertwines g v)).trans
          (q.intertwines _ _)⟩⟩
  | symplectic F hF _ e hratio =>
    exact Or.inr ⟨F, hF, ⟨unrestrictActionEquiv le_sup_left e⟩, hratio⟩
  | binaryLinear d hd _ e _ =>
    exact (hn (binaryLinear_isCompl s hi (by rcases hd with rfl | rfl <;> decide)
      (unrestrictActionEquiv le_sup_left e))).elim
  | symplecticTwo e _ =>
    exact (symplecticTwo_commutator_ne_top (marked_same_eq_top e)).elim
  | symmetricEight _ e _ =>
    exact (alternating_ne_top 8 (by decide) (marked_same_eq_top e)).elim
  | linearTwo _ _ _ _ he =>
    rw [he] at hq
    exact (lt_irrefl _ hq).elim
  | g2 _ _ _ _ _ he =>
    rw [he] at hq
    exact (lt_irrefl _ hq).elim
  | g2Two _ _ he =>
    rw [he] at hq
    exact (lt_irrefl _ hq).elim
  | symmetric _ _ _ _ he =>
    rw [he] at hq
    exact (lt_irrefl _ hq).elim
  | alternatingSix _ _ _ he =>
    rw [he] at hq
    exact (lt_irrefl _ hq).elim
  | alternatingSeven _ _ _ _ _ he =>
    rw [he] at hq
    exact (lt_irrefl _ hq).elim
  | tripleSix _ _ he =>
    rw [he] at hq
    exact (lt_irrefl _ hq).elim
  | orthogonalSix _ _ _ _ he =>
    rw [he] at hq
    exact (lt_irrefl _ hq).elim
  | exteriorFive _ _ _ _ _ he =>
    rw [he] at hq
    exact (lt_irrefl _ hq).elim

/-- The natural binary three-dimensional component already fills GL3(2). -/
theorem sylow_le_of_binaryThree [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (T : Sylow 2 G)
    (hn : IsLinearNatural (s.action.comp L.subtype) BinaryField.two 3) :
    (T : Subgroup G) ≤ L := by
  let := h.finite_module
  obtain ⟨e⟩ := hn
  let D := L ⊔ (T : Subgroup G)
  let eL := (subgroupOfEquivOfLe (show L ≤ D from le_sup_left)).trans e.groupEquiv
  let p := BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)
  have hdim : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 3 := by
    have he := e.linearEquiv.finrank_eq
    change _ = Module.finrank (ZMod 2) (Fin 3 → ZMod 2) at he
    exact he.trans (Module.finrank_fin_fun (R := ZMod 2))
  have he := (BinaryLinearRecognition.natural_of_dimension
    (s.action.comp D.subtype) (local_faithful h s T T.isPGroup')
    (L.subgroupOf D) (by decide : 0 < 3) (eL.trans p.symm) hdim).1
  intro t ht
  have htD : t ∈ D := (le_sup_right : (T : Subgroup G) ≤ D) ht
  exact (show (⟨t, htD⟩ : D) ∈ L.subgroupOf D from he ▸ mem_top _)

/-- Source alpha in the binary-three branch. -/
theorem whole_of_binaryThree [Finite G] {K : CFSG.Quasithin.GroupClass}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L) (T : Sylow 2 G)
    (hn : IsLinearNatural (s.action.comp L.subtype) BinaryField.two 3) : L = ⊤ := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  apply whole_of_sylow_offenders_le ρ L T h.generated
  exact iSup₂_le fun A hA => hA.2.trans (sylow_le_of_binaryThree h s T hn)
end CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch

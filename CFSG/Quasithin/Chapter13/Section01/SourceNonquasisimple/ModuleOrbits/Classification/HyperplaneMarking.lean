module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.SymmetricMarking
public import Theory.Representation.BinaryFullLinearRecognition.Moved
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorPermutation

/-!
# The hyperplane product markings on the original moved module

The selected component lies in one of the two actual B.5.6(5) factors.
Simplicity identifies it with that factor. For the first factor, faithful
three-dimensional moved-space recognition gives natural SL3(2) coordinates.
The second factor supplies at most two natural copies, or a natural SL2
quotient by its own fixed vectors. The latter quotient is transported through
the original moved section and its central quotient, retaining all maps.

The literal source consumer constructs a full four-way marking in every
hyperplane branch. Together with the completed irreducible branches, this
leaves only B.5.6(3), whose decomposition is in the global fixed quotient.
No extra classification or component-placement premise is added.

Source: Aschbacher--Smith 13.1.10, pp.871--872; B.5.6(5), p.105.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
namespace ProductMarkings

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

theorem component_le_factor {A B C : Subgroup D}
    (d : InternalProduct A B) (hC : IsComponent D C) : C ≤ A ∨ C ≤ B := by
  let := d.swap.second_normal
  let := d.second_normal
  rcases hC.normal_dichotomy A with ha | ha
  · exact Or.inl ha
  rcases hC.normal_dichotomy B with hb | hb
  · exact Or.inr hb
  have hc : C ≤ centralizer ((A ⊔ B : Subgroup D) : Set D) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
  rw [d.sup_eq_top] at hc
  have hh : ⁅C,C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hc.trans (centralizer_le (show (C : Set D) ⊆ (⊤ : Subgroup D) from Set.subset_univ _)))
  let := hC.2
  rw [commutator_eq_self] at hh
  exact (hC.isCComponent.ne_bot hh).elim

theorem component_eq_of_simple_factor {A C : Subgroup D} [IsSimpleGroup A]
    (hC : IsComponent D C) (hCA : C ≤ A) : C = A := by
  have hc := hC.subgroupOf hCA
  have he := (hc.1.eq_bot_or_top_of_isSimpleGroup (inferInstance : IsSimpleGroup A)).resolve_left
    hc.isCComponent.ne_bot
  exact le_antisymm hCA (subgroupOf_eq_top.mp he)

/-- Equality of the original moved subspaces gives an equivariant identification. -/
def spaceActionEquiv {K A : Subgroup D} (s : MovedSection ρ K)
    (U : Subrepresentation ρ) (hKA : K = A) (hU : U.toSubmodule = moved ρ A) :
    ActionEquiv (s.space.toRepresentation.comp K.subtype) (U.toRepresentation.comp A.subtype) where
  groupEquiv := MulEquiv.subgroupCongr hKA
  linearEquiv := LinearEquiv.ofEq _ _ (s.space_eq.trans (hKA ▸ hU.symm))
  intertwines _ _ := Subtype.ext rfl

/-- Equivariant coordinates descend through the actual fixed-vector quotients. -/
def reducedEquiv {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) E W} (a : ActionEquiv ρ σ) :
    ActionEquiv (reducedAction ρ) (reducedAction σ) where
  groupEquiv := a.groupEquiv
  linearEquiv := Submodule.Quotient.equiv _ _ a.linearEquiv (by
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩ g
      obtain ⟨k,rfl⟩ := a.groupEquiv.surjective g
      change σ (a.groupEquiv k) (a.linearEquiv v) = a.linearEquiv v
      rw [← a.intertwines, hv]
    · intro w hw
      refine ⟨a.linearEquiv.symm w, ?_, a.linearEquiv.apply_symm_apply w⟩
      intro k
      apply a.linearEquiv.injective
      rw [a.intertwines, a.linearEquiv.apply_symm_apply, hw])
  intertwines g v := by
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact congrArg Submodule.Quotient.mk (a.intertwines g v)

/-- The section's central quotient is the fixed-vector quotient of its restricted action. -/
def sectionReducedEquiv {K : Subgroup D} (s : MovedSection ρ K) :
    ActionEquiv (s.action.comp K.subtype)
      (reducedAction (s.space.toRepresentation.comp K.subtype)) where
  groupEquiv := MulEquiv.refl _
  linearEquiv := Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (by
    change s.central.toSubmodule.map (LinearMap.id) = _
    rw [Submodule.map_id, s.central_eq]
    rfl)
  intertwines g v := by
    induction v using Submodule.Quotient.induction_on with
    | _ v => rfl

/-- A three-dimensional original moved space for SL3(2) is its natural module. -/
def threeMovedEquiv [Finite D] [FiniteDimensional (ZMod 2) V]
    {K : Subgroup D} (s : MovedSection ρ K)
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hd : Module.finrank (ZMod 2) (moved ρ K) = 3) :
    ActionEquiv (s.space.toRepresentation.comp K.subtype) (linearNatural BinaryField.two 3) := by
  let hh := BinaryFullLinearRecognition.binary_three_moved_normalizer_natural ρ K e hd
  let eg := hh.choose
  let f := hh.choose_spec.choose
  have hf := hh.choose_spec.choose_spec
  let c := (subgroupOfEquivOfLe K.le_normalizer).symm
  refine ⟨c.trans eg, (LinearEquiv.ofEq _ _ s.space_eq).trans f, ?_⟩
  intro k v
  exact hf (c k) ((LinearEquiv.ofEq _ _ s.space_eq) v)

end ProductMarkings

namespace ProductMarkings
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

omit [Finite D] in
/-- A component in a nonbinary SL2 factor is that factor; the binary endpoint is solvable. -/
theorem component_eq_linearTwo {A C : Subgroup D}
    (hC : IsComponent D C) (hCA : C ≤ A) (F : BinaryField)
    (e : A ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) : C = A := by
  by_cases hd : F.degree = 1
  · let es := e.trans ((ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
      ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
        BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
      (f := es.toMonoidHom) es.injective
    let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
      (f := inclusion hCA) (inclusion_injective hCA)
    let := hC.2
    let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
  · have hl : 3 < Nat.card F.Carrier := by
      rw [F.card_eq]
      have hd' : 2 ≤ F.degree := by have := F.degree_pos; omega
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hd'
      norm_num at hp
      omega
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F.Carrier) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    let : IsSimpleGroup A := (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL).isSimpleGroup
    exact component_eq_of_simple_factor hC hCA

omit [Finite D] in
theorem component_eq_binaryThree {A C : Subgroup D}
    (hC : IsComponent D C) (hCA : C ≤ A)
    (e : A ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : C = A := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup A :=
    (e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)).symm).isSimpleGroup
  exact component_eq_of_simple_factor hC hCA

omit [Finite D] in
/-- In the hyperplane case the selected component equals one of its actual factors. -/
theorem hyperplane_component_eq (d : HyperplaneCase ρ)
    {C : Subgroup D} (hC : IsComponent D C) : C = d.first ∨ C = d.second := by
  rcases component_le_factor d.product hC with hA | hB
  · exact Or.inl (component_eq_binaryThree hC hA d.firstEquiv)
  · right
    cases d.secondCase with
    | linearThree r hr hn =>
      obtain ⟨a⟩ := hn
      exact component_eq_binaryThree hC hB a.groupEquiv
    | linearTwo F hn =>
      obtain ⟨a⟩ := hn
      exact component_eq_linearTwo hC hB F a.groupEquiv

/-- One natural copy, with the same actor on its one-element index set. -/
def oneCopy {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W) : ActionEquiv σ (repeated σ 1) where
  groupEquiv := MulEquiv.refl _
  linearEquiv := {
    toFun := fun v _ => v
    invFun := fun v => v 0
    left_inv := fun _ => rfl
    right_inv := fun v => funext fun _ => congrArg v (Subsingleton.elim _ _)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  intertwines _ _ := rfl

/-- The hyperplane module alternatives retain either full coordinates on the
moved space or coordinates on its literal fixed quotient. -/
theorem hyperplane_component_actions [FiniteDimensional (ZMod 2) V]
    (d : HyperplaneCase ρ) {C : Subgroup D} (hC : IsComponent D C)
    (s : MovedSection ρ C) :
    (∃ r : ℕ, r ≤ 2 ∧ IsRepeatedLinearNatural
      (s.space.toRepresentation.comp C.subtype) BinaryField.two 3 r) ∨
    (∃ F : BinaryField, IsLinearNatural (s.action.comp C.subtype) F 2) := by
  rcases hyperplane_component_eq d hC with hA | hB
  · left
    have hd : Module.finrank (ZMod 2) (moved ρ C) = 3 := hA ▸ d.firstDimension
    let e := (MulEquiv.subgroupCongr hA).trans d.firstEquiv
    exact ⟨1, by decide, ⟨composeAction (threeMovedEquiv s e hd) (oneCopy _)⟩⟩
  · cases d.secondCase with
    | linearThree r hr hn =>
      obtain ⟨a⟩ := hn
      exact Or.inl ⟨r,hr,⟨composeAction (spaceActionEquiv s d.secondSpace hB d.secondSpace_eq) a⟩⟩
    | linearTwo F hn =>
      obtain ⟨a⟩ := hn
      exact Or.inr ⟨F,⟨composeAction (sectionReducedEquiv s)
        (composeAction (reducedEquiv (spaceActionEquiv s d.secondSpace hB d.secondSpace_eq)) a)⟩⟩
end ProductMarkings

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Any bounded repeated natural coordinates on the original component section
construct the literal case (3) marking. The nonzero original U excludes zero copies. -/
def repeatedThreeMarking
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (s : MovedSection
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))))
    {r : ℕ} (hr : r ≤ 2)
    (a : ActionEquiv (s.space.toRepresentation.comp
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))).subtype)
      (repeated (linearNatural BinaryField.two 3) r)) : LinearThreeMarking T L := by
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let c := CommonMarking.of_source h hmany hL hn hmove
  let d := composeAction (componentSectionEquiv h hmany hL hn hj s) a
  have hp : 0 < r := by
    by_contra! hn
    have hr0 : r = 0 := Nat.eq_zero_of_le_zero hn
    have hd := d.linearEquiv.finrank_eq
    rw [hr0] at hd
    have hz : Module.finrank (ZMod 2) (Additive (normalizerMoved L)) = 0 := by
      exact hd.trans (Module.finrank_zero_of_subsingleton (R := ZMod 2) (M := Fin 0 → Fin 3 → BinaryField.two.Carrier))
    let : Nontrivial (normalizerMoved L) := (Subgroup.nontrivial_iff_ne_bot _).mpr c.moved_ne_bot
    have : 0 < Module.finrank (ZMod 2) (Additive (normalizerMoved L)) := Module.finrank_pos
    omega
  exact ⟨c,⟨ZMod 2,inferInstance,inferInstance,by simp,
    ⟨d.groupEquiv.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)).symm⟩⟩,
    r,hp,hr,⟨d⟩⟩

/-- The two-rank of the selected component fixes the field in a linear-two row. -/
theorem selected_two_degree {D : Type*} [Group D] [Finite D]
    (F : BinaryField) (e : D ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
    (hr : primeRank 2 D = 2) : F.degree = 2 :=
  linearTwo_degree_of_two_rank F e hr

/-- B.5.6(5) constructs a full source marking on the original U, including
its central quotient in the SL2(4) alternative. -/
theorem hyperplane_marked
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (d : HyperplaneCase ((reducedRepresentation L).comp
      (offenderSubgroup (reducedRepresentation L)).subtype)) :
    Nonempty (FourWayMarking.{u,u} T L) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  let : IsElementaryAbelian 2 (normalizerMoved L) :=
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).1
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let C := (NormalizerReducedAction.componentImage L).subgroupOf
    (offenderSubgroup (reducedRepresentation L))
  let : (NormalizerReducedAction.componentImage L).Normal := reducedComponent_normal L
  let : C.Normal := inferInstance
  let s := MovedSection.ofNormal ((reducedRepresentation L).comp
    (offenderSubgroup (reducedRepresentation L)).subtype) C
  rcases ProductMarkings.hyperplane_component_actions d
      (reducedOffender_component h hmany hL hn hmove) s with ⟨r,hr,⟨a⟩⟩ | ⟨F,⟨a⟩⟩
  · exact ⟨.linearThree (repeatedThreeMarking h hmany hL hn hmove s hr a)⟩
  · let e := (subgroupOfEquivOfLe hj).trans (reducedImageEquivMovedImage h hmany hL hn)
    obtain ⟨p,hp,hp3,hm⟩ := moved_component_pslTwo h hmany hL hn
    have hr := (prime_model_ranks hp hp3 (hm.of_mulEquiv e)).1
    exact ⟨.pslTwoFour (irreducibleFourMarking h hmany hL hn hmove s F
      (selected_two_degree F a.groupEquiv hr) a)⟩

/-- All hyperplane and irreducible branches are discharged. Only the quotient
splitting in B.5.6(3) remains, on the same original representation. -/
theorem reducedOffender_marked_or_twoFactors
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    Nonempty (FourWayMarking.{u,u} T L) ∨
      Nonempty (SourceTwoFactorCase ((reducedRepresentation L).comp
        (offenderSubgroup (reducedRepresentation L)).subtype)) := by
  rcases reducedOffender_marked_or_products h hmany hL hn hmove with hm | hp
  · exact Or.inl hm
  · rcases hp with hd | hd
    · exact Or.inr hd
    · obtain ⟨d⟩ := hd
      exact Or.inl (hyperplane_marked h hmany hL hn hmove d)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification

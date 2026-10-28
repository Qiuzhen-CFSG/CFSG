module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentPair
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.PairComponentAlignment
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairModule
public import Theory.Representation.BinaryOffender.PerfectMoved

/-!
# Distinct components have separated supports in the B.5 product rows

In the two-factor row, a displacement of the first invariant space by a
perfect subgroup of the second factor lies in both source spaces. Their
images are disjoint modulo the global fixed space. The displacement is
therefore fixed, and perfectness kills it in the original module. This
retains the fixed kernel without asserting a splitting of the whole module.

The hyperplane row has disjoint original moved spaces. Its factor models
have unique components, so two distinct components occupy opposite factors.
Consequently both product alternatives give literal crossed centralization.
The actual common-action application is Catalogue/LocalSeparation in
Chapter 15. Source: Aschbacher--Smith B.5.6(3),(5), p.105, and C.1.16(3),
pp.125--126.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

private theorem moved_mono {A B : Subgroup D} (h : A ≤ B) : moved ρ A ≤ moved ρ B :=
  Submodule.span_mono (by rintro _ ⟨a,ha,v,hv,rfl⟩; exact ⟨a,h ha,v,hv,rfl⟩)

theorem SourceTwoFactorCase.firstSpace_fixed (d : SourceTwoFactorCase ρ)
    (B : Subgroup D) [Group.IsPerfect B] (hB : B ≤ d.second) :
    d.firstSpace.toSubmodule ≤ fixedSpace ρ B := by
  apply le_fixedSpace_of_commutator_le_fixedSpace ρ B _
    (le_subspaceStabilizer ρ _ (fun b _ v hv => d.firstSpace.apply_mem_toSubmodule b hv))
  intro v hv b
  have hv1 : v ∈ d.firstSpace.toSubmodule := by
    apply (Submodule.span_le.mpr ?_) hv
    rintro _ ⟨a,ha,w,hw,rfl⟩
    exact d.firstSpace.toSubmodule.sub_mem (d.firstSpace.apply_mem_toSubmodule a hw) hw
  have hv2 : v ∈ d.secondSpace.toSubmodule :=
    d.secondCase.moved_le_space (moved_mono hB
      (subspaceCommutator_mono_left ρ le_top B hv))
  have hz : ρ.invariants.mkQ v = 0 := Submodule.disjoint_def.mp d.decomposition.disjoint _
    ⟨v,hv1,rfl⟩ ⟨v,hv2,rfl⟩
  exact ((Submodule.Quotient.mk_eq_zero _).mp hz) b

theorem SourceTwoFactorCase.distinct_components_cross (d : SourceTwoFactorCase ρ)
    {A B : Subgroup D} (hA : IsComponent D A) (hB : IsComponent D B) (hne : A ≠ B) :
    moved ρ A ≤ fixedSpace ρ B := by
  let := hB.2
  rcases d.component_alignment hA hB hne with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact (moved_mono ha).trans (d.firstCase.moved_le_space.trans (d.firstSpace_fixed B hb))
  · let ds : SourceTwoFactorCase ρ :=
      ⟨d.second,d.first,d.product.swap,d.secondSpace,d.firstSpace,
        d.decomposition.symm,d.secondCase,d.firstCase⟩
    exact (moved_mono ha).trans (d.secondCase.moved_le_space.trans (ds.firstSpace_fixed B hb))

private theorem component_le_factor {A B C : Subgroup D}
    (h : InternalProduct A B) (hC : IsComponent D C) : C ≤ A ∨ C ≤ B := by
  let := h.swap.second_normal
  let := h.second_normal
  rcases hC.normal_dichotomy A with ha | ha
  · exact Or.inl ha
  rcases hC.normal_dichotomy B with hb | hb
  · exact Or.inr hb
  have hc : C ≤ centralizer ((A ⊔ B : Subgroup D) : Set D) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
  rw [h.sup_eq_top] at hc
  have hcc : ⁅C,C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hc.trans (centralizer_le (show (C : Set D) ⊆ (⊤ : Subgroup D) from Set.subset_univ _)))
  let := hC.2
  rw [commutator_eq_self] at hcc
  exact (hC.isCComponent.ne_bot hcc).elim

private theorem component_unique_quasisimple {E : Type*} [Group E] [IsQuasisimple E]
    {A B : Subgroup E} (hA : IsComponent E A) (hB : IsComponent E B) : A = B := by
  have ht : IsComponent E ⊤ :=
    ⟨(inferInstance : (⊤ : Subgroup E).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  exact (hA.eq_of_le ht le_top).trans (hB.eq_of_le ht le_top).symm

private theorem component_unique_binaryTwo (F : BinaryField)
    {E : Type*} [Group E] (e : E ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
    {A B : Subgroup E} (hA : IsComponent E A) (hB : IsComponent E B) : A = B := by
  by_cases hd : F.degree = 1
  · let e3 := e.trans
      ((ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
        ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
          BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable E := Group.isSolvable_of_isSolvable_injective
      (f := e3.toMonoidHom) e3.injective
    let := hA.2
    let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr hA.isCComponent.ne_bot
    exact (Group.IsPerfect.not_isSolvable A inferInstance).elim
  · have hfour : 3 < Nat.card F.Carrier := by
      rw [F.card_eq]
      have hh : 2 ≤ F.degree := by have := F.degree_pos; omega
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
      norm_num at hp
      omega
    let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :=
      { toIsPerfect := GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hfour
        simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega) }
    let : IsQuasisimple E := IsQuasisimple.of_mulEquiv e.symm
    exact component_unique_quasisimple hA hB

theorem HyperplaneCase.component_alignment (d : HyperplaneCase ρ)
    {A B : Subgroup D} (hA : IsComponent D A) (hB : IsComponent D B) (hne : A ≠ B) :
    (A ≤ d.first ∧ B ≤ d.second) ∨ (A ≤ d.second ∧ B ≤ d.first) := by
  have unique_first (ha : A ≤ d.first) (hb : B ≤ d.first) : False := by
    let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
      { toIsPerfect := Atlas.sl_perfect 3 (by decide)
        simple := Atlas.psl_simple_high_rank 3 (by decide) }
    let : IsQuasisimple d.first := IsQuasisimple.of_mulEquiv d.firstEquiv.symm
    have he := component_unique_quasisimple (hA.subgroupOf ha) (hB.subgroupOf hb)
    have hh := congrArg (map d.first.subtype) he
    rw [map_subgroupOf_eq_of_le ha,map_subgroupOf_eq_of_le hb] at hh
    exact hne hh
  have unique_second (ha : A ≤ d.second) (hb : B ≤ d.second) : False := by
    have he : A.subgroupOf d.second = B.subgroupOf d.second := by
      cases d.secondCase with
      | linearThree r hr hn =>
        obtain ⟨e⟩ := hn
        let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) BinaryField.two.Carrier) :=
          { toIsPerfect := Atlas.sl_perfect 3 (by decide)
            simple := Atlas.psl_simple_high_rank 3 (by decide) }
        let : IsQuasisimple d.second := IsQuasisimple.of_mulEquiv e.groupEquiv.symm
        exact component_unique_quasisimple (hA.subgroupOf ha) (hB.subgroupOf hb)
      | linearTwo F hn =>
        obtain ⟨e⟩ := hn
        exact component_unique_binaryTwo F e.groupEquiv (hA.subgroupOf ha) (hB.subgroupOf hb)
    have hh := congrArg (map d.second.subtype) he
    rw [map_subgroupOf_eq_of_le ha,map_subgroupOf_eq_of_le hb] at hh
    exact hne hh
  rcases component_le_factor d.product hA with ha | ha
  · rcases component_le_factor d.product hB with hb | hb
    · exact (unique_first ha hb).elim
    · exact Or.inl ⟨ha,hb⟩
  · rcases component_le_factor d.product hB with hb | hb
    · exact Or.inr ⟨ha,hb⟩
    · exact (unique_second ha hb).elim

private theorem moved_fixed_of_disjoint (A B : Subgroup D)
    (hcomm : ⁅A,B⁆ = ⊥) (hd : Disjoint (moved ρ A) (moved ρ B)) :
    moved ρ A ≤ fixedSpace ρ B := by
  have hn : B ≤ normalizer (A : Set D) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hs := subspaceCommutator_invariant_normalizer ρ
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hn
  intro v hv b
  apply sub_eq_zero.mp
  exact Submodule.disjoint_def.mp hd _
    ((moved ρ A).sub_mem ((hs b.property v).2 hv) hv)
    (Submodule.subset_span ⟨b,b.property,v,Submodule.mem_top,rfl⟩)

theorem HyperplaneCase.distinct_components_cross (d : HyperplaneCase ρ)
    {A B : Subgroup D} (hA : IsComponent D A) (hB : IsComponent D B) (hne : A ≠ B) :
    moved ρ A ≤ fixedSpace ρ B := by
  rcases d.component_alignment hA hB hne with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have hc := moved_fixed_of_disjoint d.first d.second d.product.commutator_eq_bot d.disjoint
    exact fun v hv b => hc (moved_mono ha hv) ⟨b,hb b.property⟩
  · have hc := moved_fixed_of_disjoint d.second d.first d.product.swap.commutator_eq_bot d.disjoint.symm
    exact fun v hv b => hc (moved_mono ha hv) ⟨b,hb b.property⟩

theorem AdequateAlternative.distinct_components_cross [Finite D] (h : AdequateAlternative ρ)
    {A B : Subgroup D} (hA : IsComponent D A) (hB : IsComponent D B) (hne : A ≠ B) :
    moved ρ A ≤ fixedSpace ρ B := by
  rcases AdequateAlternative.product_rows_of_two_components ρ h hA hB hne with hc | hc
  · obtain ⟨c⟩ := hc
    exact c.distinct_components_cross hA hB hne
  · obtain ⟨c⟩ := hc
    exact c.distinct_components_cross hA hB hne
end CFSG.Quasithin.ChapterB.SourceInduction

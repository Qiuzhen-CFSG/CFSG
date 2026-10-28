module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryActor
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SeedAction
public import Theory.Representation.SimpleHeadQuotient
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The actual chief quotient in the exchanged field-four branch

The component orbit moves every literal U/V₁ section. Consequently each
proper quotient remains noncentral, and the full exchanged actor acts
faithfully on it. Finite dimensionality supplies a maximal invariant
subspace; seed separation identifies the kernel on V as exactly V₁.

The final application constructs the original star action and quadratic
actor from the local source hypotheses. It retains the canonical quotient
coordinates, the actor's placement in R₁, and its fixed-codimension bound
on the selected faithful irreducible quotient. The same quadratic actor
also supplies the cubic-ratio bound needed by the abstract recognition.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1057, using
14.7.2(1) and 14.5.18, refs/quasithin.pdf. The orthogonal identification,
whole-module comparison and weak-closure contradiction remain subsequent
source steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
open ModuleAlternatives F918Sections F918Sections.NoStrong
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

variable
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
include d h hab structural previous faithful earlier hI hKI hK hnormal c

/-- Full commutator generation descends through the literal star map. -/
theorem local_nonnormal_component_star_moved :
    subspaceCommutator σ ⊤
      (Chapter13.Section08.Source.starImage F.H (conjugateSpanBy K (T : Subgroup G))) = ⊤ := by
  have hm := local_nonnormal_component_section_moved d h hab structural previous faithful earlier
    I K hI hKI hK hnormal c
  rw [← subspaceCommutator_top_eq_coinvariants,subspaceCommutator_comp_map] at hm
  exact hm

/-- Every proper quotient is faithful for the entire point-star group. -/
theorem local_nonnormal_component_quotient_faithful
    (A : Subrepresentation σ) (hA : A ≠ ⊤) :
    Function.Injective A.quotientRepresentation := by
  obtain ⟨t,ht,htn,k,hk,hfin,hchar,a,ha,hb,horbit,hS⟩ :=
    local_nonnormal_component_exchanged_actor d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  have hm := local_nonnormal_component_star_moved d h hab structural previous faithful earlier
    I K hI hKI hK hnormal σ c
  rw [← horbit] at hm
  exact a.faithful_of_noncentral A.quotientRepresentation
    (quotient_nontrivial_of_moved_eq_top σ a.orbit hm A hA)

/-- Select a faithful irreducible quotient while retaining the exact kernel on the seed. -/
theorem local_nonnormal_component_chief_quotient :
    ∃ A : Subrepresentation σ, IsCoatom A ∧ A.quotientRepresentation.IsIrreducible ∧
      Function.Injective A.quotientRepresentation ∧
      subspaceCommutator A.quotientRepresentation ⊤
        (Chapter13.Section08.Source.starImage F.H (conjugateSpanBy K (T : Subgroup G))) = ⊤ ∧
      ∀ v : F.U, (v : G) ∈ V →
        (A.toSubmodule.mkQ (c.coordinates v).toAdd = 0 ↔ (v : G) ∈ F.Vi 1) := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (c.coordinates v).toAdd)
    (fun w => c.onto (Multiplicative.ofAdd w))
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  have hVn : ¬ V ≤ F.Vi 1 := by
    intro hv
    have hc := card_le_of_le hv
    have hV : Nat.card V = 8 := by simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    have hP : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    omega
  obtain ⟨v,hv,hvp⟩ := SetLike.not_le_iff_exists.mp hVn
  let vU : F.U := ⟨v,le_conjugateSpanBy V F.H hv⟩
  have hv0 : (c.coordinates vU).toAdd ≠ 0 := by
    intro he
    exact hvp ((c.coordinates_eq_one_iff vU).mp he)
  let : Nontrivial W := ⟨⟨(c.coordinates vU).toAdd,0,hv0⟩⟩
  let : IsCoatomic (Subrepresentation σ) := SimpleHeadQuotient.subrepresentation_coatomic σ
  obtain ⟨A,hA,_⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation σ)).resolve_left bot_ne_top
  refine ⟨A,hA,SimpleHeadQuotient.irreducible_quotient_of_isCoatom A hA,
    local_nonnormal_component_quotient_faithful d h hab structural previous faithful earlier
      I K hI hKI hK hnormal σ c A hA.1,?_,?_⟩
  · have hm := local_nonnormal_component_star_moved d h hab structural previous faithful earlier
      I K hI hKI hK hnormal σ c
    have hq := quotient_seed_commutator σ A ⊤ _ hm
    simpa only [Submodule.map_top,Submodule.range_mkQ] using hq
  · intro v hv
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact seed_intersection h c A.toSubmodule
      (fun g w hw => A.apply_mem_toSubmodule (starMap F g) hw)
      (fun he => hA.1 (Subrepresentation.toSubmodule_injective he)) v hv

open Chapter15.Section03.AbelianAmalgam

private def localQuotientSection [IsElementaryAbelian 2 F.U]
    (a : LocalQuotientAction F.H F.U (F.Vi 1)) :
    BinaryConjugationSection F.H F.U (F.Vi 1) (a.representation.comp (starMap F)) where
  section_le := a.le_local
  kernel_le := a.kernel_le
  normalized := a.normalizes
  coordinates := {
    toFun := fun u => Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U) u))
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  onto := by
    intro v
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective ((F.Vi 1).subgroupOf F.U) v.toAdd.toMul
    exact ⟨u,congrArg (fun w => Multiplicative.ofAdd (Additive.ofMul w)) hu⟩
  kernel_eq := by
    ext u
    exact QuotientGroup.eq_one_iff u
  equivariant := fun g u => (a.conjugation g u).symm

omit c in
/-- Construct the actual source action, chief quotient and quadratic actor
on the same literal U/V₁. No recognition premise is supplied. -/
theorem local_nonnormal_component_quadratic_chief :
    ∃ hU : IsElementaryAbelian 2 F.U,
      letI := hU
      ∃ a : LocalQuotientAction F.H F.U (F.Vi 1),
      ∃ A : Subrepresentation a.representation,
        IsCoatom A ∧ A.quotientRepresentation.IsIrreducible ∧
        Function.Injective A.quotientRepresentation ∧
        subspaceCommutator A.quotientRepresentation ⊤
          (Chapter13.Section08.Source.starImage F.H (conjugateSpanBy K (T : Subgroup G))) = ⊤ ∧
        (∀ v : F.U, (v : G) ∈ V →
          (A.toSubmodule.mkQ (Additive.ofMul
              (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U) v)) = 0 ↔
            (v : G) ∈ F.Vi 1)) ∧
        cubicRatio A.quotientRepresentation ≤ 2 ∧
        ∃ B : Subgroup F.H, B ≤ (F.Ri L 1).subgroupOf F.H ∧
          IsElementaryTwo (B.map (starMap F)) ∧
          IsQuadratic A.quotientRepresentation (B.map (starMap F)) ∧
          fixedCodim A.quotientRepresentation (B.map (starMap F)) ≤
            2 * rank (B.map (starMap F)) := by
  obtain ⟨t,ht,htn,k,hk,hfin,hchar,e,he1,he2,horbit,hS⟩ :=
    local_nonnormal_component_exchanged_actor d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  let := e.orbit_normal
  have hgen : e.orbit ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf F.H).map
      (starMap F) = ⊤ := by
    apply top_unique
    rw [← e.generated]
    apply sup_le_sup_left
    rw [hS]
    exact map_mono (subgroupOf_mono F.H le_sup_right)
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  obtain ⟨hU,a,_,B,hBR,hB,hquad,hcod,_⟩ :=
    local_prime_supplement_quadratic_actor h hab structural previous F.H hH e.orbit hgen
  change IsElementaryAbelian 2 F.U at hU
  let := hU
  change LocalQuotientAction F.H F.U (F.Vi 1) at a
  let c := localQuotientSection hab a
  obtain ⟨A,hA,hirr,hfaith,hfull,hseed⟩ :=
    local_nonnormal_component_chief_quotient d h hab structural previous faithful earlier
      I K hI hKI hK hnormal a.representation c
  have hq : IsQuadratic A.quotientRepresentation (B.map (starMap F)) :=
    quadratic_of_equivariant_surjection a.representation A.quotientRepresentation
      A.toSubmodule.mkQ A.toSubmodule.mkQ_surjective
      (fun g v => (A.quotientRepresentation_mk g v).symm) _ hquad
  have hb : fixedCodim A.quotientRepresentation (B.map (starMap F)) ≤
      2 * rank (B.map (starMap F)) := by
    have hh := fixedCodim_quotient_add_subrepresentation_le a.representation A (B.map (starMap F))
    exact (Nat.le_add_right _ _).trans (hh.trans hcod)
  have hcoords (v : F.U) : (c.coordinates v).toAdd =
      Additive.ofMul (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U) v) := by
    rfl
  exact ⟨hU,a,A,hA,hirr,hfaith,hfull,(by simpa only [hcoords] using hseed),
    (cubicRatio_le_nat_iff _ 2).mpr ⟨B.map (starMap F),hB,isCubic_of_isQuadratic hq,hb⟩,
    B,hBR,hB,hq,hb⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.IntrinsicCore
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.FrattiniSections
public import Theory.SpecificGroups.SL3.ExceptionalFourKernel

/-!
# Exceptional kernel restrictions on nonbinary linear-three MS cores

The literal quotient K/[O₂(K),K] is a perfect central cover of the supplied
full SL₃. Outside field four its kernel is trivial. At field four the universal
cover bounds give order dividing sixteen, at most two generators and exponent
dividing four. The same bounds apply to the component images on the entire
central section and the entire Frattini quotient.

Consequently the index of the actual MS commutator in O₂(K) divides sixteen.
Every fourth power from O₂(K) belongs to that commutator, centralizes its whole
center and acts trivially on its whole Frattini quotient. No abelianity, whole
section model, or fixed-factor ambient-centrality premise is used. The original
nonblock application retains its actual Q, U and full quotient marking.

These are restrictions on the remaining field-four descent obstruction. They
do not eliminate that obstruction or prove the whole-section alternatives.
Source: Aschbacher--Smith C.1.34, pp.136--137, I.1.3(6), p.407, and original
4.3.8--10, pp.616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ExceptionalKernel
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)

include h in
omit [Finite G] in
private theorem component_perfect : Group.IsPerfect K := by
  let := h.component.2.perfect
  let e : K.subgroupOf (K ⊔ R) ≃* K := subgroupOfEquivOfLe le_sup_left
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

include h hn in
omit [Finite G] in
private theorem cover_bounds {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E SL(3,F)) :
    Nat.card f.toMonoidHom.ker ∣ 16 ∧ Group.rank f.toMonoidHom.ker ≤ 2 ∧
      ∀ x : f.toMonoidHom.ker, x ^ 4 = 1 := by
  by_cases hn2 : n = 2
  · apply Matrix.SL3.ExceptionalFourKernel.kernel_bounds (by rw [h.field_card,hn2]; rfl) f
  · let := f.isPerfect
    have hF2 : Nat.card F ≠ 2 := by
      rw [h.field_card]
      have hh : 2^1 < 2^n := Nat.pow_lt_pow_right (by decide) hn
      omega
    have hF4 : Nat.card F ≠ 4 := by
      rw [h.field_card]
      have hh : 2^2 < 2^n := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
    obtain ⟨a,ha,_⟩ := Matrix.PSL3.OrdinaryCenterRecognition.exists_scalar_lift
      hF2 hF4 f.quotientCenterEquiv
    have hi : Function.Injective f.toMonoidHom :=
      (f.surjective.bijective_of_nat_card_le (Nat.card_le_card_of_surjective a ha)).1
    have hz := (MonoidHom.ker_eq_bot_iff _).mpr hi
    let : Subsingleton f.toMonoidHom.ker := by rw [hz]; infer_instance
    refine ⟨by rw [hz,Subgroup.card_bot]; exact one_dvd 16,
      by simp [Group.rank_eq_zero],?_⟩
    intro x
    exact Subsingleton.elim _ _

include h hn

/-- The intrinsic core differs from the original MS commutator by an index
dividing sixteen. This includes field four and nonabelian cores. -/
theorem componentCore_index_dvd : (msQ K R).relIndex (K.pCoreIn 2) ∣ 16 := by
  let := component_perfect h
  let e := Classical.choice h.model
  have hb := (cover_bounds h hn (Matrix.SL3.PerfectCore.cover e)).1
  rw [Matrix.SL3.PerfectCore.cover_kernel] at hb
  rw [←IntrinsicCore.blockU_map_eq_msQ h hn]
  change ((blockU K).map K.subtype).relIndex ((pCore 2 K).map K.subtype) ∣ 16
  rw [relIndex_map_map_of_injective _ _ K.subtype_injective]
  change (⁅pCore 2 K,(⊤ : Subgroup K)⁆ : Subgroup K).relIndex (pCore 2 K) ∣ 16
  rw [←QuotientGroup.ker_mk' (⁅pCore 2 K,(⊤ : Subgroup K)⁆ : Subgroup K),relIndex_ker]
  exact hb

/-- Every fourth power in the intrinsic two-core lies in the actual MS
commutator. This controls the exceptional field-four residual kernel. -/
theorem componentCore_fourth_mem (x : G) (hx : x ∈ K.pCoreIn 2) :
    x ^ 4 ∈ msQ K R := by
  let := component_perfect h
  let e := Classical.choice h.model
  let D := (⁅pCore 2 K,(⊤ : Subgroup K)⁆ : Subgroup K)
  let f := Matrix.SL3.PerfectCore.cover e
  obtain ⟨k,hk,rfl⟩ := hx
  have hq : QuotientGroup.mk' D k ∈ f.toMonoidHom.ker := by
    rw [Matrix.SL3.PerfectCore.cover_kernel]
    exact mem_map_of_mem _ hk
  have hp := congrArg Subtype.val ((cover_bounds h hn f).2.2 ⟨_,hq⟩)
  have hk4 : k ^ 4 ∈ D := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' D (k ^ 4) = 1
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,←map_pow] using hp
  rw [←IntrinsicCore.blockU_map_eq_msQ h hn]
  exact mem_map_of_mem K.subtype hk4

variable [CharP F 2]

/-- The literal action on the entire central section has an exceptional
kernel of order dividing sixteen, rank at most two, and exponent at most four.
No whole-section model or ambient-centrality assertion is used. -/
theorem sectionCover_kernel_bounds (X : Subgroup G)
    (hXn : (K ⊔ R : Subgroup G) ≤ normalizer (X : Set G))
    (hUX : initialMoved K R ≤ X) (hXQ : X ≤ centralizer (msQ K R : Set G))
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    let f := CentralSections.sectionCover h hn X hXn hUX hXQ e
    Nat.card f.toMonoidHom.ker ∣ 16 ∧ Group.rank f.toMonoidHom.ker ≤ 2 ∧
      ∀ x : f.toMonoidHom.ker, x ^ 4 = 1 := by
  let a := (CentralSections.sectionAction X hXn).comp (K.subgroupOf (K ⊔ R)).subtype
  let : Finite a.range := Finite.of_surjective _ a.rangeRestrict_surjective
  exact cover_bounds h hn (CentralSections.sectionCover h hn X hXn hUX hXQ e)

/-- The full Frattini action satisfies the same bounds on its original
marked projection, including when the whole core is nonabelian. -/
theorem frattiniCover_kernel_bounds (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    let f := FrattiniSections.frattiniCover h hn e
    Nat.card f.toMonoidHom.ker ∣ 16 ∧ Group.rank f.toMonoidHom.ker ≤ 2 ∧
      ∀ x : f.toMonoidHom.ker, x ^ 4 = 1 := by
  let a := (FrattiniSections.frattiniAction h hn).comp (K.subgroupOf (K ⊔ R)).subtype
  let : Finite a.range := Finite.of_surjective _ a.rangeRestrict_surjective
  exact cover_bounds h hn (FrattiniSections.frattiniCover h hn e)

omit [CharP F 2] in
/-- Fourth powers of the intrinsic two-core centralize the whole center. -/
theorem fourth_centralizes_center (x : G) (hx : x ∈ K.pCoreIn 2) :
    x ^ 4 ∈ centralizer (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
      (msQ K R) : Set G) := by
  rintro z ⟨z,hz,rfl⟩
  exact (congrArg (msQ K R).subtype
    (mem_center_iff.mp hz ⟨x^4,componentCore_fourth_mem h hn x hx⟩)).symm

omit [CharP F 2] in
/-- The original two-core acts on the full Frattini quotient with exponent
at most four. The action is the literal conjugation quotient action. -/
theorem frattiniAction_fourth (x : K) (hx : x ∈ pCore 2 K) :
    (FrattiniSections.frattiniAction h hn ⟨x,mem_sup_left x.property⟩) ^ 4 = 1 := by
  rw [←map_pow]
  apply FrattiniSections.core_le_frattiniAction_kernel h hn
  have hm := componentCore_fourth_mem h hn x (mem_map_of_mem K.subtype hx)
  rw [←commutator_map_eq_msQ] at hm
  exact (mem_map_iff_mem (K ⊔ R : Subgroup G).subtype_injective).mp hm

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ExceptionalKernel

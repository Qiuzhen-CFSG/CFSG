module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AlternatingSixSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AlternatingSevenSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearFourSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MathieuSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ModelSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SourceInduction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.SmallLinear
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.InnerAction.Models
/-! The complete model-valued part of original 2.5.2 on a selected component.
The proved universal 1.1.5 classification supplies all six model-action cases.
The original empty-Gamma local arguments exclude A6 transpositions, A7 and
its triple cover, L4(2), and every M22/M23 cover. The checked Lie and sporadic
block inspections leave exactly the source's four non-Bender model families.
Every field and quotient is transported literally to the descent interface.
Only the independent earlier C.1.29 local block implication remains explicit.
Source: Aschbacher--Smith 2.3.9(7), 2.5.2, pp.525--526,551. -/
public section
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement ClassificationModels
open Chapter15.Section03.Candidates.ComponentStructure
open Chapter1.Section02.LocalModels ChapterA.Section02
variable {G : Type*} [Group G] [Finite G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem sourceLieModel {K : Type*} [Group K] (h : LieTypeTwoModel K) : LieType.SimpleLieModel K := by
  rcases h with h | h | h
  · exact .inl h
  · apply Or.inr ∘ Or.inl
    cases h with
    | linear f hf hm => exact ⟨f,.linear hf hm⟩
    | symplectic f hf hm => exact ⟨f,.symplectic hf hm⟩
    | g2 f hf hm => exact ⟨f,.g2 hf hm⟩
    | triality f hf hm => exact ⟨f,.triality hf hm⟩
    | ree m hm model =>
      obtain ⟨d,⟨e⟩⟩ := model
      exact ⟨2*m+1,.ree_f4 m hm rfl ⟨e.trans d.modelEquiv⟩⟩
    | symplectic_derived hm => exact ⟨1,.symplectic_derived rfl hm⟩
    | g2_derived hm => exact ⟨1,.g2_derived rfl hm⟩
    | tits hm => exact ⟨1,.tits rfl hm⟩
  · exact .inr (.inr h)

private theorem even_linear_of_central_map {K : Type*} [Group K]
    (F : Type) [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F=2^n)
    (f : K →* PSL(3,F)) (hf : Function.Surjective f) (hk : f.ker ≤ center K) :
    IsEvenLinearThreeCover K := by
  let := Atlas.sl_perfect (F := F) 3 (by decide)
  have htarget : center PSL(3,F)=⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot (Matrix.SpecialLinearGroup (Fin 3) F)
  have hc : center K=f.ker := by
    apply le_antisymm _ hk
    intro x hx
    have hh : f x ∈ center PSL(3,F) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨a,rfl⟩ := hf y
      simpa only [map_mul] using congrArg f (mem_center_iff.mp hx a)
    rwa [htarget,mem_bot] at hh
  exact ⟨F,inferInstance,inferInstance,n,hn,hF,
    ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩⟩

private theorem even_linear_of_model {K : Type*} [Group K] {n : ℕ} (hn : 1 ≤ n)
    (hm : ClassicalGroup.IsPSL K 3 (2^n)) : IsEvenLinearThreeCover K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact even_linear_of_central_map F hn hF e.toMonoidHom e.surjective
    (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact bot_le)

omit [Finite G] in
private theorem even_linear_of_core_quotient (h : LocalSetup H L M S z)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4) : IsEvenLinearThreeCover L := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let f := h.componentQuotientCover e
  exact even_linear_of_central_map F (n := 2) (by decide) hF f.toMonoidHom f.surjective f.ker_le_center

omit [Finite G] in
private theorem derived_symplectic (h : LieType.IsDerivedSymplecticFour L) : IsDerivedSymplecticFour L := by
  obtain ⟨n,hn,F,_,_,hF,he⟩ := h
  exact ⟨F,inferInstance,inferInstance,n,hn,hF,he⟩

private theorem lie_models (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅) (h : LocalSetup H L M S z)
    [IsSimpleGroup L] (α : MulAut L) (hα : ∀x:L,(α x:G)=z*(x:G)*z⁻¹)
    (hm : LieTypeTwoModel L) (hi : α ∈ (MulAut.conj (G := L)).range)
    (hb : ¬ IsBenderModel L) : IsDerivedSymplecticFour L ∨ IsEvenLinearThreeCover L := by
  rcases LieType.refinement_of_inner_action h (sourceLieModel hm) α hα hi with hb' | hB | hG
  · exact (hb hb').elim
  · rcases hB with hB | ⟨n,hn,hm⟩ | hB | ⟨_,hc,_⟩
    · exact .inl (derived_symplectic hB)
    · exact .inr (even_linear_of_model hn hm)
    · exact .inr (even_linear_of_core_quotient h hB)
    · let := h.quasisimple
      rw [center_eq_bot_of_simple_perfect,card_bot] at hc
      omega
  · obtain ⟨e,_,t,ht,_⟩ := hG
    exact (linear_four_two_false hH hempty h e ⟨t,ht⟩).elim

theorem MathieuSourceSetup.nonBender_model
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hb : ¬ IsBenderModel L) :
    IsDerivedSymplecticFour L ∨ IsEvenLinearThreeCover L ∨
      (Nonempty (L ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (L ≃* Sporadic.Mathieu.M11)) ∨
      IsLargePrimeLinear L := by
  let h := c.localSetup hG structural115Input sourceC
  obtain ⟨α,hα,hm⟩ := c.modelAction115_knownSimple hG
  cases hm with
  | lie hs hm hi =>
    let := hs
    rcases lie_models c.gamma hempty h α hα hm hi hb with hm | hm
    · exact .inl hm
    · exact .inr (.inl hm)
  | two_cover hn hc hm hi =>
    have hinner : ∃ t:L, IsConjugationProjection L z t := by
      obtain ⟨t,rfl⟩ := hi
      exact ⟨t,fun x => (hα x).symm⟩
    rcases hm with hm | hm
    · exact .inr (.inl (even_linear_of_core_quotient h hm))
    · obtain ⟨F,_,_,hF,he⟩ := hm
      exact (LieType.G2.not_central_quotient_model h hinner hc (hc ▸ hn) F hF he).elim
  | six σ hσ ha => exact (alternating_six_action_false c.gamma hempty h α hα σ hσ ha).elim
  | seven σ hσ ha => exact (alternating_seven_action_false c.gamma hempty h α hα σ hσ ha).elim
  | odd hm _ =>
    rcases hm with hm | ⟨p,hp,hm⟩
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : Fintype F := Fintype.ofFinite F
      let f : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
      exact .inr (.inr (.inl (.inl ⟨e.trans (Atlas.fieldEquivPSL 3 f)⟩)))
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : Fact p.Prime := ⟨hp.1⟩
      let : Fintype F := Fintype.ofFinite F
      let f : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
      let e' := e.trans (Atlas.fieldEquivPSL 2 f)
      rcases h.linearPrime_small_alternatives p e' with ⟨he,_⟩ | ⟨_,⟨e7⟩⟩ | hlarge
      · exact (hb (BenderFusion.InnerActionModels.bender_model_of_psl2_five F (hF.trans he) e)).elim
      · exact .inr (.inl (even_linear_of_central_map (ZMod 2) (n := 1) (by decide)
          (by simp) e7.toMonoidHom e7.surjective (by rw [e7.toMonoidHom.ker_eq_bot e7.injective]; exact bot_le)))
      · exact .inr (.inr (.inr ⟨p,hp,hlarge,⟨e'⟩⟩))
  | sporadic name hn hm hi =>
    obtain ⟨e⟩ := hm
    exact .inr (.inr (.inl (.inr (sporadic_model_of_emptyGamma c hG sourceC hempty hn
      ⟨e,α,hα,hi.1⟩))))
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection

module

public import Theory.Representation.SL2SylowFixedRecognition.Definitions
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.Representation.BinaryOffender.ComponentPermutationObstruction
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.GeneratedSubgroupInvariants
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration

/-!
# Complementary fixed spaces on the central quotient

Uniform fixed spaces make the defining-characteristic Sylow quadratic.
Gaschütz gives full movement on the literal central quotient, and perfectness
prevents new global fixed vectors. Two generating Sylows then have
complementary fixed spaces. No splitting of the original module is asserted.

Source: Aschbacher--Smith, G.1.6, printed p.329.
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup Representation.BinaryOffender
namespace Representation.SL2SylowFixedRecognition

section General
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Full movement passes through a surjection whose kernel supplements the
moving space. This does not require an invariant complement to the kernel. -/
theorem moved_eq_top_of_surjection (ρ : Representation (ZMod 2) G V)
    (σ : Representation (ZMod 2) G W) (f : V →ₗ[ZMod 2] W)
    (hf : Function.Surjective f) (he : ∀ g v, f (ρ g v) = σ g (f v))
    (hs : subspaceCommutator ρ ⊤ ⊤ ⊔ LinearMap.ker f = ⊤) :
    subspaceCommutator σ ⊤ ⊤ = ⊤ := by
  have hm : subspaceCommutator ρ ⊤ ⊤ ≤ (subspaceCommutator σ ⊤ ⊤).comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    change f (ρ g v - v) ∈ subspaceCommutator σ ⊤ ⊤
    rw [map_sub,he]
    exact Submodule.subset_span ⟨g,hg,f v,Submodule.mem_top,rfl⟩
  apply top_unique
  intro w _
  obtain ⟨v,rfl⟩ := hf w
  have hv : v ∈ subspaceCommutator ρ ⊤ ⊤ ⊔ LinearMap.ker f := by rw [hs]; exact Submodule.mem_top
  obtain ⟨a,ha,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add,LinearMap.mem_ker.mp hz,add_zero]
  exact hm ha

/-- Quadraticity is preserved by conjugating the actor subgroup. -/
theorem quadratic_conjugate (ρ : Representation (ZMod 2) G V)
    {A : Subgroup G} (hA : IsQuadratic ρ A) (g : G) :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
  change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) = ρ (g * b * g⁻¹) v - v
  have h := congrArg (ρ g) (hA a ha b hb (ρ g⁻¹ v))
  simpa only [map_mul,Module.End.mul_apply,map_sub,ρ.inv_self_apply,ρ.self_inv_apply] using h

/-- Two quadratic generating subgroups give complementary fixed spaces in a
fully moved module with no global fixed vectors. -/
theorem isCompl_fixedSpace_of_quadratic_generators
    (ρ : Representation (ZMod 2) G V) (A B : Subgroup G)
    (hgen : A ⊔ B = ⊤) (hA : IsQuadratic ρ A) (hB : IsQuadratic ρ B)
    (hmoved : subspaceCommutator ρ ⊤ ⊤ = ⊤) (hfixed : fixedSpace ρ ⊤ = ⊥) :
    IsCompl (fixedSpace ρ A) (fixedSpace ρ B) := by
  have hmove (C : Subgroup G) (hC : IsQuadratic ρ C) :
      subspaceCommutator ρ ⊤ C ≤ fixedSpace ρ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c,hc,v,_,rfl⟩ a
    exact hC a a.property c hc v
  have hi : fixedSpace ρ A ⊓ fixedSpace ρ B = ⊥ := by
    have he : fixedSpace ρ (A ⊔ B) = fixedSpace ρ A ⊓ fixedSpace ρ B :=
      ρ.invariants_comp_sup A B
    rw [← he,hgen]
    exact hfixed
  have hs : subspaceCommutator ρ ⊤ A ⊔ subspaceCommutator ρ ⊤ B = ⊤ := by
    have he := BinaryGroupAction.moved_iSup ρ (fun b : Bool => if b then A else B)
    simp only [iSup_bool_eq,Bool.false_eq_true,↓reduceIte] at he
    rw [hgen,hmoved] at he
    exact he.symm
  refine ⟨disjoint_iff.mpr hi,codisjoint_iff.mpr (top_unique ?_)⟩
  rw [← hs]
  exact sup_le_sup (hmove A hA) (hmove B hB)
end General

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Uniformity on nonidentity Sylow elements makes the entire Sylow quadratic. -/
theorem FixedSpaceHypotheses.quadratic {ρ : Representation (ZMod 2) SL(2,F) V}
    {R : Sylow 2 SL(2,F)} (h : FixedSpaceHypotheses ρ R) : IsQuadratic ρ R := by
  intro a ha b hb v
  by_cases hb1 : b = 1
  · simp [hb1]
  have h2 : b * b = 1 := by
    have hh := Matrix.SpecialLinearGroup.twoSubgroup_pow_two
      (R : Subgroup SL(2,F)) R.isPGroup' ⟨b,hb⟩
    exact congrArg (fun x : R => (x : SL(2,F))) (by simpa only [pow_two] using hh)
  have hv : ρ b v - v ∈ fixedSpace ρ (zpowers b) :=
    (mem_fixedSpace_zpowers_iff ρ b _).mpr (involution_fixes_displacement ρ h2 v)
  rw [h.uniform b hb hb1] at hv
  exact hv ⟨a,ha⟩

omit [CharP F 2] in
/-- Binary SL₂ of field size at least four is perfect. -/
theorem perfect (hcard : 4 ≤ Nat.card F) : Group.IsPerfect SL(2,F) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hex : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
    by_contra hn
    push Not at hn
    have hs : (Finset.univ : Finset F) ⊆ {0,1,-1} := by
      intro a _
      by_cases ha : a = 0
      · simp [ha]
      rcases sq_eq_one_iff.mp (hn a ha) with h | h <;> simp [h]
    have hthree : ({0,1,-1} : Finset F).card ≤ 3 := by
      exact (Finset.card_insert_le _ _).trans (by
        have := Finset.card_insert_le (1 : F) {-1}
        simpa using Nat.add_le_add_right this 1)
    have hc : Nat.card F ≤ 3 := by
      simpa only [Finset.card_univ,← Nat.card_eq_fintype_card] using
        (Finset.card_le_card hs).trans hthree
    omega
  obtain ⟨a,ha,hs⟩ := hex
  exact ⟨Matrix.SL2.commutator_eq_top ha hs⟩

omit [CharP F 2] in
/-- Perfectness prevents new global fixed vectors in the literal central quotient. -/
theorem centralQuotient_fixed_eq_bot (ρ : Representation (ZMod 2) SL(2,F) V)
    (hcard : 4 ≤ Nat.card F) : fixedSpace (centralQuotient ρ) ⊤ = ⊥ := by
  let : Group.IsPerfect SL(2,F) := perfect hcard
  let Z := fixedSpace ρ ⊤
  let W := (fixedSpace (centralQuotient ρ) ⊤).comap Z.mkQ
  have hW : (⊤ : Subgroup SL(2,F)) ≤ subspaceStabilizer ρ W := by
    apply le_subspaceStabilizer
    intro g hg v hv
    change Z.mkQ (ρ g v) ∈ fixedSpace (centralQuotient ρ) ⊤
    rw [← centralQuotient_mk]
    rw [show centralQuotient ρ g (Z.mkQ v) = Z.mkQ v from hv ⟨g,hg⟩]
    exact hv
  have hC : subspaceCommutator ρ W ⊤ ≤ Z := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    apply (Submodule.Quotient.eq Z).mp
    exact hv ⟨g,hg⟩
  have hWZ := le_fixedSpace_of_commutator_le_fixedSpace ρ ⊤ W hW hC
  apply bot_unique
  intro q hq
  obtain ⟨v,rfl⟩ := Z.mkQ_surjective q
  exact (Submodule.Quotient.mk_eq_zero Z).mpr (hWZ hq)

omit [CharP F 2] in
/-- The literal central quotient is fully moved. -/
theorem centralQuotient_moved_eq_top (ρ : Representation (ZMod 2) SL(2,F) V)
    (R : Sylow 2 SL(2,F)) (h : FixedSpaceHypotheses ρ R) :
    subspaceCommutator (centralQuotient ρ) ⊤ ⊤ = ⊤ := by
  apply moved_eq_top_of_surjection ρ (centralQuotient ρ) (fixedSpace ρ ⊤).mkQ
    (fixedSpace ρ ⊤).mkQ_surjective (fun g v => (centralQuotient_mk ρ g v).symm)
  rw [Submodule.ker_mkQ]
  exact moved_sup_fixed ρ R h

/-- The quadratic action of any Sylow survives the central quotient. -/
theorem centralQuotient_quadratic (ρ : Representation (ZMod 2) SL(2,F) V)
    (R : Sylow 2 SL(2,F)) (h : FixedSpaceHypotheses ρ R) (S : Sylow 2 SL(2,F)) :
    IsQuadratic (centralQuotient ρ) S := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) R S
  have hq := quadratic_conjugate ρ h.quadratic g
  intro a ha b hb v
  obtain ⟨v,rfl⟩ := (fixedSpace ρ ⊤).mkQ_surjective v
  have he := congrArg (fixedSpace ρ ⊤).mkQ (hq a ha b hb v)
  simpa only [map_sub,centralQuotient_mk] using he

/-- The complementary-fixed-space conclusion needed before applying G.1.7.
The original Sylow and the original quotient map are retained. -/
theorem centralQuotient_exists_complement (ρ : Representation (ZMod 2) SL(2,F) V)
    (R : Sylow 2 SL(2,F)) (h : FixedSpaceHypotheses ρ R)
    (d : ℕ) (hd : 2 ≤ d) (hF : Nat.card F = 2 ^ d) :
    ∃ S : Sylow 2 SL(2,F),
      IsCompl (fixedSpace (centralQuotient ρ) R) (fixedSpace (centralQuotient ρ) S) := by
  have hc : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 4 = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by decide) hd
  have hn : normalizer (R : Set SL(2,F)) ≠ ⊤ := by
    intro he
    exact Matrix.SpecialLinearGroup.no_normal_sylow F 2 R (normalizer_eq_top_iff.mp he)
  obtain ⟨g,hg⟩ := SetLike.exists_not_mem_of_ne_top (normalizer (R : Set SL(2,F))) hn
  refine ⟨g • R,?_⟩
  apply isCompl_fixedSpace_of_quadratic_generators
    (centralQuotient ρ) (R : Subgroup SL(2,F)) (g • R : Sylow 2 SL(2,F))
    (Matrix.SpecialLinearGroup.sylow_sup_conjugate_eq_top_of_not_mem_normalizer R hg)
    (centralQuotient_quadratic ρ R h R) (centralQuotient_quadratic ρ R h (g • R))
    (centralQuotient_moved_eq_top ρ R h) (centralQuotient_fixed_eq_bot ρ hc)

end Representation.SL2SylowFixedRecognition

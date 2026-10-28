module
public import Theory.GroupTheory.PushingUp.BaumannBinary.NaturalAll
public import Theory.Representation.RankOne.QuadraticRecognition.NaturalConsequences

/-!
# Source naturality and fixed-space geometry of the Baumann quotient

The all-degree natural coordinates give a faithful quadratic action on the
original quotient V/(V ∩ Z(L)). The original Sylow-center generators supply
the corrected fixed-space generation condition, which passes to this exact
quotient. The DGS natural-module definition and its consequences therefore
hold with the same quotient marking and the same Sylow image: irreducibility,
fixed order 2ⁿ, equality of nonidentity Sylow-element fixed spaces, complementary
fixed spaces for distinct Sylows, and transitivity on nonzero vectors.

Source: Delgado–Goldschmidt–Stellmacher, *Groups and Graphs* (1985), definition
on printed p.112, properties on p.113, and the natural-module clause of (6.3)
on p.120. This does not assert the remaining bound [O₂(L),L] ≤ V.
The literal original-adjacent-core application is in
`CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.BaumannApplication.SourceNatural`.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace Theory.GroupTheory.BaumannBinary
variable {G F W : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

omit [Finite F] in
private theorem coordinate_faithful (ρ : Representation (ZMod 2) SL(2,F) W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, E (ρ g v) = Matrix.mulVec g.val (E v)) : Function.Injective ρ := by
  intro a b hab
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  obtain ⟨w,rfl⟩ := E.surjective v
  rw [←he,←he,hab]

omit [Finite F] in
private theorem coordinate_fixed (ρ : Representation (ZMod 2) SL(2,F) W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, E (ρ g v) = Matrix.mulVec g.val (E v)) : fixedSpace ρ ⊤ = ⊥ := by
  apply bot_unique
  intro v hv
  have h (g : SL(2,F)) : Matrix.mulVec g.val (E v) = E v :=
    (he g v).symm.trans (congrArg E (hv ⟨g,mem_top g⟩))
  have h₁ := congrFun (h (Matrix.SpecialLinearGroup.transvection zero_ne_one 1)) 0
  have h₀ := congrFun (h (Matrix.SpecialLinearGroup.transvection one_ne_zero 1)) 1
  have hv₁ : E v 1 = 0 := by
    simpa [Matrix.SpecialLinearGroup.transvection_coe,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using h₁
  have hv₀ : E v 0 = 0 := by
    simpa [Matrix.SpecialLinearGroup.transvection_coe,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using h₀
  apply E.injective
  ext i
  rw [map_zero]
  fin_cases i
  · exact hv₀
  · exact hv₁

private theorem coordinate_quadratic (ρ : Representation (ZMod 2) SL(2,F) W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, E (ρ g v) = Matrix.mulVec g.val (E v)) (S : Sylow 2 SL(2,F)) :
    IsQuadratic ρ S := by
  have hu : IsQuadratic ρ (Matrix.SpecialLinearGroup.upperUnipotent F) := by
    intro a ha b hb v
    obtain ⟨x,rfl⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F a).mp ha
    obtain ⟨y,rfl⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F b).mp hb
    apply E.injective
    simp only [he,map_sub]
    ext i
    fin_cases i
    · simp [Matrix.SpecialLinearGroup.transvection_coe,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.mul_apply]
      ring
    · simp [Matrix.SpecialLinearGroup.transvection_coe,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.mul_apply]
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F)
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2) S
  have hh := SL2SylowFixedRecognition.quadratic_conjugate ρ hu g
  change IsQuadratic ρ ((g • Matrix.SpecialLinearGroup.upperUnipotentSylow F 2 : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) at hh
  rwa [hg] at hh

/-- The exact source definition and every p.113 consequence, on the original
central quotient and with its original marked action. -/
theorem centerClosure_source_natural (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    letI := (centerClosure_reduced P hc).elementary
    let hker := hk.trans (centerClosure_centralizer P hc hP q hq hk hn hF).symm
    let ρ := NormalElementaryQuotient.representation (centerClosure (P : Subgroup G)) q hq hker
    let σ := SL2SylowFixedRecognition.centralQuotient ρ
    let S := P.mapSurjective hq
    IsSourceNatural σ S n ∧ σ.IsIrreducible ∧
      Nat.card (fixedSpace σ S) = 2^n ∧
      (∀ t ∈ (S : Subgroup SL(2,F)), t ≠ 1 →
        fixedSpace σ (zpowers t) = fixedSpace σ S) ∧
      (∀ g ∉ normalizer (S : Set SL(2,F)),
        IsCompl (fixedSpace σ S) (fixedSpace σ (g • S : Sylow 2 SL(2,F)))) ∧
      (∀ v w, v ≠ 0 → w ≠ 0 → ∃ g, σ g v = w) := by
  let := (centerClosure_reduced P hc).elementary
  let V := centerClosure (P : Subgroup G)
  have hker := hk.trans (centerClosure_centralizer P hc hP q hq hk hn hF).symm
  let ρ := NormalElementaryQuotient.representation V q hq hker
  let σ := SL2SylowFixedRecognition.centralQuotient ρ
  let S := P.mapSurjective hq
  obtain ⟨E,he⟩ := centerClosure_natural_quotient_all P hc hP q hq hk hn hF
  have hgenρ : GeneratedByFixedSpace ρ S := by
    have hh := fixed_generation P q hq hker
    change (⨆ g : (⊤ : Subgroup SL(2,F)), (fixedSpace ρ S).map (ρ g)) = ⊤ at hh
    unfold GeneratedByFixedSpace
    simpa only [iSup_subtype,mem_top,iSup_true] using hh
  have hgen : GeneratedByFixedSpace σ S := by
    have hh := generatedByFixedSpace_of_equivariant_surjection ρ σ (MonoidHom.id _)
      (fixedSpace ρ ⊤).mkQ (fixedSpace ρ ⊤).mkQ_surjective (fun _ _ => rfl) S hgenρ
    simpa only [Subgroup.map_id] using hh
  have hfaith := coordinate_faithful σ E he
  have hfix := coordinate_fixed σ E he
  have hquad := coordinate_quadratic σ E he S
  let : Finite (Additive V ⧸ fixedSpace ρ ⊤) :=
    Finite.of_surjective _ (fixedSpace ρ ⊤).mkQ_surjective
  have hfixed := sl2_natural_fixed_spaces σ S hquad hgen hfix E
  refine ⟨sourceNatural_of_coordinates σ hfaith S hquad E hF,
    irreducible_of_natural_coordinates σ E he,hfixed.1.trans hF,hfixed.2,?_,?_⟩
  · intro g hg
    apply sl2_sylow_fixed_isCompl σ S (g • S) ?_ hquad hgen hfix
    intro hh
    exact hg (Sylow.smul_eq_iff_mem_normalizer.mp hh.symm)
  · intro v w hv hw
    exact transitive_of_natural_coordinates σ E he hv hw
end Theory.GroupTheory.BaumannBinary

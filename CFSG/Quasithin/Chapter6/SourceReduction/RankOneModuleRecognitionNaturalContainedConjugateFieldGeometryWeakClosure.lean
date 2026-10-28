module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryKernel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureFixedSpaceMarking
public import CFSG.Quasithin.ChapterE.Section03.Parameters
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure

/-!
# Weak closure in the field-space centralizer

The fixed plane of the field involution spans the original natural plane
over its defining field. An A₂ actor is field-linear, so fixing this plane
pointwise makes it trivial. E.3.10 therefore forces the small-corank
conjugate generators inside C_P(U) to centralize B. This proves both W₀
and W₁ bounds using the original induced automizer and global parameter.

Source: Aschbacher–Smith, 6.1.14(3), printed p.671.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ConjugateFixedSpaces Representation.SL2NaturalOffenders.FixedField
open Representation.BinaryOffender ChapterE
universe u

private theorem linear_fixes_fixed_plane
    {F : Type} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hi : Function.Involutive E)
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (ha : a ^ 2 = 1) (ho : ¬ ∃ g, a = MulAut.conj g)
    (d : Module.End F (Fin 2 → F)) (hd : ∀ v, E v = v → d v = v) :
    d = 1 := by
  classical
  obtain ⟨σ, _, _, c, B, hnat, hβ, hB⟩ :=
    outer_involution_natural_alignment a E hi he ha ho
  let b := (Pi.basisFun F (Fin 2)).map B.symm
  apply b.ext
  intro j
  simp only [b, Module.Basis.map_apply, Pi.basisFun_apply, Module.End.one_apply]
  apply hd
  apply B.injective
  rw [hB]
  change (fun k => σ (B (B.symm (Pi.single j 1)) k)) = B (B.symm (Pi.single j 1))
  simp only [B.apply_symm_apply]
  ext k
  by_cases hk : k = j <;> simp [hk]

variable {G : Type u} [Group G] [Finite G] {L M B U : Subgroup G} {n : ℕ}
  [IsElementaryAbelian 2 B]

omit [Finite G] in
/-- A₂ cannot contain a nontrivial actor fixing the field plane pointwise. -/
theorem field_fixedSpace_no_A2_centralizer
    (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥)
    (A : Subgroup G) (hAB : A ≤ normalizer (B : Set G))
    (hAU : A ≤ centralizer (U : Set G)) :
    ¬ inducedAutomizer B A ∈ fixedSpaceFamily (automizerRepresentation B) 2 := by
  intro hA
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨t, _, htB, hU, K, _, _, _, _, a, σ, hσ, hσsq, hσact⟩ := hfield
  obtain ⟨hasq, haout⟩ := field_quotientActor e a t σ hσ hσsq hσact
  have hi : Function.Involutive (vectorActor f ⟨t, htB⟩) := by
    apply intertwiner_involutive_of_fixed (quotientActor e t) _
      (vectorActor_intertwines e f hf t htB) hasq
    obtain ⟨u, hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    have hu := u.property
    let v : B := ⟨u, (hU.le hu).1⟩
    refine ⟨(f v).toAdd, ?_, ?_⟩
    · intro hz
      have hv : v = 1 := f.injective (by simpa using congrArg Multiplicative.ofAdd hz)
      exact hune (Subtype.ext (congrArg (fun b : B => (b : G)) hv))
    · apply (vectorActor_fixed_iff f ⟨t, htB⟩ _).mpr
      simpa [v] using (hU.le hu).2
  obtain ⟨E, hE, hsemi⟩ := natural_binary_marking_semilinear e f hf
  let ρ : Representation (ZMod 2) (Automizer B) (Fin 2 → F) :=
    E.conjRingEquiv.toMonoidHom.comp (automizerRepresentation B)
  have hcoord (a : Automizer B) (v : B) :
      ρ a (f v).toAdd = (f (a.val v)).toAdd := by
    rw [← hE]
    change E (automizerRepresentation B a (E.symm (E (Additive.ofMul v)))) = _
    rw [E.symm_apply_apply]
    exact hE _
  have hfix (D : Subgroup (Automizer B)) (v : Additive B) :
      E v ∈ fixedSpace ρ D ↔ v ∈ fixedSpace (automizerRepresentation B) D := by
    constructor
    · intro hv a
      apply E.injective
      change E (automizerRepresentation B (a : Automizer B) v) = E v
      have hh := hv a
      change E (automizerRepresentation B a (E.symm (E v))) = E v at hh
      simpa only [E.symm_apply_apply] using hh
    · intro hv a
      change E (automizerRepresentation B a (E.symm (E v))) = E v
      rw [E.symm_apply_apply]
      exact congrArg E (hv a)
  let I := inducedAutomizer B A
  have hI : I ∈ fixedSpaceFamily ρ 2 := by
    refine ⟨hA.1, hA.2.1, ?_⟩
    intro D hDI hidx
    ext v
    obtain ⟨w, rfl⟩ := E.surjective v
    rw [hfix, hfix, hA.2.2 D hDI hidx]
  have hIsemi : ∀ a : I, ∃ σ : F ≃+* F, ∀ c v,
      ρ (a : Automizer B) (c • v) = σ c • ρ (a : Automizer B) v := by
    intro a
    obtain ⟨b, hb, he⟩ := a.property
    obtain ⟨σ, hσ⟩ := hsemi b (hNL b.property) b.property
    refine ⟨σ, ?_⟩
    intro c v
    rw [← he]
    exact hσ c v
  have hlin := fixedSpaceFamily_two_fieldLinear ρ hI hIsemi
  apply hA.2.1.1
  apply (inducedAutomizer_eq_bot_iff hAB).mpr
  intro a ha b hb
  let z : Automizer B := B.normalizerMonoidHom.rangeRestrict ⟨a, hAB ha⟩
  have hz : z ∈ I := mem_map.mpr ⟨_, ha, rfl⟩
  let d : Module.End F (Fin 2 → F) :=
    { toFun := ρ z
      map_add' := (ρ z).map_add
      map_smul' := hlin z hz }
  have hd : d = 1 := linear_fixes_fixed_plane (quotientActor e t)
    (vectorActor f ⟨t, htB⟩) hi (vectorActor_intertwines e f hf t htB) hasq haout d (by
      intro v hv
      let w := f.symm (Multiplicative.ofAdd v)
      have hw : (w : G) ∈ U := by
        rw [hU]
        exact ⟨w.property, (vectorActor_fixed_iff f ⟨t, htB⟩ _).mp hv⟩
      have hwv : (f w).toAdd = v := by simp [w]
      change ρ z v = v
      rw [← hwv, hcoord]
      congr 2
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hAU ha _ hw).symm)
  have hh := LinearMap.congr_fun hd (f ⟨b, hb⟩).toAdd
  change ρ z (f ⟨b, hb⟩).toAdd = (f ⟨b, hb⟩).toAdd at hh
  rw [hcoord] at hh
  have heq := congrArg (fun v : B => (v : G))
    (f.injective (Multiplicative.toAdd.injective hh))
  change a * b * a⁻¹ = b at heq
  exact (mul_inv_eq_iff_eq_mul.mp heq).symm

/-- E.3.10 turns the A₂ exclusion into both source weak-closure bounds.
This statement applies directly to C_P(U), without moving the original layer. -/
theorem field_fixedSpace_weak_closure
    (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥)
    (hs : globalS B = n) (R : Subgroup G)
    (hRB : R ≤ normalizer (B : Set G)) (hRU : R ≤ centralizer (U : Set G))
    {i : ℕ} (hi : i + 2 ≤ n) :
    W B R i ≤ R ⊓ centralizer (B : Set G) := by
  apply le_inf (W_le _ _ _) ?_
  change sSup (gamma B R i) ≤ _
  apply sSup_le
  rintro A ⟨⟨g, hAg, hidx⟩, hAR⟩
  by_cases hc : B.map (MulAut.conj g).toMonoidHom ≤ centralizer (B : Set G)
  · exact hAg.trans hc
  have hcomm : ⁅B, B.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro he
    exact hc (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  have hcor : subgroupCorank (B.map (MulAut.conj g).toMonoidHom) A = i := by
    simp only [subgroupCorank, hidx, Nat.log_pow Nat.one_lt_two]
  have hsmall : (subgroupCorank (B.map (MulAut.conj g).toMonoidHom) A : ℕ∞) < globalS B := by
    rw [hcor, hs]
    exact ENat.natCast_lt_natCast.mpr (by omega)
  have hf := (inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS
    g (le_inf hAg (hAR.trans hRB)) hsmall hcomm).2
  rw [hs, ENat.toNat_natCast, hcor] at hf
  exact False.elim (field_fixedSpace_no_A2_centralizer hnatural hNL hfield hUne A
    (hAR.trans hRB) (hAR.trans hRU)
    (fixedSpaceFamily_mono _ (by decide) (by omega) hf))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

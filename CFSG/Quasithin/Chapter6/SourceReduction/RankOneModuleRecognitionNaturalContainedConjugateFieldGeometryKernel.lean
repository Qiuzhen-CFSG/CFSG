module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryQuotient
public import Theory.GroupTheory.AbelianConjugateSpan
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryDefs

/-!
# Kernels of the field-fixed normalizer action

The pointwise stabilizer of U inside L is exactly the kernel of the
original natural action on B. Indeed the field-fixed plane contains a
basis of the original natural plane, and its fixed SL₂ actor acts
faithfully. Thus C_L(U)=C_L(B).

The actual two-cores of N_L(U) and O²(N_L(U)) centralize B. Once the local
component argument establishes relative normality of the residual in
N_G(U), its two-core centralizes the entire normalizer closure of B.
That normality remains explicit here and is owned by the contained branch.

Source: Aschbacher–Smith, 6.1.14(5), printed p.671.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces
open Representation.SL2NaturalOffenders.FixedField
universe u
variable {G : Type u} [Group G] {L B U : Subgroup G}
  {F : Type} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

private theorem fixed_pointwise_faithful
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hi : Function.Involutive E)
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (ha : a ^ 2 = 1) (ho : ¬ ∃ g, a = MulAut.conj g)
    (g : a.fixedSubgroup)
    (hg : ∀ v : fixedVectors E, g.val.val.mulVec (v : Fin 2 → F) = v) :
    g = 1 := by
  obtain ⟨σ, _, _, ea, ev, hev⟩ := outer_involution_fixed_natural a E hi he ha ho
  apply ea.injective
  rw [map_one]
  apply Representation.specialLinearNatural_injective 2
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := ev.surjective v
  rw [map_one, Module.End.one_apply, Representation.specialLinearNatural_apply]
  rw [← hev]
  congr 1
  exact Subtype.ext (hg w)

/-- The marked fixed plane detects the kernel of the original L-action. -/
theorem fixedNormalizer_centralizer
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (f : B ≃* Multiplicative (Fin 2 → F))
    (hf : ∀ (l : L) (v : B),
      ((f.symm (Multiplicative.ofAdd ((e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec
        (Multiplicative.toAdd (f v))))) : G) = (l : G) * (v : G) * (l : G)⁻¹)
    (t : normalizer (L : Set G)) (htB : (t : G) ∈ normalizer (B : Set G))
    (hU : U = B ⊓ centralizer ({(t : G)} : Set G))
    (hi : Function.Involutive (vectorActor f ⟨t, htB⟩))
    (hsq : quotientActor e t ^ 2 = 1)
    (hout : ¬ ∃ g, quotientActor e t = MulAut.conj g) :
    L ⊓ centralizer (U : Set G) = L ⊓ centralizer (B : Set G) := by
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le (hU.le.trans inf_le_left)))
  rintro l ⟨hl, hc⟩
  let k : L := ⟨l, hl⟩
  let q := e (QuotientGroup.mk' (pCore 2 L) k)
  let a := quotientActor e t
  let E := vectorActor f ⟨t, htB⟩
  have hq : q ∈ a.fixedSubgroup := (MulAut.mem_fixedSubgroup _ _).mpr
    ((mem_normalizer_fixed_iff e f hf t htB hU hi hsq hout k).mp
      (Subgroup.centralizer_le_normalizer _ hc))
  have hq1 : q = 1 := by
    have hh := fixed_pointwise_faithful a E hi (vectorActor_intertwines e f hf t htB)
      hsq hout ⟨q, hq⟩ (fun v => ?_)
    · exact congrArg Subtype.val hh
    · have hvU : (f.symm (Multiplicative.ofAdd (v : Fin 2 → F)) : G) ∈ U := by
        rw [hU]
        exact ⟨(f.symm _).property, (vectorActor_fixed_iff f ⟨t, htB⟩ _).mp v.property⟩
      apply Multiplicative.ofAdd.injective
      apply f.symm.injective
      apply Subtype.ext
      have hh := hf k (f.symm (Multiplicative.ofAdd (v : Fin 2 → F)))
      simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at hh
      exact hh.trans (mul_inv_eq_iff_eq_mul.mpr (hc _ hvU).symm)
  refine ⟨hl, mem_centralizer_iff.mpr ?_⟩
  intro b hb
  have hh := hf k ⟨b, hb⟩
  change (f.symm (Multiplicative.ofAdd (q.val.mulVec (f ⟨b, hb⟩).toAdd)) : G) = _ at hh
  rw [hq1] at hh
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, ofAdd_toAdd,
    MulEquiv.symm_apply_apply] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Representation.SL2NaturalOffenders.FixedField
universe u
variable {G : Type u} [Group G] {L M B U : Subgroup G} {n : ℕ}

/-- Pointwise stabilization of the field-fixed plane inside L is exactly
pointwise stabilization of the whole original module. -/
theorem field_fixedSpace_inner_centralizer
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) :
    L ⊓ centralizer (U : Set G) = L ⊓ centralizer (B : Set G) := by
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨t, _, htB, hU, K, _, _, _, _, a, σ, hσ, hσsq, hσact⟩ := hfield
  obtain ⟨hasq, haout⟩ := ConjugateFixedSpaces.field_quotientActor e a t σ hσ hσsq hσact
  have hi : Function.Involutive (ConjugateFixedSpaces.vectorActor f ⟨t, htB⟩) := by
    apply intertwiner_involutive_of_fixed (ConjugateFixedSpaces.quotientActor e t) _
      (ConjugateFixedSpaces.vectorActor_intertwines e f hf t htB) hasq
    obtain ⟨u, hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    have hu := u.property
    let v : B := ⟨u, (hU.le hu).1⟩
    refine ⟨(f v).toAdd, ?_, ?_⟩
    · intro hz
      have hv : v = 1 := f.injective (by simpa using congrArg Multiplicative.ofAdd hz)
      exact hune (Subtype.ext (congrArg (fun b : B => (b : G)) hv))
    · apply (ConjugateFixedSpaces.vectorActor_fixed_iff f ⟨t, htB⟩ _).mpr
      simpa [v] using (hU.le hu).2
  exact ConjugateFixedSpaces.fixedNormalizer_centralizer e f hf t htB hU hi hasq haout

variable [Finite G]

/-- Both intrinsic two-cores centralize B under their original embeddings. -/
theorem field_fixedSpace_core_centralizes
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) (hn : 2 < n) :
    (L ⊓ normalizer (U : Set G)).pCoreIn 2 ≤ centralizer (B : Set G) ∧
      (fieldLocalResidual L U).pCoreIn 2 ≤ centralizer (B : Set G) := by
  obtain ⟨m, _, hNU, hRU⟩ := field_fixedSpace_natural hn hnatural hfield hUne
  have hc := field_fixedSpace_inner_centralizer hnatural hfield hUne
  have step (K : Subgroup G) (hKL : K ≤ L) (h : IsNaturalModule K U m) :
      K.pCoreIn 2 ≤ centralizer (B : Set G) := by
    obtain ⟨F, _, _, _, _, hmodel⟩ := h
    rw [← hmodel.centralizer_eq_core (Representation.specialLinearNatural_injective 2)]
    exact ((inf_le_inf_right _ hKL).trans hc.le).trans inf_le_right
  exact ⟨step _ inf_le_left hNU, step _ ((map_subtype_le _).trans inf_le_left) hRU⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Representation.SL2NaturalOffenders.FixedField
universe u
variable {G : Type u} [Group G] [Finite G] {L M B U : Subgroup G} {n : ℕ}

/-- The residual's relative normality propagates its core centralization
from B to the entire N_G(U)-closure. -/
theorem field_fixedSpace_core_centralizes_closure
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (hN : ((fieldLocalResidual L U).subgroupOf (normalizer (U : Set G))).Normal) :
    (fieldLocalResidual L U).pCoreIn 2 ≤ centralizer (fieldModuleClosure B U : Set G) := by
  have hR : fieldLocalResidual L U ≤ normalizer (U : Set G) :=
    (map_subtype_le _).trans inf_le_right
  have hNR := (normal_subgroupOf_iff_le_normalizer hR).mp hN
  have hNQ := hNR.trans (normalizer_le_normalizer_characteristic_image
    (fieldLocalResidual L U) (pCore 2 (fieldLocalResidual L U)))
  exact le_centralizer_conjugateSpanBy_of_normalizes _ B (normalizer (U : Set G))
    hNQ (field_fixedSpace_core_centralizes hnatural hfield hUne hn).2
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

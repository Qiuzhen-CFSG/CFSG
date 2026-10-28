module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryNatural
public import Theory.Representation.SL2NaturalOffenders.FixedField.Displacement

/-!
# The quotient by an involutory field fixed space

The binary displacement map, transported through the original natural
coordinates, is a surjection B → U with kernel U. The literal N_L(U)-action
commutes with this map. Hence the actual quotient B/U is equivariantly
isomorphic to U, for both N_L(U) and its embedded residual O²(N_L(U)).
The equivalence retains the ambient conjugation equations and needs no
involution lift through the kernel.

Source: Aschbacher–Smith, opening calculation in 6.1.14, printed p.671.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces
open Representation.SL2NaturalOffenders.FixedField
universe u
variable {G : Type u} [Group G] {L B U : Subgroup G}
  {F : Type} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Transport displacement through the natural marking and its fixed plane. -/
theorem fixedNormalizer_displacement
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
    ∃ d : B →* U, Function.Surjective d ∧ d.ker = U.subgroupOf B ∧
      ∀ (l : (L ⊓ normalizer (U : Set G) : Subgroup G)) (b b' : B),
        (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
        (d b' : G) = (l : G) * (d b : G) * (l : G)⁻¹ := by
  let E := vectorActor f ⟨t, htB⟩
  let a := quotientActor e t
  let ffix := fixedModuleEquiv f ⟨t, htB⟩ hU
  let δ := displacement E hi
  let d : B →* U := ffix.symm.toMonoidHom.comp (δ.toMultiplicative.comp f.toMonoidHom)
  have he := vectorActor_intertwines e f hf t htB
  have hd : Function.Surjective d := ffix.symm.surjective.comp
    ((displacement_surjective a E hi he hsq hout).comp f.surjective)
  refine ⟨d, hd, ?_, ?_⟩
  · ext b
    change ffix.symm (Multiplicative.ofAdd (δ (f b).toAdd)) = 1 ↔ (b : G) ∈ U
    rw [← ffix.symm.map_one, ffix.symm.injective.eq_iff]
    change δ (f b).toAdd = 0 ↔ _
    rw [displacement_eq_zero, vectorActor_fixed_iff]
    simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply]
    rw [hU]
    exact ⟨fun h => ⟨b.property, h⟩, fun h => h.2⟩
  · intro l b b' hb'
    let k : L := inclusion inf_le_left l
    let q := e (QuotientGroup.mk' (pCore 2 L) k)
    have hq : q ∈ a.fixedSubgroup := (MulAut.mem_fixedSubgroup _ _).mpr
      ((mem_normalizer_fixed_iff e f hf t htB hU hi hsq hout k).mp l.property.2)
    have hb : (f b').toAdd = q.val.mulVec (f b).toAdd := by
      apply Multiplicative.ofAdd.injective
      apply f.symm.injective
      apply Subtype.ext
      simpa only [ofAdd_toAdd, MulEquiv.symm_apply_apply] using hb'.trans (hf k b).symm
    have hh := displacement_equivariant a E hi he ⟨q, hq⟩ (f b).toAdd
    have hdval (v : B) : (d v : G) =
        (f.symm (Multiplicative.ofAdd (δ (f v).toAdd : Fin 2 → F)) : G) :=
      fixedModuleEquiv_symm_coe f ⟨t, htB⟩ hU _
    rw [hdval, hb, hh]
    have hu : (f ⟨(d b : G), (hU.le (d b).property).1⟩).toAdd =
        (δ (f b).toAdd : Fin 2 → F) := by
      have hh : (⟨(d b : G), (hU.le (d b).property).1⟩ : B) =
          f.symm (Multiplicative.ofAdd (δ (f b).toAdd : Fin 2 → F)) :=
        Subtype.ext (hdval b)
      rw [hh, f.apply_symm_apply]
      rfl
    rw [← hu]
    exact hf k ⟨(d b : G), (hU.le (d b).property).1⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Representation.SL2NaturalOffenders.FixedField
universe u
variable {G : Type u} [Group G] {L M B U : Subgroup G} {n : ℕ}

/-- The fixed-field witness gives a surjection B → U with kernel U and the
actual N_L(U)-equivariance, even when the field markings differ. -/
theorem field_fixedSpace_displacement
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) :
    ∃ d : B →* U, Function.Surjective d ∧ d.ker = U.subgroupOf B ∧
      ∀ (l : (L ⊓ normalizer (U : Set G) : Subgroup G)) (b b' : B),
        (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
        (d b' : G) = (l : G) * (d b : G) * (l : G)⁻¹ := by
  obtain ⟨F, _, _, _, hF, e, f, hf⟩ := hnatural
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
  exact ConjugateFixedSpaces.fixedNormalizer_displacement e f hf t htB hU hi hasq haout

variable [Finite G] [IsElementaryAbelian 2 B]

/-- The literal quotient B/U is the same half-degree natural module as U. -/
theorem field_fixedSpace_quotient
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) (hn : 2 < n) :
    ∃ (m : ℕ) (eQ : (B ⧸ U.subgroupOf B) ≃* U), n = 2 * m ∧
      IsNaturalModule (L ⊓ normalizer (U : Set G)) U m ∧
      IsNaturalModule (fieldLocalResidual L U) U m ∧
      ∀ (l : (L ⊓ normalizer (U : Set G) : Subgroup G)) (b b' : B),
        (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
        (eQ (QuotientGroup.mk' (U.subgroupOf B) b') : G) =
          (l : G) * (eQ (QuotientGroup.mk' (U.subgroupOf B) b) : G) * (l : G)⁻¹ := by
  obtain ⟨m, hnm, hNU, hRU⟩ := field_fixedSpace_natural hn hnatural hfield hUne
  obtain ⟨d, hd, hk, he⟩ := field_fixedSpace_displacement hnatural hfield hUne
  let eQ := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d hd)
  refine ⟨m, eQ, hnm, hNU, hRU, ?_⟩
  intro l b b' hb
  exact he l b b' hb
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

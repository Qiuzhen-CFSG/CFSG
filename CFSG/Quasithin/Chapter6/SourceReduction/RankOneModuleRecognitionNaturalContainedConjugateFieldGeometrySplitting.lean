module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryQuotient

/-!
# Two copies of the field-fixed natural module

A trace-one scalar splits binary displacement equivariantly under the fixed
SL₂ actors. Its kernel is the fixed module itself, so the original layer
is equivariantly isomorphic to two copies of that module. Transport through
the natural marking preserves the literal conjugation action of N_L(U),
without requiring an involutory lift of the field actor.

Source: Aschbacher–Smith, 6.1.14(5), printed p.671.
-/

public section


namespace Representation.SL2NaturalOffenders.FixedField
open Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F] [CharP F 2]

/-- The trace surjection splits equivariantly under the fixed actors. -/
theorem displacement_equivariant_section
    (a : MulAut (SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hi : Function.Involutive E)
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (ha : a ^ 2 = 1) (ho : ¬ ∃ g, a = MulAut.conj g) :
    ∃ s : fixedVectors E →+ (Fin 2 → F),
      (∀ v, displacement E hi (s v) = v) ∧
      ∀ (g : a.fixedSubgroup) (v : fixedVectors E),
        s ⟨g.val.val.mulVec (v : Fin 2 → F), fixed_action_mem_of_intertwines a E he g v⟩ =
          g.val.val.mulVec (s v) := by
  obtain ⟨σ, hσ, hσi, c, B, hnat, _, hB⟩ :=
    outer_involution_natural_alignment a E hi he ha ho
  have hne : ∃ x, σ x ≠ x := by
    by_contra! h
    exact hσ (RingEquiv.ext h)
  obtain ⟨r, hr⟩ := InvolutiveTrace.exists_trace_one σ hσi hne
  let s : fixedVectors E →+ (Fin 2 → F) :=
    { toFun := fun v => r • (v : Fin 2 → F)
      map_zero' := smul_zero r
      map_add' := fun v w => smul_add r (v : Fin 2 → F) w }
  refine ⟨s, ?_, ?_⟩
  · intro v
    apply Subtype.ext
    apply B.injective
    change B (E (r • (v : Fin 2 → F)) + r • (v : Fin 2 → F)) = B v
    rw [map_add, hB, map_smul]
    have hv : (fun i => σ (B v i)) = B v := by
      rw [← hB, show E (v : Fin 2 → F) = v from v.property]
    ext i
    change σ (r * B v i) + r * B v i = B v i
    rw [map_mul, congrFun hv i, ← add_mul]
    have hr' : σ r + r = 1 := (add_comm _ _).trans hr
    rw [hr', one_mul]
  · intro g v
    change r • (g.val.val.mulVec (v : Fin 2 → F)) = g.val.val.mulVec (r • (v : Fin 2 → F))
    exact (Matrix.mulVec_smul _ _ _).symm
end Representation.SL2NaturalOffenders.FixedField

namespace Representation.SL2NaturalOffenders.FixedField
open Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F] [CharP F 2]

theorem displacement_double_equiv
    (a : MulAut (SpecialLinearGroup (Fin 2) F))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F)) (hi : Function.Involutive E)
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (ha : a ^ 2 = 1) (ho : ¬ ∃ g, a = MulAut.conj g) :
    ∃ e : (Fin 2 → F) ≃+ (fixedVectors E × fixedVectors E),
      ∀ (g : a.fixedSubgroup) (v : Fin 2 → F),
        e (g.val.val.mulVec v) =
          (⟨g.val.val.mulVec (e v).1, fixed_action_mem_of_intertwines a E he g (e v).1⟩,
           ⟨g.val.val.mulVec (e v).2, fixed_action_mem_of_intertwines a E he g (e v).2⟩) := by
  obtain ⟨s, hs, hse⟩ := displacement_equivariant_section a E hi he ha ho
  let δ := displacement E hi
  let p : (Fin 2 → F) →+ fixedVectors E :=
    { toFun := fun v => ⟨v - s (δ v), by
        apply (displacement_eq_zero E hi _).mp
        change δ (v - s (δ v)) = 0
        rw [map_sub, hs, sub_self]⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := by
        intro v w
        apply Subtype.ext
        change (v + w) - s (δ (v + w)) = (v - s (δ v)) + (w - s (δ w))
        rw [map_add, map_add]
        abel }
  have hδ (u : fixedVectors E) : δ (u : Fin 2 → F) = 0 :=
    (displacement_eq_zero E hi _).mpr u.property
  let e : (Fin 2 → F) ≃+ (fixedVectors E × fixedVectors E) :=
    { toFun := fun v => (p v, δ v)
      invFun := fun uv => (uv.1 : Fin 2 → F) + s uv.2
      left_inv := by intro v; exact sub_add_cancel v (s (δ v))
      right_inv := by
        rintro ⟨u, v⟩
        apply Prod.ext
        · apply Subtype.ext
          change ((u : Fin 2 → F) + s v) - s (δ ((u : Fin 2 → F) + s v)) = u
          rw [map_add, hδ, hs, zero_add, add_sub_cancel_right]
        · change δ ((u : Fin 2 → F) + s v) = v
          rw [map_add, hδ, hs, zero_add]
      map_add' := by intro v w; exact Prod.ext (p.map_add v w) (δ.map_add v w) }
  refine ⟨e, ?_⟩
  intro g v
  have hd : δ (g.val.val.mulVec v) =
      ⟨g.val.val.mulVec (δ v), fixed_action_mem_of_intertwines a E he g (δ v)⟩ :=
    Subtype.ext (displacement_equivariant a E hi he g v)
  apply Prod.ext
  · apply Subtype.ext
    change g.val.val.mulVec v - s (δ (g.val.val.mulVec v)) =
      g.val.val.mulVec (v - s (δ v))
    rw [hd, hse, Matrix.mulVec_sub]
  · exact hd
end Representation.SL2NaturalOffenders.FixedField

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces
open Representation.SL2NaturalOffenders.FixedField
universe u
variable {G : Type u} [Group G] {L B U : Subgroup G}
  {F : Type} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

theorem fixedNormalizer_double_equiv
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
    ∃ d : B ≃* (U × U),
      ∀ (l : (L ⊓ normalizer (U : Set G) : Subgroup G)) (b b' : B),
        (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
        ((d b').1 : G) = (l : G) * ((d b).1 : G) * (l : G)⁻¹ ∧
        ((d b').2 : G) = (l : G) * ((d b).2 : G) * (l : G)⁻¹ := by
  let E := vectorActor f ⟨t, htB⟩
  let a := quotientActor e t
  let ffix := fixedModuleEquiv f ⟨t, htB⟩ hU
  have he := vectorActor_intertwines e f hf t htB
  obtain ⟨q, hq⟩ := displacement_double_equiv a E hi he hsq hout
  let d : B ≃* (U × U) := f.trans (q.toMultiplicative.trans
    ((MulEquiv.prodMultiplicative (fixedVectors E) (fixedVectors E)).trans
      (MulEquiv.prodCongr ffix.symm ffix.symm)))
  refine ⟨d, ?_⟩
  intro l b b' hb'
  let k : L := inclusion inf_le_left l
  let x := e (QuotientGroup.mk' (pCore 2 L) k)
  have hx : x ∈ a.fixedSubgroup := (MulAut.mem_fixedSubgroup _ _).mpr
    ((mem_normalizer_fixed_iff e f hf t htB hU hi hsq hout k).mp l.property.2)
  have hb : (f b').toAdd = x.val.mulVec (f b).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    simpa only [ofAdd_toAdd, MulEquiv.symm_apply_apply] using hb'.trans (hf k b).symm
  have hqq := hq ⟨x, hx⟩ (f b).toAdd
  have heq (v : fixedVectors E) :
      (ffix.symm (Multiplicative.ofAdd
        (⟨x.val.mulVec v, fixed_action_mem_of_intertwines a E he ⟨x, hx⟩ v⟩ :
          fixedVectors E)) : G) =
        (l : G) * (ffix.symm (Multiplicative.ofAdd v) : G) * (l : G)⁻¹ := by
    rw [fixedModuleEquiv_symm_coe]
    have hv : (f ⟨(ffix.symm (Multiplicative.ofAdd v) : G),
        (hU.le (ffix.symm (Multiplicative.ofAdd v)).property).1⟩).toAdd = (v : Fin 2 → F) := by
      have hh : (⟨(ffix.symm (Multiplicative.ofAdd v) : G),
          (hU.le (ffix.symm (Multiplicative.ofAdd v)).property).1⟩ : B) =
          f.symm (Multiplicative.ofAdd (v : Fin 2 → F)) :=
        Subtype.ext (fixedModuleEquiv_symm_coe f ⟨t, htB⟩ hU _)
      rw [hh, f.apply_symm_apply]
      rfl
    change (f.symm (Multiplicative.ofAdd (x.val.mulVec (v : Fin 2 → F))) : G) = _
    rw [← hv]
    exact hf k _
  change (ffix.symm (Multiplicative.ofAdd (q (f b').toAdd).1) : G) = _ ∧
    (ffix.symm (Multiplicative.ofAdd (q (f b').toAdd).2) : G) = _
  rw [hb, hqq]
  exact ⟨heq _, heq _⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Representation.SL2NaturalOffenders.FixedField
universe u
variable {G : Type u} [Group G] {L M B U : Subgroup G} {n : ℕ}

/-- The original layer is two copies of the field-fixed module, with the
literal N_L(U)-action on both factors. -/
theorem field_fixedSpace_double_equiv
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) :
    ∃ d : B ≃* (U × U),
      ∀ (l : (L ⊓ normalizer (U : Set G) : Subgroup G)) (b b' : B),
        (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
        ((d b').1 : G) = (l : G) * ((d b).1 : G) * (l : G)⁻¹ ∧
        ((d b').2 : G) = (l : G) * ((d b).2 : G) * (l : G)⁻¹ := by
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
  exact ConjugateFixedSpaces.fixedNormalizer_double_equiv e f hf t htB hU hi hasq haout

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

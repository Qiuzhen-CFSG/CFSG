module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateDefs
public import Theory.Representation.SL2NaturalOffenders.FixedField.ActorAlignment
public import Mathlib.Algebra.Module.ZMod

/-!
# Marked actions for the fixed-space alternatives of 6.1.13

Conjugation by a common normalizer induces compatible actions on the actual
quotient L/O₂(L) and on the marked natural module. We retain the original
actor when aligning its quotient action with an entrywise field involution;
there is no assumption that an involution lifts through the module kernel.
The coordinate subgroup and the corank calculation use the literal U ≤ B.

Source: Aschbacher--Smith, printed p.670 (PDF p.687).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces
universe u
variable {G : Type u} [Group G] {L B : Subgroup G}
  {F : Type} [Field F]

noncomputable def quotientActor
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (t : normalizer (L : Set G)) : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) :=
  MulAut.congr e (QuotientGroup.congr _ _ (L.normalizerMonoidHom t)
    (characteristic_iff_map_eq.mp inferInstance _))

theorem quotientActor_mk
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (t : normalizer (L : Set G)) (l : L) :
    quotientActor e t (e (QuotientGroup.mk' (pCore 2 L) l)) =
      e (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom t l)) := by
  change e (QuotientGroup.congr _ _ _ _ (e.symm (e _))) = _
  rw [e.symm_apply_apply]
  rfl

variable [Algebra (ZMod 2) F]

noncomputable def vectorActor (f : B ≃* Multiplicative (Fin 2 → F))
    (t : normalizer (B : Set G)) : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F) :=
  let a : (Fin 2 → F) ≃+ (Fin 2 → F) :=
    (MulAut.congr f (B.normalizerMonoidHom t)).toAdditive
  a.toLinearEquiv (ZMod.map_smul a)

theorem vectorActor_coe (f : B ≃* Multiplicative (Fin 2 → F))
    (t : normalizer (B : Set G)) (v : Fin 2 → F) :
    ((f.symm (Multiplicative.ofAdd (vectorActor f t v))) : G) =
      (t : G) * (f.symm (Multiplicative.ofAdd v) : G) * (t : G)⁻¹ := by
  change ((f.symm (f (B.normalizerMonoidHom t (f.symm (Multiplicative.ofAdd v))))) : G) = _
  rw [f.symm_apply_apply]
  rfl

theorem vectorActor_intertwines
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (f : B ≃* Multiplicative (Fin 2 → F))
    (hf : ∀ (l : L) (v : B),
      ((f.symm (Multiplicative.ofAdd ((e (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec
        (Multiplicative.toAdd (f v))))) : G) = (l : G) * (v : G) * (l : G)⁻¹)
    (t : normalizer (L : Set G)) (ht : (t : G) ∈ normalizer (B : Set G)) :
    ∀ g v, vectorActor f ⟨t, ht⟩ (g.val.mulVec v) =
      (quotientActor e t g).val.mulVec (vectorActor f ⟨t, ht⟩ v) := by
  intro g v
  obtain ⟨q, rfl⟩ := e.surjective g
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  rw [quotientActor_mk]
  apply Multiplicative.ofAdd.injective
  apply f.symm.injective
  apply Subtype.ext
  rw [vectorActor_coe]
  have hn := hf l (f.symm (Multiplicative.ofAdd v))
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at hn
  rw [hn]
  have hn' := hf (L.normalizerMonoidHom t l)
    (f.symm (Multiplicative.ofAdd (vectorActor f ⟨t, ht⟩ v)))
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at hn'
  rw [hn', vectorActor_coe]
  change (t : G) * ((l : G) * (f.symm (Multiplicative.ofAdd v) : G) * (l : G)⁻¹) * (t : G)⁻¹ =
    ((t : G) * (l : G) * (t : G)⁻¹) *
      ((t : G) * (f.symm (Multiplicative.ofAdd v) : G) * (t : G)⁻¹) *
        ((t : G) * (l : G) * (t : G)⁻¹)⁻¹
  group

/-- The literal subgroup U, expressed in the chosen natural coordinates. -/
def coordinateSpace (f : B ≃* Multiplicative (Fin 2 → F)) (U : Subgroup G) :
    AddSubgroup (Fin 2 → F) where
  carrier := {v | (f.symm (Multiplicative.ofAdd v) : G) ∈ U}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change (f.symm (Multiplicative.ofAdd (v + w)) : G) ∈ U
    exact (by simpa using U.mul_mem hv hw)
  neg_mem' := by
    intro v hv
    change (f.symm (Multiplicative.ofAdd (-v)) : G) ∈ U
    exact (by simpa using U.inv_mem hv)

omit [Algebra (ZMod 2) F] in
@[simp] theorem mem_coordinateSpace (f : B ≃* Multiplicative (Fin 2 → F))
    (U : Subgroup G) (v : Fin 2 → F) :
    v ∈ coordinateSpace f U ↔ (f.symm (Multiplicative.ofAdd v) : G) ∈ U := Iff.rfl

omit [Algebra (ZMod 2) F] in
theorem coordinateSpace_card (f : B ≃* Multiplicative (Fin 2 → F))
    {U : Subgroup G} (hUB : U ≤ B) : Nat.card (coordinateSpace f U) = Nat.card U := by
  let e : U ≃ coordinateSpace f U := {
    toFun u := ⟨Multiplicative.toAdd (f ⟨u, hUB u.property⟩), by simp⟩
    invFun v := ⟨f.symm (Multiplicative.ofAdd v.val), v.property⟩
    left_inv u := by apply Subtype.ext; simp
    right_inv v := by apply Subtype.ext; simp }
  exact (Nat.card_congr e).symm

theorem vectorActor_fixed_iff (f : B ≃* Multiplicative (Fin 2 → F))
    (t : normalizer (B : Set G)) (v : Fin 2 → F) :
    vectorActor f t v = v ↔
      (f.symm (Multiplicative.ofAdd v) : G) ∈ centralizer ({(t : G)} : Set G) := by
  have he : vectorActor f t v = v ↔
      (t : G) * (f.symm (Multiplicative.ofAdd v) : G) * (t : G)⁻¹ =
        (f.symm (Multiplicative.ofAdd v) : G) := by
    rw [← vectorActor_coe]
    exact ((Subtype.val_injective.comp f.symm.injective).comp Multiplicative.ofAdd.injective).eq_iff.symm
  rw [he, mem_centralizer_singleton_iff]
  exact mul_inv_eq_iff_eq_mul.trans eq_comm

omit [Algebra (ZMod 2) F] in
theorem corank_half_card [Finite G] {U : Subgroup G} {n : ℕ}
    [IsElementaryAbelian 2 B] (hUB : U ≤ B)
    (hB : Nat.card B = 2 ^ (n * 2)) (hn : ChapterE.subgroupCorank B U = n) :
    Nat.card U = 2 ^ n := by
  have hi : U.relIndex B = 2 ^ n := by
    rw [Subgroup.relIndex_eq_two_pow_quotient_finrank,
      ← ChapterE.subgroupCorank_eq_quotient_finrank, hn]
  have hmul := (U.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv] at hmul
  change Nat.card U * U.relIndex B = Nat.card B at hmul
  rw [hi, hB, Nat.mul_comm n 2, two_mul, pow_add] at hmul
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ n) hmul

variable [Finite F] [CharP F 2]
omit [Algebra (ZMod 2) F] in
/-- Alignment of the genuine quotient actor supplies exactly the field witness
required in 6.1.13; no lift of an involution through the centralizer kernel is used. -/
theorem field_fixedSpace_of_outer_quotient
    {M U : Subgroup G} {n : ℕ}
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hF : Nat.card F = 2 ^ n)
    (t : normalizer (L : Set G)) (htM : (t : G) ∈ M)
    (htB : (t : G) ∈ normalizer (B : Set G))
    (hU : U = B ⊓ centralizer ({(t : G)} : Set G))
    (hsq : quotientActor e t ^ 2 = 1)
    (houter : ¬ ∃ g, quotientActor e t = MulAut.conj g) :
    IsInvolutoryFieldFixedSpace L M B U n := by
  obtain ⟨σ, hσne, hσsq, c, hc⟩ :=
    Representation.SL2NaturalOffenders.outer_involution_actor_alignment
      (quotientActor e t) hsq houter
  refine ⟨t, htM, htB, hU, F, inferInstance, inferInstance, inferInstance, hF,
    e.trans (MulAut.conj c⁻¹), σ, hσne, ?_, ?_⟩
  · ext x
    exact hσsq x
  · intro l
    simpa only [quotientActor_mk, MulEquiv.trans_apply] using
      hc (e (QuotientGroup.mk' (pCore 2 L) l))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces

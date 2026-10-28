module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryNatural
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Mathlib.FieldTheory.Fixed

/-!
# The centralizer of the involutory field plane

After simultaneous field alignment, a semilinear map fixing the field-fixed
plane pointwise fixes its coordinate basis. Its field automorphism fixes the
quadratic fixed field, so it is either identity or the original involution.
Transporting through the actual natural marking gives
C_P(U) = C_P(B)⟨t⟩. The ambient field witness may have order greater than two;
only its induced action is involutory.

Source: Aschbacher–Smith, 6.1.14(1), printed pp.670–671.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ConjugateFixedSpaces Representation.SL2NaturalOffenders.FixedField

private theorem aut_fixed_by_involution
    {F : Type} [Field F] [Finite F] (σ τ : F ≃+* F)
    (hσ : σ ≠ 1) (hs : σ ^ 2 = 1)
    (ht : ∀ x : F, σ x = x → τ x = x) : τ = 1 ∨ τ = σ := by
  classical
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  let H := zpowers σ
  let K := FixedPoints.subfield H F
  let a : F ≃ₐ[K] F := AlgEquiv.ofRingEquiv (f := τ) (by
    intro x
    exact ht x (x.property ⟨σ, mem_zpowers σ⟩))
  obtain ⟨s, hsa⟩ := FixedPoints.toAlgAut_surjective H F a
  have he : (s : F ≃+* F) = τ := by
    ext x
    exact DFunLike.congr_fun hsa x
  have ho : orderOf σ = 2 := orderOf_eq_prime hs hσ
  obtain ⟨k, hk, heq⟩ := (Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp s.property))
  have hk : k < orderOf σ := Finset.mem_range.mp hk
  rw [ho] at hk
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · exact Or.inl (he.symm.trans (by simpa using heq.symm))
  · exact Or.inr (he.symm.trans (by simpa using heq.symm))

private theorem semilinear_pointwise_fixed
    {F : Type} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F))
    (E D : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (hi : Function.Involutive E)
    (he : ∀ g v, E (g.val.mulVec v) = (a g).val.mulVec (E v))
    (ha : a ^ 2 = 1) (ho : ¬ ∃ g, a = MulAut.conj g)
    (τ : F ≃+* F) (hD : ∀ c v, D (c • v) = τ c • D v)
    (hfix : ∀ v, E v = v → D v = v) : D = 1 ∨ D = E := by
  classical
  obtain ⟨σ, hσ, hs, c, B, _, _, hB⟩ :=
    outer_involution_natural_alignment a E hi he ha ho
  let b := (Pi.basisFun F (Fin 2)).map B.symm
  have hb (j : Fin 2) : E (b j) = b j := by
    apply B.injective
    rw [hB]
    simp only [b, Module.Basis.map_apply, Pi.basisFun_apply, B.apply_symm_apply]
    ext k
    by_cases hk : k = j <;> simp [hk]
  have hdb (j : Fin 2) : D (b j) = b j := hfix _ (hb j)
  have hτ (x : F) (hx : σ x = x) : τ x = x := by
    have hxfix : E (x • b 0) = x • b 0 := by
      apply B.injective
      rw [hB, B.map_smul]
      simp only [b, Module.Basis.map_apply, Pi.basisFun_apply, B.apply_symm_apply]
      ext k
      by_cases hk : k = 0 <;> simp [hk, hx]
    have hh := hfix _ hxfix
    rw [hD, hdb] at hh
    exact (smul_left_injective F (b.ne_zero 0)) hh
  have hσsq : σ ^ 2 = 1 := by ext x; exact hs x
  have hcoord (v : Fin 2 → F) : B (D v) = fun j => τ (B v j) := by
    have hv : v = ∑ j : Fin 2, (B v j) • b j := by
      apply B.injective
      ext j
      fin_cases j <;> simp [b]
    have hdv : D v = ∑ j : Fin 2, τ (B v j) • b j := by
      conv_lhs => rw [hv]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hD, hdb]
    rw [hdv, map_sum]
    ext j
    fin_cases j <;> simp [b]
  rcases aut_fixed_by_involution σ τ hσ hσsq hτ with ht | ht
  · left
    apply LinearEquiv.ext
    intro v
    apply B.injective
    rw [hcoord, ht]
    rfl
  · right
    apply LinearEquiv.ext
    intro v
    apply B.injective
    rw [hcoord, ht, hB]

universe u
variable {G : Type u} [Group G] {L B U P : Subgroup G} {n : ℕ}

/-- An actor fixing the field plane has either trivial module action or
exactly the action of the supplied field witness. -/
theorem field_fixedSpace_actor_dichotomy
    (hnatural : IsNaturalModule L B n)
    (t : normalizer (L : Set G)) (htB : (t : G) ∈ normalizer (B : Set G))
    (hU : U = B ⊓ centralizer ({(t : G)} : Set G)) (hUne : U ≠ ⊥)
    (hfield : ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ n ∧
      ∃ (a : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) K)
        (σ : K ≃+* K), σ ≠ 1 ∧ σ ^ 2 = 1 ∧
        ∀ l : L,
          a (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom t l)) =
            Theory.PSL2.sl2FieldAut σ (a (QuotientGroup.mk' (pCore 2 L) l)))
    (r : normalizer (L : Set G)) (hrB : (r : G) ∈ normalizer (B : Set G))
    (hrU : (r : G) ∈ centralizer (U : Set G)) :
    B.normalizerMonoidHom ⟨r, hrB⟩ = 1 ∨
      B.normalizerMonoidHom ⟨r, hrB⟩ = B.normalizerMonoidHom ⟨t, htB⟩ := by
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨K, _, _, _, _, a, σ, hσ, hσsq, hσact⟩ := hfield
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
  obtain ⟨τ, hτ⟩ := Representation.OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
    (Representation.specialLinearNatural 2 (k := F))
    (fun k hk => Representation.SL2NaturalOffenders.centralizer_scalar k hk)
    (quotientActor e r) (vectorActor f ⟨r, hrB⟩)
    (vectorActor_intertwines e f hf r hrB)
  have hh := semilinear_pointwise_fixed (quotientActor e t)
    (vectorActor f ⟨t, htB⟩) (vectorActor f ⟨r, hrB⟩) hi
    (vectorActor_intertwines e f hf t htB) hasq haout τ hτ (by
      intro v hv
      have hvU : (f.symm (Multiplicative.ofAdd v) : G) ∈ U := by
        rw [hU]
        exact ⟨(f.symm _).property, (vectorActor_fixed_iff f ⟨t, htB⟩ _).mp hv⟩
      apply (vectorActor_fixed_iff f ⟨r, hrB⟩ _).mpr
      exact mem_centralizer_singleton_iff.mpr (hrU _ hvU))
  rcases hh with hh | hh
  · left
    apply MulEquiv.ext
    intro b
    have he := LinearEquiv.congr_fun hh (f b).toAdd
    apply Subtype.ext
    have hh := congrArg (fun v => (f.symm (Multiplicative.ofAdd v) : G)) he
    change (r : G) * (b : G) * (r : G)⁻¹ = (b : G)
    simpa only [vectorActor_coe, LinearEquiv.coe_one, id_eq, ofAdd_toAdd, f.symm_apply_apply] using hh
  · right
    apply MulEquiv.ext
    intro b
    have he := LinearEquiv.congr_fun hh (f b).toAdd
    apply Subtype.ext
    have hh := congrArg (fun v => (f.symm (Multiplicative.ofAdd v) : G)) he
    change (r : G) * (b : G) * (r : G)⁻¹ = (t : G) * (b : G) * (t : G)⁻¹
    simpa only [vectorActor_coe, ofAdd_toAdd, f.symm_apply_apply] using hh

/-- The literal centralizer formula in 6.1.14(1). It uses the original field
witness, which need not itself be an involution in the ambient group. -/
theorem field_fixedSpace_centralizer_eq_sup
    (hnatural : IsNaturalModule L B n)
    (hPL : P ≤ normalizer (L : Set G)) (hPB : P ≤ normalizer (B : Set G))
    (t : normalizer (L : Set G)) (htP : (t : G) ∈ P)
    (htB : (t : G) ∈ normalizer (B : Set G))
    (hU : U = B ⊓ centralizer ({(t : G)} : Set G)) (hUne : U ≠ ⊥)
    (hfield : ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ n ∧
      ∃ (a : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) K)
        (σ : K ≃+* K), σ ≠ 1 ∧ σ ^ 2 = 1 ∧
        ∀ l : L,
          a (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom t l)) =
            Theory.PSL2.sl2FieldAut σ (a (QuotientGroup.mk' (pCore 2 L) l))) :
    P ⊓ centralizer (U : Set G) = (P ⊓ centralizer (B : Set G)) ⊔ zpowers (t : G) := by
  apply le_antisymm
  · rintro r ⟨hrP, hrU⟩
    rcases field_fixedSpace_actor_dichotomy hnatural t htB hU hUne hfield
      ⟨r, hPL hrP⟩ (hPB hrP) hrU with hr | hr
    · apply mem_sup_left
      refine ⟨hrP, ?_⟩
      intro b hb
      have he := congrArg (fun a : MulAut B => (a ⟨b, hb⟩ : G)) hr
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · have hc : r * (t : G)⁻¹ ∈ P ⊓ centralizer (B : Set G) := by
        refine ⟨P.mul_mem hrP (P.inv_mem htP), ?_⟩
        have he : B.normalizerMonoidHom
            (⟨r, hPB hrP⟩ * (⟨t, htB⟩ : normalizer (B : Set G))⁻¹) = 1 := by
          rw [map_mul, map_inv, hr, mul_inv_cancel]
        intro b hb
        have hh := congrArg (fun a : MulAut B => (a ⟨b, hb⟩ : G)) he
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      have hh := mul_mem (mem_sup_left hc)
        (mem_sup_right (mem_zpowers (t : G)))
      simpa only [inv_mul_cancel_right] using hh
  · apply sup_le
    · exact inf_le_inf_left _ (centralizer_le (hU.le.trans inf_le_left))
    · apply zpowers_le.mpr
      refine ⟨htP, ?_⟩
      intro u hu
      exact mem_centralizer_singleton_iff.mp ((hU.le hu).2)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

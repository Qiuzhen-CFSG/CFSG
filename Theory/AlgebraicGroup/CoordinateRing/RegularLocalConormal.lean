module

public import Theory.AlgebraicGroup.CoordinateRing.RegularLocalDomain
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Conormal spaces of regular local quotients

For a surjection `P → R` of commutative regular local rings, this module proves
the conormal intersection identity
`ker(f) ⊓ maximalIdeal(P)² = maximalIdeal(P) * ker(f)`.  This is the content of
Stacks Project, Lemma 10.106.4 (tag 00NR), built on the regular-local domain
theorem from tag 00NP.

The proof lifts bases of the kernel and target of the induced cotangent map.
After quotienting `P` by the lifted kernel directions, the remaining directions
bound its embedding dimension by that of `R`.  Regularity forces equality of
Krull dimensions, while the domain theorem and the strict dimension drop for a
nonzero kernel force this intermediate quotient to be `R`.  Linear independence
of the lifted kernel directions then gives the stated intersection identity.

The final definitions express the resulting injection after extension from the
source residue field to any flat residue-field algebra.  In particular, for a
local surjection `P → R`, its domain is exactly
`ResidueField R ⊗[P] ker(algebraMap P R)`, the domain used by
`KaehlerDifferential.cotangentComplexBaseChange`; the pure-tensor formula
identifies it with the canonical conormal map.
-/

namespace Theory.AlgebraicGroup

open IsLocalRing
open TensorProduct

universe u

set_option linter.style.haveILetI false

variable {P R : Type u} [CommRing P] [CommRing R]
  [IsRegularLocalRing P] [IsRegularLocalRing R]

public theorem regularLocal_ker_inf_maximalIdeal_sq
    (f : P →+* R) (hf : Function.Surjective f) :
    RingHom.ker f ⊓ maximalIdeal P ^ 2 = maximalIdeal P * RingHom.ker f := by
  letI : Algebra P R := f.toAlgebra
  letI : IsLocalHom (algebraMap P R) := hf.isLocalHom
  let mP := maximalIdeal P
  let mR := maximalIdeal R
  let I := RingHom.ker f
  have halg : algebraMap P R = f := rfl
  have hI : I ≤ mP := by
    change RingHom.ker f ≤ maximalIdeal P
    rw [← maximalIdeal_comap f]
    exact Ideal.comap_mono bot_le
  have hcomap : mR.comap (algebraMap P R) =
      RingHom.ker (algebraMap P R) ⊔ mP := by
    rw [halg, maximalIdeal_comap f, sup_eq_right.mpr hI]
  have hmP_le : mP ≤ mR.comap (algebraMap P R) := by
    rw [hcomap]
    exact le_sup_right
  let cotMapP : mP.Cotangent →ₗ[P] mR.Cotangent :=
    Ideal.mapCotangent mP mR (Algebra.ofId P R) hmP_le
  letI : Module (ResidueField P) (CotangentSpace R) :=
    Module.compHom (CotangentSpace R)
      (algebraMap (ResidueField P) (ResidueField R))
  have hk_surj : Function.Surjective
      (algebraMap (ResidueField P) (ResidueField R)) := by
    intro r
    obtain ⟨r, rfl⟩ := residue_surjective r
    obtain ⟨p, rfl⟩ := hf r
    exact ⟨residue P p, by simp [halg]⟩
  let bR0 := Module.finBasis (ResidueField R) (CotangentSpace R)
  letI : Module.Finite (ResidueField P) (CotangentSpace R) :=
    ⟨Submodule.fg_def.mpr ⟨Set.range bR0, Set.finite_range _, by
      apply top_unique
      intro v _
      rw [← bR0.sum_repr v]
      apply Submodule.sum_mem
      intro i _
      obtain ⟨c, hc⟩ := hk_surj (bR0.repr v i)
      rw [← hc]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)⟩⟩
  let cotMap : CotangentSpace P →ₗ[ResidueField P] CotangentSpace R :=
    { cotMapP with
      map_smul' := by
        intro c v
        obtain ⟨p, rfl⟩ := residue_surjective c
        change cotMapP ((algebraMap P (ResidueField P) p) • v) =
          (algebraMap (ResidueField P) (ResidueField R) (residue P p)) • cotMapP v
        rw [IsScalarTower.algebraMap_smul (ResidueField P)]
        rw [show algebraMap (ResidueField P) (ResidueField R) (residue P p) =
          residue R (algebraMap P R p) by simp]
        change cotMapP (p • v) =
          (algebraMap R (ResidueField R) (algebraMap P R p)) • cotMapP v
        rw [IsScalarTower.algebraMap_smul (ResidueField R)]
        rw [IsScalarTower.algebraMap_smul R]
        exact cotMapP.map_smul p v }
  have hcot_surj : Function.Surjective cotMap := by
    exact Ideal.mapCotangent_surjective_of_comap_eq hf hcomap
  let bK := Module.finBasis (ResidueField P) (LinearMap.ker cotMap)
  have kernelLiftExists (i : Fin (Module.finrank (ResidueField P) (LinearMap.ker cotMap))) :
      ∃ x : mP, (x : P) ∈ I ∧ mP.toCotangent x = (bK i : CotangentSpace P) := by
    have hi : (bK i : CotangentSpace P) ∈
        (Submodule.comap mP.subtype (I ⊓ mP)).map mP.toCotangent := by
      have hi' : (bK i : CotangentSpace P) ∈
          (Submodule.comap mP.subtype
            (RingHom.ker (algebraMap P R) ⊓ mP)).map mP.toCotangent := by
        rw [← Ideal.mapCotangent_ker_of_surjective hf hcomap]
        change cotMap (bK i : CotangentSpace P) = 0
        exact LinearMap.mem_ker.mp (bK i).property
      simpa only [halg] using hi'
    rcases hi with ⟨x, hx, hxeq⟩
    change (x : P) ∈ I ⊓ mP at hx
    exact ⟨x, hx.1, hxeq⟩
  let x : Fin (Module.finrank (ResidueField P) (LinearMap.ker cotMap)) → mP :=
    fun i ↦ Classical.choose (kernelLiftExists i)
  have hxI (i) : (x i : P) ∈ I := (Classical.choose_spec (kernelLiftExists i)).1
  have hxCot (i) : mP.toCotangent (x i) = (bK i : CotangentSpace P) :=
    (Classical.choose_spec (kernelLiftExists i)).2

  let bR := Module.finBasis (ResidueField P) (CotangentSpace R)
  let z : Fin (Module.finrank (ResidueField P) (CotangentSpace R)) → CotangentSpace P :=
    fun i ↦ Function.surjInv hcot_surj (bR i)
  have hz (i) : cotMap (z i) = bR i := Function.surjInv_eq hcot_surj _
  let y : Fin (Module.finrank (ResidueField P) (CotangentSpace R)) → mP :=
    fun i ↦ Function.surjInv mP.toCotangent_surjective (z i)
  have hyCot (i) : mP.toCotangent (y i) = z i :=
    Function.surjInv_eq mP.toCotangent_surjective _

  have hspanK : Submodule.span (ResidueField P)
      (Set.range fun i ↦ (bK i : CotangentSpace P)) = LinearMap.ker cotMap := by
    calc
      _ = (Submodule.span (ResidueField P) (Set.range bK)).map
          (LinearMap.ker cotMap).subtype := by
            rw [Submodule.map_span]
            congr 1
            ext v
            simp
      _ = _ := by rw [bK.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hmapZ : (Submodule.span (ResidueField P) (Set.range z)).map cotMap = ⊤ := by
    rw [Submodule.map_span]
    apply top_unique
    rw [← bR.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨z i, ⟨i, rfl⟩, hz i⟩
  have hspanCot : Submodule.span (ResidueField P)
      (Set.range (fun i ↦ (bK i : CotangentSpace P)) ∪ Set.range z) = ⊤ := by
    apply top_unique
    intro v _
    have hvmap : cotMap v ∈
        (Submodule.span (ResidueField P) (Set.range z)).map cotMap := by
      rw [hmapZ]
      exact Submodule.mem_top
    rcases hvmap with ⟨w, hw, hwv⟩
    have hvw : v - w ∈ LinearMap.ker cotMap := by
      rw [LinearMap.mem_ker]
      simp [hwv]
    rw [← hspanK] at hvw
    rw [Submodule.span_union]
    simpa only [sub_add_cancel] using Submodule.add_mem _
      (Submodule.mem_sup_left hvw) (Submodule.mem_sup_right hw)

  have hspanCotLifts : Submodule.span (ResidueField P)
      (mP.toCotangent '' (Set.range x ∪ Set.range y)) = ⊤ := by
    rw [← hspanCot]
    congr 1
    ext v
    simp only [Set.mem_image, Set.mem_union, Set.mem_range]
    constructor
    · rintro ⟨a, (⟨i, rfl⟩ | ⟨i, rfl⟩), rfl⟩
      · exact Or.inl ⟨i, (hxCot i).symm⟩
      · exact Or.inr ⟨i, (hyCot i).symm⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨x i, Or.inl ⟨i, rfl⟩, hxCot i⟩
      · exact ⟨y i, Or.inr ⟨i, rfl⟩, hyCot i⟩
  have hspanMaxSubtype : Submodule.span P (Set.range x ∪ Set.range y) = ⊤ :=
    CotangentSpace.span_image_eq_top_iff.mp hspanCotLifts
  have hspanMax : Ideal.span
      (Set.range (fun i ↦ (x i : P)) ∪ Set.range (fun i ↦ (y i : P))) = mP := by
    have h := congrArg (Submodule.map mP.subtype) hspanMaxSubtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h
    have himage : mP.subtype '' (Set.range x ∪ Set.range y) =
        Set.range (fun i ↦ (x i : P)) ∪ Set.range (fun i ↦ (y i : P)) := by
      ext v
      constructor
      · rintro ⟨w, (⟨i, rfl⟩ | ⟨i, rfl⟩), rfl⟩
        · exact Or.inl ⟨i, rfl⟩
        · exact Or.inr ⟨i, rfl⟩
      · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact ⟨x i, Or.inl ⟨i, rfl⟩, rfl⟩
        · exact ⟨y i, Or.inr ⟨i, rfl⟩, rfl⟩
    rw [himage] at h
    exact h

  let J : Ideal P := Ideal.span (Set.range fun i ↦ (x i : P))
  let Y : Ideal P := Ideal.span (Set.range fun i ↦ (y i : P))
  have hJ : J ≤ I := Ideal.span_le.mpr fun _ ⟨i, hi⟩ ↦ hi ▸ hxI i
  have hJY : J ⊔ Y = mP := by
    change Ideal.span (Set.range fun i ↦ (x i : P)) ⊔
      Ideal.span (Set.range fun i ↦ (y i : P)) = mP
    rw [← Ideal.span_union, hspanMax]
  have hJtop : J ≠ ⊤ := by
    intro h
    have hItop : I = ⊤ := top_unique (h ▸ hJ)
    have hone : (1 : P) ∈ I := hItop.symm ▸ Submodule.mem_top
    have : f 1 = 0 := RingHom.mem_ker.mp hone
    exact one_ne_zero (f.map_one.symm.trans this)

  let Q := P ⧸ J
  let q : P →+* Q := Ideal.Quotient.mk J
  have hJker (a : P) (ha : a ∈ J) : f a = 0 := RingHom.mem_ker.mp (hJ ha)
  let qf : Q →+* R := Ideal.Quotient.lift J f hJker
  have hq_surj : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hqf_surj : Function.Surjective qf :=
    Ideal.Quotient.lift_surjective_of_surjective J hJker hf
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hJtop
  letI : IsLocalRing Q := IsLocalRing.of_surjective' q hq_surj
  have hmapMax : mP.map q = maximalIdeal Q :=
    map_maximalIdeal_of_surjective q hq_surj
  have hmapJ : J.map q = ⊥ := by
    rw [eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    change q a = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact ha
  have hspanQ : Ideal.span (Set.range fun i ↦ q (y i : P)) = maximalIdeal Q := by
    calc
      _ = Y.map q := by
        change Ideal.span (Set.range fun i ↦ q (y i : P)) =
          (Ideal.span (Set.range fun i ↦ (y i : P))).map q
        rw [Ideal.map_span]
        congr 1
        ext v
        simp
      _ = (J ⊔ Y).map q := by
        simp [Ideal.map_sup, hmapJ]
      _ = mP.map q := congrArg (fun K : Ideal P ↦ K.map q) hJY
      _ = _ := hmapMax
  have hspanFinrankQ : (maximalIdeal Q).spanFinrank ≤
      Module.finrank (ResidueField P) (CotangentSpace R) := by
    rw [← hspanQ]
    calc
      _ ≤ (Set.range fun i ↦ q (y i : P)).ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
      _ ≤ (Set.univ : Set (Fin (Module.finrank (ResidueField P) (CotangentSpace R)))).ncard := by
        simpa only [Set.image_univ] using
          (Set.ncard_image_le (s := Set.univ)
            (f := fun i ↦ q (y i : P)) Set.finite_univ)
      _ = Nat.card (Fin (Module.finrank (ResidueField P) (CotangentSpace R))) := by
        rw [Set.ncard_univ]
      _ = _ := Nat.card_fin _
  have hfinrankR : Module.finrank (ResidueField P) (CotangentSpace R) =
      Module.finrank (ResidueField R) (CotangentSpace R) := by
    simpa only [Module.finrank] using congrArg Cardinal.toNat
      (rank_eq_of_equiv_equiv
        (algebraMap (ResidueField P) (ResidueField R))
        (AddEquiv.refl (CotangentSpace R))
        ⟨RingHom.injective _, hk_surj⟩ (fun _ _ ↦ rfl))
  have hdimR : Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R :=
    (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
  have hdim_le : ringKrullDim R ≤ ringKrullDim Q :=
    ringKrullDim_le_of_surjective qf hqf_surj
  have hregQ_le : (maximalIdeal Q).spanFinrank ≤ ringKrullDim Q := by
    calc
      (↑(maximalIdeal Q).spanFinrank : WithBot ℕ∞) ≤
          Module.finrank (ResidueField P) (CotangentSpace R) := by exact_mod_cast hspanFinrankQ
      _ = Module.finrank (ResidueField R) (CotangentSpace R) := by exact_mod_cast hfinrankR
      _ = ringKrullDim R := hdimR
      _ ≤ ringKrullDim Q := hdim_le
  letI : IsRegularLocalRing Q := IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Q hregQ_le
  have hdimQ : ringKrullDim Q = ringKrullDim R := by
    apply le_antisymm
    · rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := Q)]
      calc
        (↑(maximalIdeal Q).spanFinrank : WithBot ℕ∞) ≤
            Module.finrank (ResidueField P) (CotangentSpace R) := by exact_mod_cast hspanFinrankQ
        _ = Module.finrank (ResidueField R) (CotangentSpace R) := by exact_mod_cast hfinrankR
        _ = ringKrullDim R := hdimR
    · exact hdim_le
  letI : IsDomain Q := Theory.AlgebraicGroup.isDomain_of_isRegularLocalRing Q
  have hqf_inj : Function.Injective qf := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hker
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have haNZ : a ∈ nonZeroDivisors Q := by simpa using ha0
    have hdrop := ringKrullDim_succ_le_of_surjective qf hqf_surj haNZ
      (RingHom.mem_ker.mp ha)
    rw [hdimQ, ← hdimR] at hdrop
    have hdropNat : Module.finrank (ResidueField R) (CotangentSpace R) + 1 ≤
        Module.finrank (ResidueField R) (CotangentSpace R) := by
      exact_mod_cast hdrop
    omega
  have hJI : J = I := le_antisymm hJ fun a ha ↦ by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hqf_inj
    rw [map_zero]
    exact RingHom.mem_ker.mp ha

  apply le_antisymm
  · intro a ha
    have haJ : a ∈ J := hJI ▸ ha.1
    obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun.mp haJ)
    have hsumSubtype :
        (⟨∑ i, c i * (x i : P), by rw [hc]; exact hI ha.1⟩ : mP) = ⟨a, hI ha.1⟩ := by
      exact Subtype.ext hc
    have hsumCot : (∑ i, residue P (c i) • (bK i : CotangentSpace P)) = 0 := by
      have hterm (i) : mP.toCotangent (c i • x i) =
          residue P (c i) • (bK i : CotangentSpace P) := by
        rw [map_smul, hxCot]
        simpa only [ResidueField.algebraMap_eq] using
          (IsScalarTower.algebraMap_smul (ResidueField P) (c i)
            (bK i : CotangentSpace P)).symm
      calc
        _ = mP.toCotangent (∑ i, c i • x i) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ (hterm i).symm
        _ = mP.toCotangent
            (⟨∑ i, c i * (x i : P), by rw [hc]; exact hI ha.1⟩ : mP) := by
          apply congrArg mP.toCotangent
          apply Subtype.ext
          simp
        _ = mP.toCotangent ⟨a, hI ha.1⟩ := congrArg mP.toCotangent hsumSubtype
        _ = 0 := (Ideal.toCotangent_eq_zero mP ⟨a, hI ha.1⟩).mpr ha.2
    have hlinK : LinearIndependent (ResidueField P)
        (fun i ↦ (bK i : CotangentSpace P)) :=
      bK.linearIndependent.map' (LinearMap.ker cotMap).subtype
        (Submodule.ker_subtype (LinearMap.ker cotMap))
    have hcMax (i) : c i ∈ mP := by
      apply (residue_eq_zero_iff (c i)).mp
      exact Fintype.linearIndependent_iff.mp hlinK
        (fun i ↦ residue P (c i)) hsumCot i
    rw [← hc]
    exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_mul (hcMax i) (hxI i)
  · intro a ha
    exact ⟨by
        have : mP * I ≤ I := by
          simpa using Ideal.mul_mono_left (I := mP) (J := ⊤) (K := I) le_top
        exact this ha,
      by
        simpa [pow_two] using (Ideal.mul_mono_right (I := mP) hI) ha⟩

private def conormalToCotangent (I : Ideal P)
    (hI : I ≤ maximalIdeal P) :
    I →ₗ[P] (maximalIdeal P).Cotangent :=
  (maximalIdeal P).toCotangent.comp (Submodule.inclusion hI)

private lemma ker_conormalToCotangent (I : Ideal P)
    (hI : I ≤ maximalIdeal P)
    (hinter : I ⊓ maximalIdeal P ^ 2 = maximalIdeal P * I) :
    LinearMap.ker (conormalToCotangent I hI) =
      maximalIdeal P • (⊤ : Submodule P I) := by
  ext x
  simp only [LinearMap.mem_ker, conormalToCotangent, LinearMap.comp_apply,
    Submodule.inclusion_apply, Ideal.toCotangent_eq_zero,
    Submodule.mem_smul_top_iff]
  change (x : P) ∈ maximalIdeal P ^ 2 ↔ (x : P) ∈ maximalIdeal P * I
  rw [← hinter]
  simp only [Ideal.mem_inf, x.property, true_and]

private noncomputable def conormalTensorToCotangent (I : Ideal P)
    (hI : I ≤ maximalIdeal P) :
    TensorProduct P (ResidueField P) I →ₗ[ResidueField P] CotangentSpace P :=
  LinearMap.liftBaseChange (ResidueField P) (conormalToCotangent I hI)

private lemma conormalTensorToCotangent_injective (I : Ideal P)
    (hI : I ≤ maximalIdeal P)
    (hinter : I ⊓ maximalIdeal P ^ 2 = maximalIdeal P * I) :
    Function.Injective (conormalTensorToCotangent I hI) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ :=
      TensorProduct.mk_surjective P I (ResidueField P)
        Ideal.Quotient.mk_surjective z
    rw [LinearMap.mem_ker] at hz
    change (LinearMap.liftBaseChange (ResidueField P)
      (conormalToCotangent I hI)) (1 ⊗ₜ[P] x) = 0 at hz
    rw [LinearMap.liftBaseChange_one_tmul] at hz
    have hx : x ∈ maximalIdeal P • (⊤ : Submodule P I) := by
      rw [← ker_conormalToCotangent I hI hinter]
      exact hz
    change (1 ⊗ₜ[P] x : TensorProduct P (ResidueField P) I) = 0
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      have hr0 : algebraMap P (ResidueField P) r = 0 := by
        rw [ResidueField.algebraMap_eq, residue_eq_zero_iff]
        exact hr
      rw [TensorProduct.tmul_smul]
      rw [← IsScalarTower.algebraMap_smul (A := ResidueField P) r,
        hr0, zero_smul]
    · intro x y hx hy
      rw [TensorProduct.tmul_add, hx, hy, add_zero]
  · exact bot_le

private noncomputable def conormalBaseChangeToCotangent
    (A : Type u) [CommRing A] [Algebra P A] [Algebra (ResidueField P) A]
    [IsScalarTower P (ResidueField P) A]
    (I : Ideal P) (hI : I ≤ maximalIdeal P) :
    TensorProduct P A I →ₗ[A]
      TensorProduct (ResidueField P) A (CotangentSpace P) :=
  (conormalTensorToCotangent I hI).baseChange A ∘ₗ
    (AlgebraTensorModule.cancelBaseChange P (ResidueField P) A A I).symm.toLinearMap

private lemma conormalBaseChangeToCotangent_injective
    (A : Type u) [CommRing A] [Algebra P A] [Algebra (ResidueField P) A]
    [IsScalarTower P (ResidueField P) A] [Module.Flat (ResidueField P) A]
    (I : Ideal P) (hI : I ≤ maximalIdeal P)
    (hinter : I ⊓ maximalIdeal P ^ 2 = maximalIdeal P * I) :
    Function.Injective (conormalBaseChangeToCotangent A I hI) := by
  rw [conormalBaseChangeToCotangent]
  let g := conormalTensorToCotangent I hI
  have hgl : Function.Injective (g.lTensor A) :=
    Module.Flat.lTensor_preserves_injective_linearMap g
      (conormalTensorToCotangent_injective I hI hinter)
  intro x y hxy
  apply (AlgebraTensorModule.cancelBaseChange P (ResidueField P) A A I).symm.injective
  apply hgl
  exact hxy

section TargetResidueField

variable [Algebra P R] [IsLocalHom (algebraMap P R)]

public theorem ker_algebraMap_le_maximalIdeal :
    RingHom.ker (algebraMap P R) ≤ maximalIdeal P := by
  rw [← maximalIdeal_comap (algebraMap P R)]
  exact Ideal.comap_mono bot_le

/-- The conormal map after extension to the target residue field.  Its domain
is definitionally the domain of `KaehlerDifferential.cotangentComplexBaseChange`. -/
public noncomputable def regularLocalConormalToCotangentBaseChange :
    TensorProduct P (ResidueField R) (RingHom.ker (algebraMap P R)) →ₗ[ResidueField R]
      TensorProduct (ResidueField P) (ResidueField R) (CotangentSpace P) :=
  conormalBaseChangeToCotangent (ResidueField R) (RingHom.ker (algebraMap P R))
    ker_algebraMap_le_maximalIdeal

@[simp]
public theorem regularLocalConormalToCotangentBaseChange_tmul
    (a : ResidueField R) (x : RingHom.ker (algebraMap P R)) :
    regularLocalConormalToCotangentBaseChange (P := P) (R := R) (a ⊗ₜ[P] x) =
      a ⊗ₜ[ResidueField P]
        (maximalIdeal P).toCotangent ⟨x, ker_algebraMap_le_maximalIdeal x.property⟩ := by
  simp [regularLocalConormalToCotangentBaseChange, conormalBaseChangeToCotangent,
    conormalTensorToCotangent, conormalToCotangent]
  congr 1

public theorem regularLocalConormalToCotangentBaseChange_injective
    (hf : Function.Surjective (algebraMap P R)) :
    Function.Injective
      (regularLocalConormalToCotangentBaseChange (P := P) (R := R)) := by
  exact conormalBaseChangeToCotangent_injective (ResidueField R)
    (RingHom.ker (algebraMap P R)) ker_algebraMap_le_maximalIdeal
    (regularLocal_ker_inf_maximalIdeal_sq (algebraMap P R) hf)

end TargetResidueField

end Theory.AlgebraicGroup

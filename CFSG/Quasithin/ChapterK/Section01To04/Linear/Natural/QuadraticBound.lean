module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The lower bound for quadratic natural linear actors

A quadratic subgroup of SL(V) embeds, by its displacement maps, in
Hom_F(V/C_V(A), C_V(A)). Faithfulness makes C_V(A) proper. Counting this
space over F and restricting scalars to F₂ gives
m(A) ≤ (n-1) m(V/C_V(A)), hence the sharp candidate lower bound 1/(n-1).
The actual ambient action is connected to this calculation in Natural.

This argument applies in every dimension at least two. It supplies the inner
quadratic-actor bound in Aschbacher–Smith, K.3.2.1, printed pp.454–455
(combined manuscript, 1 March 2004). It does not exclude outer actors.
-/

@[expose] public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped ENNReal
namespace CFSG.Quasithin.ChapterK.Linear.Natural

variable (F : BinaryField) (n : ℕ)

lemma field_finrank : Module.finrank (ZMod 2) F.Carrier = F.degree := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
  rw [Nat.card_zmod, F.card_eq] at h
  exact (Nat.pow_right_injective (by decide : 1 < 2) h).symm

lemma natural_injective : Function.Injective (linearNatural F n) := by
  intro g h he
  apply specialLinearNatural_injective n
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun he v

noncomputable abbrev fieldFixedSpace (A : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)) :=
  Representation.invariants ((specialLinearNatural (k := F.Carrier) n).comp A.subtype)

lemma fixedCodim_eq_field_codim (A : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)) :
    fixedCodim (linearNatural F n) A = F.degree *
      Module.finrank F.Carrier ((Fin n → F.Carrier) ⧸ fieldFixedSpace F n A) := by
  change Module.finrank (ZMod 2) ((Fin n → F.Carrier) ⧸
    (fieldFixedSpace F n A).restrictScalars (ZMod 2)) = _
  rw [(Submodule.Quotient.restrictScalarsEquiv (ZMod 2) (fieldFixedSpace F n A)).finrank_eq,
    ← Module.finrank_mul_finrank (ZMod 2) F.Carrier, field_finrank]

lemma fieldFixedSpace_ne_top {A : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)}
    (hA : A ≠ ⊥) : fieldFixedSpace F n A ≠ ⊤ := by
  intro ht
  apply hA
  apply le_antisymm _ bot_le
  intro a ha
  change a = 1
  apply natural_injective F n
  apply LinearMap.ext
  intro v
  have hv : v ∈ fieldFixedSpace F n A := ht ▸ Submodule.mem_top
  rw [map_one, Module.End.one_apply]
  change specialLinearNatural (k := F.Carrier) n a v = v
  exact hv ⟨a, ha⟩

lemma quadratic_rank_bound {A : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)}
    (hA : A ≠ ⊥) (hq : IsQuadratic (linearNatural F n) A) :
    rank A ≤ fixedCodim (linearNatural F n) A * (n - 1) := by
  classical
  let C := fieldFixedSpace F n A
  let σ := specialLinearNatural (k := F.Carrier) n
  let d (a : A) : (Fin n → F.Carrier) →ₗ[F.Carrier] C :=
    (σ a - LinearMap.id).codRestrict C (fun v b => hq b b.property a a.property v)
  have hd (a : A) : C ≤ (d a).ker := by
    intro v hv
    apply Subtype.ext
    exact sub_eq_zero.mpr (hv a)
  let f (a : A) : ((Fin n → F.Carrier) ⧸ C) →ₗ[F.Carrier] C := C.liftQ (d a) (hd a)
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply specialLinearNatural_injective n
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun l : ((Fin n → F.Carrier) ⧸ C) →ₗ[F.Carrier] C =>
      (l (C.mkQ v) : Fin n → F.Carrier)) he
    change σ a v - v = σ b v - v at hv
    exact sub_left_injective hv
  let : Finite (((Fin n → F.Carrier) ⧸ C) →ₗ[F.Carrier] C) :=
    Module.finite_of_finite F.Carrier
  have hc := Nat.card_le_card_of_injective f hf
  rw [Module.natCard_eq_pow_finrank (K := F.Carrier)
    (V := ((Fin n → F.Carrier) ⧸ C) →ₗ[F.Carrier] C),
    Module.finrank_linearMap, F.card_eq, ← pow_mul] at hc
  have hl := Nat.log_monotone (b := 2) hc
  rw [Nat.log_pow (by decide : 1 < 2)] at hl
  change rank A ≤ F.degree *
    (Module.finrank F.Carrier ((Fin n → F.Carrier) ⧸ C) * Module.finrank F.Carrier C) at hl
  have hC : Module.finrank F.Carrier C ≤ n - 1 := by
    have hh := Submodule.finrank_lt (fieldFixedSpace_ne_top F n hA)
    simp only [Module.finrank_pi, Fintype.card_fin] at hh
    change Module.finrank F.Carrier C < n at hh
    omega
  calc
    rank A ≤ F.degree *
        (Module.finrank F.Carrier ((Fin n → F.Carrier) ⧸ C) * Module.finrank F.Carrier C) := hl
    _ ≤ F.degree * (Module.finrank F.Carrier ((Fin n → F.Carrier) ⧸ C) * (n - 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hC)
    _ = fixedCodim (linearNatural F n) A * (n - 1) := by
      rw [fixedCodim_eq_field_codim]
      exact (Nat.mul_assoc _ _ _).symm

lemma quadratic_actionRatio_ge (hn : 2 ≤ n)
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)}
    (hA : IsElementaryTwo A) (hq : IsQuadratic (linearNatural F n) A) :
    1 / (n - 1 : ℕ) ≤ actionRatio (linearNatural F n) A := by
  have hr : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA.rank_pos)
  have hn' : ((n - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
  unfold actionRatio
  apply (ENNReal.le_div_iff_mul_le (Or.inl hr) (Or.inl (by simp))).mpr
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  apply (ENNReal.div_le_iff hn' (by simp)).mpr
  exact_mod_cast quadratic_rank_bound F n hA.1 hq

lemma quadraticRatio_ge (hn : 2 ≤ n) :
    1 / (n - 1 : ℕ) ≤ quadraticRatio (linearNatural F n) := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA, hq⟩
  exact quadratic_actionRatio_ge F n hn hA hq

end CFSG.Quasithin.ChapterK.Linear.Natural

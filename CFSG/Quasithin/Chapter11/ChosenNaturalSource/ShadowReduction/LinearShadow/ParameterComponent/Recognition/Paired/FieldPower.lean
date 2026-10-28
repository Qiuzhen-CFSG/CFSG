module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.Torsion
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Common field powers on marked Cartan torsion

An invertible triangular semilinear operator conjugates a diagonal subgroup
by its coefficient automorphism: the intertwining identity on diagonal
entries gives this after cancellation of each nonzero diagonal entry of
the operator. This works for a subgroup of the torus and does not assume
that the torus itself is normalized.

Every automorphism of a finite binary field is one Frobenius power.
Faithfulness of the actual matrix marking therefore gives the same power
on all p-torsion elements in the literal L/O₂(L). The odd-primary
injectivity from Torsion lifts it to the original ambient subgroup.
The conjugation convention is x ↦ t*x*t⁻¹ in every displayed identity.

The source owner must still construct the compatible Cartan coordinates
and triangular semilinear operator from the actual SL₃/Sp₄ marking.
They are geometric inputs here; no downstream natural marking of the
outside component is imported or assumed.
Source: Aschbacher--Smith, 11.3.5(2), printed pp.771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Matrix
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
variable {G : Type*} [Group G]

/-- The automorphism of the literal component quotient induced by t.
Conjugation is explicitly x ↦ t*x*t⁻¹ throughout this argument. -/
def quotientConjugation (L : Subgroup G) (t : G) (ht : t ∈ normalizer (L : Set G)) :
    MulAut (L ⧸ pCore 2 L) :=
  let e : L ≃* L := ((MulAut.conj t).subgroupMap L).trans
    (MulEquiv.subgroupCongr (mem_normalizer_iff_map_conj_eq.mp ht))
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

theorem quotientConjugation_mk (L : Subgroup G) (t : G)
    (ht : t ∈ normalizer (L : Set G)) (x : L) :
    quotientConjugation L t ht (QuotientGroup.mk' (pCore 2 L) x) =
      QuotientGroup.mk' (pCore 2 L) ⟨t*x*t⁻¹,(ht x).mp x.property⟩ := rfl

private theorem common_frobenius {F : Type*} [Field F] [Finite F] [CharP F 2]
    (σ : F ≃+* F) : ∃ j : ℕ, ∀ x : F, σ x = x ^ (2 ^ j) := by
  let : Fintype F := Fintype.ofFinite F
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let σ' : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := σ) (by
    intro x
    have h : σ.toRingHom.comp (algebraMap (ZMod 2) F) = algebraMap (ZMod 2) F :=
      RingHom.ext_zmod _ _
    exact DFunLike.congr_fun h x)
  obtain ⟨j,hj⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    (ZMod 2) F).surjective σ'
  refine ⟨j,fun x => ?_⟩
  have hx := DFunLike.congr_fun hj x
  change (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ (j : ℕ)) x = σ x at hx
  simpa only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    pow_iterate, ZMod.card] using hx.symm

/-- A single coefficient-field automorphism on marked diagonal matrices
gives one common power on the original quotient p-torsion. This statement
retains both the faithful matrix marking and its actual conjugation identity. -/
theorem primeTorsion_quotient_field_power
    {F ι : Type*} [Field F] [Finite F] [CharP F 2] [Fintype ι] [DecidableEq ι]
    (A L : Subgroup G) (p : ℕ) (hL : primeTorsion A p ≤ L)
    (t : G) (htA : t ∈ normalizer (A : Set G)) (htL : t ∈ normalizer (L : Set G))
    (ρ : (L ⧸ pCore 2 L) →* Matrix ι ι F) (hρ : Function.Injective ρ)
    (σ : F ≃+* F)
    (hdiag : ∀ x : L, (x : G) ∈ primeTorsion A p →
      ∃ d : ι → F, ρ (QuotientGroup.mk' (pCore 2 L) x) = diagonal d)
    (hfield : ∀ x : L, (x : G) ∈ primeTorsion A p →
      ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) x)) =
        (ρ (QuotientGroup.mk' (pCore 2 L) x)).map σ) :
    ∃ j : ℕ, ∀ (x : G) (hx : x ∈ primeTorsion A p),
      QuotientGroup.mk' (pCore 2 L)
        ⟨t*x*t⁻¹,hL ((primeTorsion_normalizer A p htA x).mp hx)⟩ =
          (QuotientGroup.mk' (pCore 2 L) ⟨x,hL hx⟩) ^ (2 ^ j) := by
  obtain ⟨j,hj⟩ := common_frobenius σ
  refine ⟨j,fun x hx => ?_⟩
  let a : L := ⟨x,hL hx⟩
  obtain ⟨d,hd⟩ := hdiag a hx
  apply hρ
  rw [map_pow]
  change ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) a)) = _
  rw [hfield a hx,hd,diagonal_map (map_zero σ),diagonal_pow]
  congr 1
  funext i
  exact hj (d i)

/-- An invertible triangular semilinear operator normalizing the marked
diagonal p-torsion acts on it by its coefficient automorphism. Comparing
diagonal entries proves this even when the subgroup is smaller than the
full torus. No scalar-action hypothesis is used. -/
theorem primeTorsion_field_action_of_triangular
    {F ι : Type*} [Field F] [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    (A L : Subgroup G) (p : ℕ) (hL : primeTorsion A p ≤ L)
    (t : G) (htA : t ∈ normalizer (A : Set G)) (htL : t ∈ normalizer (L : Set G))
    (ρ : (L ⧸ pCore 2 L) →* Matrix ι ι F) (σ : F ≃+* F)
    (g : Matrix ι ι F) (hg : g.IsUpperTriangular) (hdet : g.det ≠ 0)
    (hdiag : ∀ x : L, (x : G) ∈ primeTorsion A p →
      ∃ d : ι → F, ρ (QuotientGroup.mk' (pCore 2 L) x) = diagonal d)
    (hint : ∀ x : L, (x : G) ∈ primeTorsion A p →
      g * (ρ (QuotientGroup.mk' (pCore 2 L) x)).map σ =
        ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) x)) * g) :
    ∀ x : L, (x : G) ∈ primeTorsion A p →
      ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) x)) =
        (ρ (QuotientGroup.mk' (pCore 2 L) x)).map σ := by
  have hn : ∀ i, g i i ≠ 0 := by
    rw [det_of_isUpperTriangular hg, Finset.prod_ne_zero_iff] at hdet
    exact fun i => hdet i (Finset.mem_univ i)
  intro x hx
  let y : L := ⟨t*x*t⁻¹,hL ((primeTorsion_normalizer A p htA x).mp hx)⟩
  obtain ⟨d,hd⟩ := hdiag x hx
  obtain ⟨e,he⟩ := hdiag y ((primeTorsion_normalizer A p htA x).mp hx)
  have he' : ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) x)) =
      diagonal e := he
  have hi := hint x hx
  rw [hd, he', diagonal_map (map_zero σ)] at hi ⊢
  congr 1
  funext i
  apply mul_right_cancel₀ (hn i)
  have hii := congrArg (fun z : Matrix ι ι F => z i i) hi
  simp only [mul_diagonal, diagonal_mul] at hii
  exact hii.symm.trans (mul_comm _ _)

/-- The source flag and semilinear intertwiner determine the same power
on every coordinate of the p-torsion in the original quotient. -/
theorem primeTorsion_quotient_field_power_of_triangular
    {F ι : Type*} [Field F] [Finite F] [CharP F 2]
    [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    (A L : Subgroup G) (p : ℕ) (hL : primeTorsion A p ≤ L)
    (t : G) (htA : t ∈ normalizer (A : Set G)) (htL : t ∈ normalizer (L : Set G))
    (ρ : (L ⧸ pCore 2 L) →* Matrix ι ι F) (hρ : Function.Injective ρ)
    (σ : F ≃+* F) (g : Matrix ι ι F) (hg : g.IsUpperTriangular) (hdet : g.det ≠ 0)
    (hdiag : ∀ x : L, (x : G) ∈ primeTorsion A p →
      ∃ d : ι → F, ρ (QuotientGroup.mk' (pCore 2 L) x) = diagonal d)
    (hint : ∀ x : L, (x : G) ∈ primeTorsion A p →
      g * (ρ (QuotientGroup.mk' (pCore 2 L) x)).map σ =
        ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) x)) * g) :
    ∃ j : ℕ, ∀ (x : G) (hx : x ∈ primeTorsion A p),
      QuotientGroup.mk' (pCore 2 L)
        ⟨t*x*t⁻¹,hL ((primeTorsion_normalizer A p htA x).mp hx)⟩ =
          (QuotientGroup.mk' (pCore 2 L) ⟨x,hL hx⟩) ^ (2 ^ j) :=
  primeTorsion_quotient_field_power A L p hL t htA htL ρ hρ σ hdiag
    (primeTorsion_field_action_of_triangular A L p hL t htA htL ρ σ g hg hdet hdiag hint)

/-- The matrix field action contradicts a mixed action on the actual odd
p-torsion, without replacing that subgroup or changing its conjugator. -/
theorem no_mixed_action_of_diagonal_field
    {F ι : Type*} [Field F] [Finite F] [CharP F 2] [Fintype ι] [DecidableEq ι]
    (A L : Subgroup G) [IsMulCommutative A] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hL : primeTorsion A p ≤ L) (t : G)
    (htA : t ∈ normalizer (A : Set G)) (htL : t ∈ normalizer (L : Set G))
    (ρ : (L ⧸ pCore 2 L) →* Matrix ι ι F) (hρ : Function.Injective ρ)
    (σ : F ≃+* F)
    (hdiag : ∀ x : L, (x : G) ∈ primeTorsion A p →
      ∃ d : ι → F, ρ (QuotientGroup.mk' (pCore 2 L) x) = diagonal d)
    (hfield : ∀ x : L, (x : G) ∈ primeTorsion A p →
      ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) x)) =
        (ρ (QuotientGroup.mk' (pCore 2 L) x)).map σ)
    (hm : ¬ primeTorsion A p ≤ centralizer ({t} : Set G))
    (hf : primeTorsion A p ⊓ centralizer ({t} : Set G) ≠ ⊥) : False := by
  obtain ⟨j,hj⟩ := primeTorsion_quotient_field_power A L p hL t htA htL ρ hρ σ hdiag hfield
  exact no_mixed_action_of_quotient_power A L p (2 ^ j) hp2 hL t htA hj hm hf

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired

module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RootObstructions

/-!
# Four square tests in the first G₂ parabolic

In the five-root radical, the square of a chart element is
A(b e + c d). Conjugating a radical element by another radical element
changes only its central coordinate. Thus radical perturbations of an actor
do not affect these commutator-square tests.

The B(1) test excludes the open short-root Bruhat cell. In the other cell,
the E(1) test removes its short-root parameter. The C(1)D(1) and B(1)E(1)
tests then remove both parameters of the full split torus. Consequently an
actor in either displayed cell passing all four tests lies in the radical.
The normal-form construction and the placement of the four test elements in
the actual derived parabolic's two-core are proved separately.

Source: the relative-block check in Aschbacher–Smith 2.3.9(7), printed p.526.
Root coordinates and conjugation identities are from the licensed ATLAS port
(LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
-/

@[expose] public section

open Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.FirstActor
variable {F : Type*} [Field F] [CharP F 2]

private theorem three_eq_one : (3 : F) = 1 := by
  have h := CharTwo.two_eq_zero (R := F)
  linear_combination h

private theorem chart_square (t : Fin 6 → F) (ht : t 5 = 0) :
    unipotentProduct t ^ 2 = rootA (t 1 * t 4 + t 2 * t 3) := by
  rw [fiveRoot_square t ht, CharTwo.neg_eq, three_eq_one, one_mul]

private theorem chart_square_mul_inv (t u : Fin 6 → F) (ht : t 5 = 0) (hu : u 5 = 0) :
    (unipotentProduct t * (unipotentProduct u)⁻¹) ^ 2 =
      rootA ((t 1 + u 1) * (t 4 + u 4) + (t 2 + u 2) * (t 3 + u 3)) := by
  rw [unipotentProduct_inv, unipotentProduct_mul, chart_square]
  · simp [unipotentProductParameters, unipotentInverseParameters, ht, hu, CharTwo.neg_eq,
      add_comm]
  · simp [unipotentProductParameters, unipotentInverseParameters, ht, hu]

private theorem chart_square_conjugate (t u v : Fin 6 → F)
    (ht : t 5 = 0) (hu : u 5 = 0) (hv : v 5 = 0) :
    (unipotentProduct t *
      (unipotentProduct v * unipotentProduct u * (unipotentProduct v)⁻¹)⁻¹) ^ 2 =
      (unipotentProduct t * (unipotentProduct u)⁻¹) ^ 2 := by
  rw [unipotentProduct_inv, unipotentProduct_mul, unipotentProduct_mul,
    chart_square_mul_inv, chart_square_mul_inv t u ht hu]
  · congr 1
    simp [unipotentProductParameters, unipotentInverseParameters, hu, hv]
  · exact ht
  · simp [unipotentProductParameters, unipotentInverseParameters, hu, hv]

private theorem radical_perturbation {q r g : Model F} (hq : q ∈ radical₁)
    (hr : r ∈ radical₁) (hg : g * q * g⁻¹ ∈ radical₁) :
    ⁅q, r * g⁆ ^ 2 = ⁅q, g⁆ ^ 2 := by
  obtain ⟨t,ht,he⟩ := hq
  obtain ⟨u,hu,hf⟩ := hg
  obtain ⟨v,hv,hk⟩ := hr
  have h1 : ⁅q,r*g⁆ = q * (r * (g*q*g⁻¹) * r⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  have h2 : ⁅q,g⁆ = q * (g*q*g⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [h1,h2,← hf,← he,← hk]
  exact chart_square_conjugate t u v ht hu hv

private theorem chart_commutator_square (t u : Fin 6 → F) (ht : t 5 = 0) (hu : u 5 = 0)
    (g : Model F) (hg : g * unipotentProduct t * g⁻¹ = unipotentProduct u) :
    ⁅unipotentProduct t,g⁆ ^ 2 =
      rootA ((t 1 + u 1) * (t 4 + u 4) + (t 2 + u 2) * (t 3 + u 3)) := by
  have h : ⁅unipotentProduct t,g⁆ = unipotentProduct t * (unipotentProduct u)⁻¹ := by
    rw [← hg, commutatorElement_def]; group
  rw [h, chart_square_mul_inv t u ht hu]

omit [CharP F 2] in
private theorem conj_mul (x y q : Model F) :
    (x*y)*q*(x*y)⁻¹ = x*(y*q*y⁻¹)*x⁻¹ := by group

omit [CharP F 2] in
private theorem rootF_conjugate_rootB (a b : F) :
    rootF a * rootB b * (rootF a)⁻¹ = rootB b := by
  rw [← rootF_neg]
  have he : rootF a = unipotentProduct ![0,0,0,0,0,a] := by simp [unipotentProduct]
  have hf : rootB b = unipotentProduct ![0,b,0,0,0,0] := by simp [unipotentProduct]
  rw [he,hf,show rootF (-a) = unipotentProduct ![0,0,0,0,0,-a] by simp [unipotentProduct],
    unipotentProduct_mul,unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> simp [unipotentProductParameters]

private theorem rootF_conjugate_rootE_chart (a c : F) :
    rootF a * rootE c * (rootF a)⁻¹ =
      unipotentProduct ![c^2*a^3,c*a^3,c*a^2,c*a,c,0] := by
  rw [← rootF_neg, rootF_conjugate_rootE]
  simp [unipotentProduct, CharTwo.neg_eq]

def bigLevi (a b : F) (l m : Fˣ) : Model F :=
  rootF a * weylS * rootF b * torus l m

def smallLevi (a : F) (l m : Fˣ) : Model F := rootF a * torus l m

private theorem big_conjugate_B (a b : F) (l m : Fˣ) :
    bigLevi a b l m * rootB 1 * (bigLevi a b l m)⁻¹ =
      unipotentProduct ![((l:F)^2/(m:F))^2*a^3,
        ((l:F)^2/(m:F))*a^3,((l:F)^2/(m:F))*a^2,
        ((l:F)^2/(m:F))*a,(l:F)^2/(m:F),0] := by
  rw [bigLevi, conj_mul, torus_rootB, mul_one, conj_mul, rootF_conjugate_rootB,
    conj_mul, weylS_rootB, rootF_conjugate_rootE_chart]

private theorem big_commutator_B (a b : F) (l m : Fˣ) :
    ⁅rootB (1 : F), bigLevi a b l m⁆ ^ 2 = rootA ((l:F)^2/(m:F)) := by
  have h := chart_commutator_square (![0,1,0,0,0,0] : Fin 6 → F)
    ![((l:F)^2/(m:F))^2*a^3,((l:F)^2/(m:F))*a^3,
      ((l:F)^2/(m:F))*a^2,((l:F)^2/(m:F))*a,(l:F)^2/(m:F),0]
    rfl rfl (bigLevi a b l m) (by simpa [unipotentProduct] using big_conjugate_B a b l m)
  simp [unipotentProduct] at h
  rw [h]
  congr 1
  ring_nf
  simp [CharTwo.two_eq_zero]

private theorem small_conjugate_E (a : F) (l m : Fˣ) :
    smallLevi a l m * rootE 1 * (smallLevi a l m)⁻¹ =
      unipotentProduct ![((m:F)^2/(l:F))^2*a^3,
        ((m:F)^2/(l:F))*a^3,((m:F)^2/(l:F))*a^2,
        ((m:F)^2/(l:F))*a,(m:F)^2/(l:F),0] := by
  rw [smallLevi, conj_mul, torus_rootE, mul_one, rootF_conjugate_rootE_chart]

private theorem small_commutator_E (a : F) (l m : Fˣ) :
    ⁅rootE (1 : F), smallLevi a l m⁆ ^ 2 = rootA (((m:F)^2/(l:F))*a^3) := by
  have h := chart_commutator_square (![0,0,0,0,1,0] : Fin 6 → F)
    ![((m:F)^2/(l:F))^2*a^3,((m:F)^2/(l:F))*a^3,
      ((m:F)^2/(l:F))*a^2,((m:F)^2/(l:F))*a,(m:F)^2/(l:F),0]
    rfl rfl (smallLevi a l m) (by simpa [unipotentProduct] using small_conjugate_E a l m)
  simp [unipotentProduct] at h
  rw [h]
  congr 1
  ring_nf
  simp [CharTwo.two_eq_zero]

omit [CharP F 2] in
private theorem torus_conjugate_CD (l m : Fˣ) :
    torus l m * (rootC 1 * rootD 1) * (torus l m)⁻¹ =
      unipotentProduct ![0,0,(l:F),(m:F),0,0] := by
  change MulAut.conj (torus l m) (rootC 1 * rootD 1) = _
  rw [map_mul]
  simp only [MulAut.conj_apply, torus_rootC, torus_rootD, mul_one]
  simp [unipotentProduct]

omit [CharP F 2] in
private theorem torus_conjugate_BE (l m : Fˣ) :
    torus l m * (rootB 1 * rootE 1) * (torus l m)⁻¹ =
      unipotentProduct ![0,(l:F)^2/(m:F),0,0,(m:F)^2/(l:F),0] := by
  change MulAut.conj (torus l m) (rootB 1 * rootE 1) = _
  rw [map_mul]
  simp only [MulAut.conj_apply, torus_rootB, torus_rootE, mul_one]
  simp [unipotentProduct]

private theorem torus_commutator_CD (l m : Fˣ) :
    ⁅rootC (1 : F) * rootD 1, torus l m⁆ ^ 2 = rootA ((1+(l:F))*(1+(m:F))) := by
  have h := chart_commutator_square (![0,0,1,1,0,0] : Fin 6 → F)
    ![0,0,(l:F),(m:F),0,0] rfl rfl (torus l m)
    (by simpa [unipotentProduct] using torus_conjugate_CD l m)
  simpa [unipotentProduct] using h

private theorem torus_commutator_BE (l m : Fˣ) :
    ⁅rootB (1 : F) * rootE 1, torus l m⁆ ^ 2 =
      rootA ((1+(l:F)^2/(m:F))*(1+(m:F)^2/(l:F))) := by
  have h := chart_commutator_square (![0,1,0,0,1,0] : Fin 6 → F)
    ![0,(l:F)^2/(m:F),0,0,(m:F)^2/(l:F),0] rfl rfl (torus l m)
    (by simpa [unipotentProduct] using torus_conjugate_BE l m)
  simpa [unipotentProduct] using h

omit [CharP F 2] in
private theorem rootA_eq_one_iff (a : F) : rootA a = 1 ↔ a = 0 := by
  rw [← rootA_zero, rootA_injective.eq_iff]

private theorem one_add_eq_zero (a : F) : 1+a=0 → a=1 := by
  intro h
  calc
    a = -1 := eq_neg_of_add_eq_zero_right h
    _ = 1 := CharTwo.neg_eq _

private theorem torus_eq_one_of_squares (l m : Fˣ)
    (hCD : ⁅rootC (1 : F) * rootD 1, torus l m⁆ ^ 2 = 1)
    (hBE : ⁅rootB (1 : F) * rootE 1, torus l m⁆ ^ 2 = 1) : torus l m = 1 := by
  rw [torus_commutator_CD, rootA_eq_one_iff, mul_eq_zero] at hCD
  rw [torus_commutator_BE, rootA_eq_one_iff, mul_eq_zero] at hBE
  have hsq (a : F) (ha : a^2=1) : a=1 := by
    rcases sq_eq_one_iff.mp ha with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  have hlm : (l:F)=1 ∧ (m:F)=1 := by
    rcases hCD with hl | hm
    · have hl := one_add_eq_zero _ hl
      refine ⟨hl, ?_⟩
      rcases hBE with h | h
      · have h := one_add_eq_zero _ h
        simpa [hl] using ((div_eq_one_iff_eq (Units.ne_zero m)).mp h).symm
      · apply hsq
        simpa [hl] using one_add_eq_zero _ h
    · have hm := one_add_eq_zero _ hm
      refine ⟨?_, hm⟩
      rcases hBE with h | h
      · apply hsq
        simpa [hm] using one_add_eq_zero _ h
      · have h := one_add_eq_zero _ h
        simpa [hm] using ((div_eq_one_iff_eq (Units.ne_zero l)).mp h).symm
  rw [show l=1 from Units.ext hlm.1, show m=1 from Units.ext hlm.2, torus_identity]

/-- The two cells modulo the five-root radical. -/
def HasNormalForm (g : Model F) : Prop :=
  (∃ r ∈ radical₁, ∃ a : F, ∃ l m : Fˣ, g = r * smallLevi a l m) ∨
  (∃ r ∈ radical₁, ∃ a b : F, ∃ l m : Fˣ, g = r * bigLevi a b l m)

theorem mem_radical_of_normalForm {g : Model F} (hn : HasNormalForm g)
    (hB : ⁅rootB (1 : F), g⁆ ^ 2 = 1)
    (hE : ⁅rootE (1 : F), g⁆ ^ 2 = 1)
    (hCD : ⁅rootC (1 : F) * rootD 1, g⁆ ^ 2 = 1)
    (hBE : ⁅rootB (1 : F) * rootE 1, g⁆ ^ 2 = 1) : g ∈ radical₁ := by
  have hqrB : rootB (1:F) ∈ radical₁ :=
    ⟨![0,1,0,0,0,0],rfl,by simp [unipotentProduct]⟩
  have hqrE : rootE (1:F) ∈ radical₁ :=
    ⟨![0,0,0,0,1,0],rfl,by simp [unipotentProduct]⟩
  have hqrCD : rootC (1:F) * rootD 1 ∈ radical₁ :=
    ⟨![0,0,1,1,0,0],rfl,by simp [unipotentProduct]⟩
  have hqrBE : rootB (1:F) * rootE 1 ∈ radical₁ :=
    ⟨![0,1,0,0,1,0],rfl,by simp [unipotentProduct]⟩
  rcases hn with ⟨r,hr,a,l,m,rfl⟩ | ⟨r,hr,a,b,l,m,rfl⟩
  · have he := radical_perturbation hqrE hr
      (show smallLevi a l m * rootE 1 * (smallLevi a l m)⁻¹ ∈ radical₁ from
        ⟨_,rfl,(small_conjugate_E a l m).symm⟩)
    rw [he,small_commutator_E,rootA_eq_one_iff] at hE
    have ha : a=0 := by
      have := (mul_eq_zero.mp hE).resolve_left
        (div_ne_zero (pow_ne_zero _ (Units.ne_zero m)) (Units.ne_zero l))
      exact (pow_eq_zero_iff (by decide : (3:ℕ) ≠ 0)).mp this
    subst a
    simp only [smallLevi,rootF_zero,one_mul] at hCD hBE ⊢
    rw [radical_perturbation hqrCD hr ⟨_,rfl,(torus_conjugate_CD l m).symm⟩] at hCD
    rw [radical_perturbation hqrBE hr ⟨_,rfl,(torus_conjugate_BE l m).symm⟩] at hBE
    rw [torus_eq_one_of_squares l m hCD hBE,mul_one]
    exact hr
  · have hb := radical_perturbation hqrB hr
      (show bigLevi a b l m * rootB 1 * (bigLevi a b l m)⁻¹ ∈ radical₁ from
        ⟨_,rfl,(big_conjugate_B a b l m).symm⟩)
    rw [hb,big_commutator_B,rootA_eq_one_iff] at hB
    exact (div_ne_zero (pow_ne_zero _ (Units.ne_zero l)) (Units.ne_zero m) hB).elim

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.FirstActor

end

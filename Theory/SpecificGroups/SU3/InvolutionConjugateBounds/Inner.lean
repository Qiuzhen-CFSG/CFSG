module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Defs
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Inner.RootPair
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Inner.Conjugacy
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport

/-!
# The uniform five-conjugate bound for inner involutions of PSU₃(p)

The explicit sign-involution calculation generates both opposite root
groups using five inner conjugates. Arbitrary Hermitian forms are carried
to the antidiagonal form by actual matrix-group equivalences. Involution
conjugacy then carries the sign calculation to any inducing involution.
Finally, mapping the generated subgroup under `MulAut.conj` gives the
literal inner-automorphism containment required by `InnerFiveBound`.

The nontrivial inner actor makes conjugation faithful on the supplied
simple group, so its inducing element really has order two. No simplicity,
order, or automorphism-classification theorem is assumed beyond the task's
inherited simplicity hypothesis.

Source: Aschbacher–Smith K.2, printed p.453; Guralnick–Malle,
*Classification of 2F-modules I*, §2 and Proposition 4.3. The uniform
estimate is proved here by root geometry, extending the explicit count
at seven in that proposition. See `Inner.RootPair` for the five matrices.
-/

public section

open Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Inner

variable {G H : Type*} [Group G] [Group H]

private theorem inducing_involution [IsSimpleGroup G] (k : G)
    (hk : MulAut.conj k ≠ 1) (hk2 : MulAut.conj k ^ 2 = 1) : orderOf k = 2 := by
  have hi : Function.Injective (MulAut.conj : G →* MulAut G) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases (inferInstance : (MulAut.conj : G →* MulAut G).ker.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hk (show k ∈ (MulAut.conj : G →* MulAut G).ker from h ▸ mem_top k)).elim
  apply orderOf_eq_prime
  · apply hi
    simpa only [map_pow, map_one] using hk2
  · intro he
    exact hk (he ▸ map_one _)

private theorem generating_conjugates_of_isConj {t k : G} {n : ℕ}
    (h : ∃ s : Fin n → G, closure (Set.range fun i => s i * t * (s i)⁻¹) = ⊤)
    (htk : IsConj t k) :
    ∃ s : Fin n → G, closure (Set.range fun i => s i * k * (s i)⁻¹) = ⊤ := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨g, rfl⟩ := isConj_iff.mp htk
  refine ⟨fun i => s i * g⁻¹, ?_⟩
  have he : (fun i => s i * g⁻¹ * (g * t * g⁻¹) * (s i * g⁻¹)⁻¹) =
      (fun i => s i * t * (s i)⁻¹) := by funext i; group
  rwa [he]

private theorem generating_conjugates_of_equiv (e : G ≃* H) (k : G) {n : ℕ}
    (h : ∃ s : Fin n → H, closure (Set.range fun i => s i * e k * (s i)⁻¹) = ⊤) :
    ∃ s : Fin n → G, closure (Set.range fun i => s i * k * (s i)⁻¹) = ⊤ := by
  obtain ⟨s, hs⟩ := h
  refine ⟨fun i => e.symm (s i), ?_⟩
  have hm := congrArg (fun K : Subgroup H => K.map e.symm.toMonoidHom) hs
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr e.symm.surjective] at hm
  simpa only [Function.comp_def, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    map_mul, map_inv, e.symm_apply_apply] using hm

private theorem inner_cover_of_generating_conjugates (k : G) {n : ℕ}
    (h : ∃ s : Fin n → G, closure (Set.range fun i => s i * k * (s i)⁻¹) = ⊤) :
    MulAut.HasInnerConjugateCover (MulAut.conj k) n := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, ?_⟩
  have hm := congrArg (fun K : Subgroup G => K.map (MulAut.conj : G →* MulAut G)) hs
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map] at hm
  exact le_of_eq (by simpa only [Function.comp_def, map_mul, map_inv] using hm.symm)

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Inner

namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Inner
open Matrix Subgroup BenderSuzuki.External
open OddPrimeSylow.NormalizedOuter.Coverage

private theorem sign_orderOf {E : Type*} [Field E] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (h2 : (2 : E) ≠ 0) :
    orderOf (signInvolution J hJ) = 2 := by
  apply orderOf_eq_prime
  · change (hermitianTorusPSU J hJ (-1)) ^ 2 = 1
    rw [← map_pow]
    simp
  · intro he
    obtain ⟨z, hz⟩ := coord_first_surjective J h2 1
    change z.val.1 = 1 at hz
    have ha := hermitianTorusPSU_mul_unipotent J hJ (-1) z
    change signInvolution J hJ * root J hJ z =
      root J hJ (hermitianTorusAction J (-1) z) * signInvolution J hJ at ha
    rw [he, one_mul, mul_one] at ha
    have hf := congrArg (fun w : hermitianUnipotentCoord J => w.val.1)
      (root_injective J hJ ha)
    simp only [hermitianTorusAction_fst, Units.val_neg, Units.val_one,
      map_neg, map_one, inv_neg, inv_one, neg_one_sq, mul_one, mul_neg_one, hz] at hf
    apply h2
    linear_combination hf

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Inner

namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds
open Inner OddPrimeSylow.NormalizedOuter.FormTransport

universe u

/-- Every nontrivial inner involution of PSU₃(p) is covered by five of its
conjugates by actual elements of PSU₃(p), uniformly for odd primes above five. -/
theorem innerFiveBound : InnerFiveBound.{u} := by
  intro E _ _ J _ p hp _ hlarge hcard hc a ha ha2 hi
  obtain ⟨k, rfl⟩ := hi
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : E) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime E Nat.prime_two hp2
  have hfixed := J.card_fixed_of_prime_frobenius hc
  have hk : orderOf k = 2 := inducing_involution k ha ha2
  obtain ⟨e⟩ := exists_projectiveEquiv J p hcard hfixed
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) :=
    e.symm.isSimpleGroup
  apply inner_cover_of_generating_conjugates
  apply generating_conjugates_of_equiv e k
  apply generating_conjugates_of_isConj
    (sign_five_generate (standardForm J) rfl hp h2 hcard hfixed)
  exact projective_involutions_isConj (standardForm J) hp hp2 hcard hc _ _
    (sign_orderOf (standardForm J) rfl h2) ((e.orderOf_eq k).trans hk)

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds

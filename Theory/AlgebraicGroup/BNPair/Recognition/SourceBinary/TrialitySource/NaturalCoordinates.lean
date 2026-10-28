module
public import Theory.SpecificGroups.PSL2.SemilinearCoverage.RootParameters
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.FieldMarking

/-!
# Recovering the natural action's field coordinates

A homomorphism SL₂(K) → SL₂(E) that preserves the upper root line and sends
the marked Weyl matrix to the marked Weyl matrix comes from a field embedding
when K is finite of characteristic two. The root group gives additivity;
the rank-one braid fixes parameter one. The diagonal conjugation identity
then gives multiplication by squares, and every element of K is a square.
This proves the needed two-dimensional matrix assertion directly, without
assuming the representation classification cited by the source.

For the triality source's actual fixed field K inside F, the resulting
embedding lands back in that same K: its elements satisfy x^q = x. Thus
its scalar twist is an automorphism of the already marked fixed field,
including q=2 and q=4. Constructing the two-dimensional source action and
its marked axes from the earlier radical geometry remains necessary.

Source: Fong--Seitz II (9.24)--(9.27), printed pp.218--219. The elementary
matrix argument extends PSL2.SemilinearCoverage.Multiplicativity from
automorphisms to homomorphisms over two different fields. The literal
source-section consumer is TrialitySource.ScalarAlignment.
-/


public noncomputable section
open Theory.PSL2.SemilinearCoverage
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
namespace NaturalCoordinates
variable {K E : Type*} [Field K] [Finite K] [CharP K 2] [Field E] [CharP E 2]

/-- A two-dimensional action preserving the root line and swapping its two
marked axes has field coordinates. No irreducible representation classification
or preselected field embedding is assumed. -/
theorem exists_field_map (r : SL2 K →* SL2 E)
    (hU : ∀ a : K, ∃ b : E, r (uni a) = uni b) (hW : r (weyl K) = weyl E) :
    ∃ κ : K →+* E, r = Matrix.SpecialLinearGroup.map κ := by
  classical
  choose f hf using hU
  have hadd (a b : K) : f (a+b) = f a + f b := by
    apply uni_injective
    rw [← hf, ← uni_mul_uni, map_mul, hf, hf, uni_mul_uni]
  have hzero : f 0 = 0 := by
    have hh := hadd 0 0
    exact add_left_cancel (a := f 0) (by simpa only [add_zero] using hh.symm)
  have hone : f 1 = 1 := by
    have hbraid : uni (1 : K)*weyl K*uni 1 = weyl K*uni 1*weyl K := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]
    have h := congrArg r hbraid
    simp only [map_mul,hf,hW] at h
    have he := congrArg (fun g : SL2 E => g.val 1 1) h
    simpa [Matrix.mul_apply,Fin.sum_univ_two] using he
  have hsquare (a : Kˣ) (b : K) : f ((a : K)^2*b) = f ((a : K)^2)*f b := by
    have htor : tor a ∈ Borel K := by rw [mem_Borel_iff]; simp
    have hrel (c : K) : tor a*uni c*(tor a)⁻¹ = uni ((a : K)^2*c) := by
      simpa using Borel_conj_uni htor c
    have hmap (c : K) : r (tor a)*uni (f c)*(r (tor a))⁻¹ = uni (f ((a : K)^2*c)) := by
      have h := congrArg r (hrel c)
      simpa only [map_mul,map_inv,hf] using h
    have h1 := hmap 1
    rw [hone,mul_one] at h1
    have heq := (mul_inv_eq_iff_eq_mul).mp h1
    have hB : r (tor a) ∈ Borel E := by
      rw [mem_Borel_iff]
      have he := congrArg (fun g : SL2 E => g.val 1 1) heq
      simpa [Matrix.mul_apply,Fin.sum_univ_two] using he
    have hs (c : K) : f ((a : K)^2*c) = (r (tor a)).val 0 0 ^ 2 * f c :=
      uni_injective ((hmap c).symm.trans (Borel_conj_uni hB _))
    have hsq : f ((a : K)^2) = (r (tor a)).val 0 0 ^ 2 := by
      simpa only [mul_one,hone] using hs 1
    rw [hs,hsq]
  have hmul (a b : K) : f (a*b) = f a*f b := by
    obtain ⟨c,rfl⟩ := (Finite.surjective_of_injective (CharTwo.sq_injective (R := K))) a
    by_cases hc : c = 0
    · simp [hc,hzero]
    · exact hsquare (Units.mk0 c hc) b
  let κ : K →+* E :=
    { toFun := f
      map_zero' := hzero
      map_one' := hone
      map_add' := hadd
      map_mul' := hmul }
  refine ⟨κ,sl2_hom_ext_root_weyl _ _ ?_ ?_⟩
  · intro a
    rw [hf]
    ext i j
    change (uni (κ a)).val i j = κ ((uni a).val i j)
    fin_cases i <;> fin_cases j <;> simp
  · rw [hW]
    ext i j
    change (weyl E).val i j = κ ((weyl K).val i j)
    fin_cases i <;> fin_cases j <;> simp

omit [Finite K] [CharP K 2] [CharP E 2] in
/-- Relabel the entire natural actor, not just its upper root line. -/
theorem relabel_field_map (ι : K →+* E) (κ : K ≃+* K) :
    (Matrix.SpecialLinearGroup.map (ι.comp κ.toRingHom)).comp
        (Theory.PSL2.sl2FieldAut κ.symm).toMonoidHom = Matrix.SpecialLinearGroup.map ι := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  change ι (κ (κ.symm (a.val i j))) = ι (a.val i j)
  rw [κ.apply_symm_apply]

open Triality.Standard Triality.Standard.RootPresentationRecognition

/-- Any coefficient embedding of the actual fixed field in the source cubic
field lands back in that same fixed field. The marking is not chosen anew. -/
theorem exists_fixed_automorphism {F : Type*} [Field F] [Finite F] [CharP F 2]
    {σ : F ≃+* F} {n : ℕ} {hn : 0 < n}
    (e : ScalarMarking (binaryParameters n hn) σ)
    (r : SL2 (ScalarMarking.SourceFixed (σ := σ)) →* SL2 F)
    (hU : ∀ a, ∃ b : F, r (uni a) = uni b) (hW : r (weyl _) = weyl F) :
    ∃ κ : ScalarMarking.SourceFixed (σ := σ) ≃+* ScalarMarking.SourceFixed (σ := σ),
      r = Matrix.SpecialLinearGroup.map
        ((ScalarMarking.SourceFixed (σ := σ)).subtype.comp κ.toRingHom) := by
  obtain ⟨k,hk⟩ := exists_field_map r hU hW
  have hfixed (a : ScalarMarking.SourceFixed (σ := σ)) : σ (k a) = k a := by
    apply e.extension.injective
    rw [e.frobenius,fieldFrobenius_apply,← map_pow,← map_pow]
    congr 2
    let := Fintype.ofFinite (ScalarMarking.SourceFixed (σ := σ))
    have hc : Fintype.card (ScalarMarking.SourceFixed (σ := σ)) =
        (binaryParameters n hn).q := by
      rw [← Nat.card_eq_fintype_card,scalarMarking_sourceFixed_card e,binaryParameters_q]
    rw [← hc]
    exact FiniteField.pow_card a
  let k' := k.codRestrict (ScalarMarking.SourceFixed (σ := σ)) hfixed
  let κ := RingEquiv.ofBijective k' ⟨k'.injective,Finite.surjective_of_injective k'.injective⟩
  exact ⟨κ,hk⟩

end NaturalCoordinates
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource

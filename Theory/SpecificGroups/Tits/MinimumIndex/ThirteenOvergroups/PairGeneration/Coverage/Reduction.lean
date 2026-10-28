module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Coverage.Soundness

/-!
# Compression of thirteen-normalizer double-coset coverage

The first Schreier-chain cardinality identifies the full point-zero stabilizer.
A checked orbit witness first moves any element into one of 32 point fibers.
Closure checks cover each fiber by 144 right normalizer cosets, leaving just
4608 products to compare with the fixed double-coset representatives.

The three families of finite checks remain explicit premises here. They do not
follow from the untrusted witness tables, nor from the source's reported orders.
Source: the primary ATLAS point maps and the certified ambient Schreier chain.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate
open Atlas1600OrderCertificate Theory.GroupTheory

/-- The first subgroup of the checked chain is the full point-zero stabilizer. -/
public theorem fix_zero_mem_H1 (x : Atlas1600Group) (hx : x.val 0 = 0) : x.val ∈ H1 := by
  classical
  let cover : Fin 1600 × H1 → H0 := fun y =>
    ⟨L0Rep y.1 * y.2.val, H0.mul_mem (L0Rep_mem _) (H1_le y.2.property)⟩
  have hinj : Function.Injective cover := by
    rintro ⟨r, k⟩ ⟨r', k'⟩ he
    have hr : r = r' := by
      apply L0Point_injective
      have hp := congrArg (fun p : Equiv.Perm (Fin 1600) => p 0) (Subtype.ext_iff.mp he)
      simpa only [cover, Equiv.Perm.mul_apply, H1_fix, L0Rep_point] using hp
    subst r'
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact mul_left_cancel (Subtype.ext_iff.mp he)
  have hsurj : Function.Surjective cover :=
    (hinj.bijective_of_nat_card_le (by simpa using H0_card_step.le)).2
  obtain ⟨⟨r, k⟩, he⟩ := hsurj ⟨x.val, H0_eq_atlas.symm ▸ x.property⟩
  have he' : L0Rep r * k.val = x.val := Subtype.ext_iff.mp he
  have hr : r = 0 := by
    apply L0Point_injective
    rw [← L0Rep_point, ← L0Rep_point, L0Rep_base]
    have hp := congrArg (fun p : Equiv.Perm (Fin 1600) => p 0) he'
    simpa only [Equiv.Perm.mul_apply, H1_fix, hx, Equiv.Perm.one_apply] using hp
  subst r
  rw [L0Rep_base, one_mul] at he'
  exact he' ▸ k.property

public theorem stabilizer_cover_of_transitions
    (hstep : ∀ (i : Fin 6) (j : Fin 144), transitionTest i j = true)
    (x : Atlas1600Group) (hx : x.val 0 = 0) :
    ∃ (j : Fin 144) (n : thirteenNormalizer), x = stabilizerRep j * n.val := by
  have hw : ∀ w : List (Fin 6), ∃ (j : Fin 144) (n : thirteenNormalizer),
      evalWord chainGenerator w = stabilizerRep j * n.val := by
    intro w
    induction w with
    | nil =>
      refine ⟨0, 1, ?_⟩
      change (1 : Atlas1600Group) = 1 * 1
      exact (one_mul 1).symm
    | cons i w ih =>
      obtain ⟨j, n, hn⟩ := ih
      refine ⟨transitionRep i j, normalizerElement (transitionNormal i j) * n, ?_⟩
      change chainGenerator i * evalWord chainGenerator w =
        stabilizerRep (transitionRep i j) * (normalWord (transitionNormal i j) * n.val)
      rw [hn, ← mul_assoc, transitionTest_sound i j (hstep i j), mul_assoc]
  obtain ⟨w, hval⟩ := fix_zero_mem_H1 x hx
  have he : evalWord chainGenerator w = x := Subtype.ext ((chainWord_val w).trans hval)
  rw [← he]
  exact hw w

private theorem val_mul_apply (g h : Atlas1600Group) (p : Fin 1600) :
    (g * h).val p = g.val (h.val p) := rfl

private theorem inv_mul_fix (g x : Atlas1600Group) (h : g.val 0 = x.val 0) :
    (g⁻¹ * x).val 0 = 0 := by
  change g.val.symm (x.val 0) = 0
  rw [← h]
  exact g.val.symm_apply_apply 0

/-- The exact normalizer-double-coset conclusion follows from the three finite tests. -/
public theorem coverage_of_finite_checks
    (hpoint : ∀ p : Fin 1600, pointTest p = true)
    (hstep : ∀ (i : Fin 6) (j : Fin 144), transitionTest i j = true)
    (hfactor : ∀ (i : Fin 32) (j : Fin 144), factorTest i j = true)
    (x : Atlas1600Group) :
    ∃ (a b : thirteenNormalizer) (k : Fin 3010), x = a.val * representative k * b.val := by
  let i := pointOrbit (x.val 0)
  let n := normalizerElement (pointNormal (x.val 0))
  let y := (n.val * orbitRep i)⁻¹ * x
  have hx : (n.val * orbitRep i).val 0 = x.val 0 := by
    rw [val_mul_apply]
    exact pointTest_sound _ (hpoint _)
  have hy : y.val 0 = 0 := inv_mul_fix _ _ hx
  obtain ⟨j, b, hb⟩ := stabilizer_cover_of_transitions hstep y hy
  have he : x = n.val * (orbitRep i * stabilizerRep j) * b.val := by
    calc
      x = (n.val * orbitRep i) * y := by dsimp [y]; simp only [mul_inv_cancel_left]
      _ = n.val * (orbitRep i * stabilizerRep j) * b.val := by rw [hb]; simp only [mul_assoc]
  refine ⟨n * normalizerElement (factorLeft i j), normalizerElement (factorRight i j) * b,
    factorRep i j, ?_⟩
  change x = (n.val * normalWord (factorLeft i j)) * representative (factorRep i j) *
    (normalWord (factorRight i j) * b.val)
  rw [he, factorTest_sound i j (hfactor i j)]
  simp only [mul_assoc]

end Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate

module
public import ABG.ChapterII.Section2.UnitarySemilinear
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.FieldTheory.OddFixedQuadraticEmbedding
public import ABG.ChapterII.Section2.UnitaryOddExtensionEmbedding
public import ABG.ChapterII.Section2.UnitaryOddExtensionIndex

/-!
# Unitary Sylow subgroups fixed by odd coefficient automorphisms

For odd prime p and nonzero n, every odd-order subgroup A of the full
coefficient automorphism group of GF(p^(2n)) fixes some Sylow two subgroup
of each valid actual SU₂ determinant level pointwise. The action is the
original GU2CoefficientEquiv on the identity-Gram Hermitian group. This is
the unitary-model fixed-Sylow step in ABG II.3, Proposition 3(iv), article
pp. 27–28; no small field or determinant level is excluded.

The actual fixed field has order p^(2k), where n=k|A|. Its coefficient
embedding into the original quadratic field commutes with the stored
unitary involutions because |A| is odd. This gives an injective map of
actual unitary groups with pointwise A-fixed image. The unitary order
formula makes that image's index odd. A Sylow of the image therefore
maps to a Sylow of GU₂; intersecting with the normal SU2Level gives the
required Sylow. The argument works at every level; the public endpoint
retains the source's valid-level divisibility hypothesis.
-/

namespace ABG

private theorem fixed_unitary_sylow_aux
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (A : Subgroup (GaloisField p (2 * n) ≃+* GaloisField p (2 * n)))
    (m : ℕ)
    (k : ℕ) (hk : k ≠ 0)
    (f : GU2 p k hk →* GU2 p n hn)
    (hindex : Odd f.range.index)
    (hfixed : ∀ (σ : A) (x : GU2 p k hk), GU2CoefficientEquiv p n hn σ.val (f x) = f x) :
    ∃ S : Sylow 2 (SU2Level p n hn m),
      ∀ (σ : A) (x : S), GU2CoefficientEquiv p n hn σ.val x.val.val = x.val.val := by
  classical
  let C := f.range
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := C)
  let Q : Sylow 2 (GU2 p n hn) :=
    (P.isPGroup'.map C.subtype).toSylow (by
      rw [Subgroup.index_map_subtype]
      exact Nat.Prime.not_dvd_mul Nat.prime_two P.not_dvd_index hindex.not_two_dvd_nat)
  obtain ⟨S, hS⟩ := Q.exists_subgroupOf_eq_of_normal (SU2Level p n hn m)
  refine ⟨S, ?_⟩
  intro σ x
  have hx : x.val.val ∈ C := by
    have hxQ : x.val.val ∈ Q := by
      have hxS : x.val ∈ (S : Subgroup (SU2Level p n hn m)) := x.property
      rw [hS] at hxS
      exact hxS
    obtain ⟨y, _, hy⟩ := hxQ
    exact hy ▸ y.property
  obtain ⟨y, hy⟩ := hx
  rw [← hy]
  exact hfixed σ y

/-- An odd subgroup of the full quadratic-field coefficient automorphism group
fixes an actual Sylow two subgroup of the unitary determinant level pointwise. -/
public theorem exists_unitary_sylow_fixed_by_odd_coefficient_subgroup
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0)
    (A : Subgroup (GaloisField p (2 * n) ≃+* GaloisField p (2 * n)))
    (hA : Odd (Nat.card A)) (m : ℕ) (_hm : 2 ^ m ∣ p ^ n + 1) :
    ∃ S : Sylow 2 (SU2Level p n hn m),
      ∀ (σ : A) (x : S), GU2CoefficientEquiv p n hn σ.val x.val.val = x.val.val := by
  obtain ⟨k, hk, hnk, e, he⟩ :=
    GaloisField.exists_fixed_quadratic_embedding_of_odd p n hn A hA
  let f := GU2OddExtensionHom p k n hk hn (Nat.card A) hA hnk e
  have hf := GU2OddExtensionHom_injective p k n hk hn (Nat.card A) hA hnk e
  apply fixed_unitary_sylow_aux p n hn A m k hk f
    (GU2_odd_index_of_injective p k n hp hk hn (Nat.card A) hA hnk f hf)
  intro σ x
  apply Subtype.ext
  ext i j
  exact he σ (x.val i j)

end ABG


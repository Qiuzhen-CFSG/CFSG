module

public import Theory.SpecificGroups.Classical.LinearFundamental

/-!
# Classical fundamental subgroups for A.2.17

This module supplies the split linear branch of the structural argument in
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), Lemma A.2.17, printed pp.38–39.

In degree `3 + d`, use the decomposition `2 + (1 + d)`. The two actual
special-linear block groups embed in the central quotient and commute. The
fundamental SL₂ is proper, and in odd characteristic its scalar minus one is
a nonidentity involution. Row transvections of the complementary block lie in
the literal prime-to-r residual of the fundamental subgroup's centralizer.
Their rank `e*d` proves that residual rank at most one forces degree three,
or degree four with `e = 1`. No identification of that residual is assumed.

The lower module also calculates the centralizer in the covering SL group
and the scalar kernel of the joint block map. Identifying the full projective
centralizer residual, and the unitary, symplectic, and orthogonal structural
branches, remain separate obligations for the complete A.2.17 argument.
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure
open Matrix Matrix.SpecialLinearGroup
open Matrix.SpecialLinearGroup.LinearFundamental

variable (F : Type*) [Field F] (d : ℕ)

/-- The projective matrix group with its marked fundamental two-space. -/
abbrev LinearAmbient := ProjectiveSpecialLinearGroup (Fin 2 ⊕ Fin (1 + d)) F

/-- The genuine fundamental SL₂, acting on the first two coordinates. -/
@[expose] def linearFundamental : SpecialLinearGroup (Fin 2) F →* LinearAmbient F d :=
  projectLeft

/-- The special-linear group of the complementary space, inside the same quotient. -/
@[expose] def linearComplement : SpecialLinearGroup (Fin (1 + d)) F →* LinearAmbient F d :=
  projectRight

/-- The literal subgroup denoted J* in the split linear source argument. -/
@[expose] def linearResidual (r : ℕ) :=
  Subgroup.primeToResidual r
    (Subgroup.centralizer (linearFundamental F d).range.carrier)

/-- The sum-index model is the usual projective matrix group in degree `3 + d`. -/
def linearModelEquiv : LinearAmbient F d ≃* ProjectiveSpecialLinearGroup (Fin (3 + d)) F :=
  projectiveReindex (finSumFinEquiv.trans (finCongr (by omega)))

/-- The fundamental map is injective even after the ambient central quotient. -/
theorem linearFundamental_injective : Function.Injective (linearFundamental F d) :=
  projectLeft_injective

/-- An off-block transvection proves that this fundamental subgroup is proper. -/
theorem linearFundamental_proper : (linearFundamental F d).range ≠ ⊤ :=
  projectLeft_range_ne_top

/-- The complementary subgroup is SL of the complementary dimension, without
a further central quotient on that factor. -/
def linearComplementEquiv : SpecialLinearGroup (Fin (1 + d)) F ≃*
    (linearComplement F d).range :=
  MonoidHom.ofInjective (projectRight_injective (m := Fin 2))

/-- Both marked factors commute in the literal ambient quotient. -/
theorem linear_factors_commute (a : SpecialLinearGroup (Fin 2) F)
    (b : SpecialLinearGroup (Fin (1 + d)) F) :
    Commute (linearFundamental F d a) (linearComplement F d b) :=
  projectLeft_projectRight_commute a b

/-- The fundamental central involution survives the quotient in odd characteristic. -/
theorem linearFundamental_involution {r : ℕ} [Fact r.Prime] [CharP F r] (hr : r ≠ 2) :
    let : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
    linearFundamental F d (-1) ≠ 1 ∧ linearFundamental F d (-1) ^ 2 = 1 := by
  let : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
  exact map_neg_one_isInvolution hr (linearFundamental F d) (linearFundamental_injective F d)

/-- The split-linear dimension restriction in A.2.17 follows from the rank of
the actual residual, with the defining field and its exponent unchanged. -/
theorem linear_dimension_of_residual_rank [Finite F] {r e : ℕ}
    [Fact r.Prime] [CharP F r] (hcard : Nat.card F = r ^ e) (he : 0 < e)
    (hJ : primeRank r (linearResidual F d r) ≤ 1) :
    3 + d = 3 ∨ 3 + d = 4 ∧ e = 1 := by
  have h := linear_dimension_restriction hcard he hJ
  rcases h with h | ⟨h, he⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, he⟩


/-- On the covering group the fundamental centralizer has exactly the
scalar/complementary block form, with the required determinant relation. -/
theorem linear_coverCentralizer (hF : (2 : F) ≠ 0)
    (g : SpecialLinearGroup (Fin 2 ⊕ Fin (1 + d)) F)
    (hg : g ∈ Subgroup.centralizer
      (left (m := Fin 2) (n := Fin (1 + d)) (F := F)).range.carrier) :
    ∃ (c : F) (D : Matrix (Fin (1 + d)) (Fin (1 + d)) F),
      c ^ 2 * D.det = 1 ∧ g.val = fromBlocks (scalar (Fin 2) c) 0 0 D := by
  obtain ⟨c, D, h⟩ := (mem_coverCentralizer_iff hF g).mp hg
  refine ⟨c, D, ?_, h⟩
  have hd := g.property
  rw [h, det_fromBlocks_zero₂₁] at hd
  simpa using hd

/-- The joint fundamental/complementary map has only its common scalar kernel;
the scalar has square one and also satisfies the complementary determinant. -/
theorem linear_jointKernel (a : SpecialLinearGroup (Fin 2) F)
    (b : SpecialLinearGroup (Fin (1 + d)) F) :
    linearFundamental F d a * linearComplement F d b = 1 ↔
      ∃ c : F, c ^ 2 = 1 ∧ c ^ (1 + d) = 1 ∧
        a.val = scalar (Fin 2) c ∧ b.val = scalar (Fin (1 + d)) c := by
  have hm : linearFundamental F d a * linearComplement F d b =
      QuotientGroup.mk' (Subgroup.center _) (block (a, b)) := by
    change QuotientGroup.mk' _ (block (a, 1)) * QuotientGroup.mk' _ (block (1, b)) = _
    rw [← map_mul, ← map_mul]
    simp
  rw [hm, projectBlock_eq_one_iff]
  constructor
  · rintro ⟨c, ha, hb⟩
    refine ⟨c, ?_, ?_, ha, hb⟩
    · have h := a.property
      rw [ha] at h
      simpa using h
    · have h := b.property
      rw [hb] at h
      simpa using h
  · rintro ⟨c, _, _, ha, hb⟩
    exact ⟨c, ha, hb⟩

end CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure

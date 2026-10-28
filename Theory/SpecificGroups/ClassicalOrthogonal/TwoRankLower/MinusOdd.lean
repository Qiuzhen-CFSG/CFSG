module
public import Theory.SpecificGroups.ClassicalOrthogonal.TwoRankLower.Odd
public import Theory.SpecificGroups.ClassicalOrthogonal.A02ParabolicSections.SourceGeometry.Minus
public import Mathlib.Tactic.FieldSimp

/-!
# Faithful five-spaces in minus orthogonal commutator groups

Completing the square in the chosen anisotropic plane embeds the actual
centerless PSp₄ five-space. Its perfectness puts the image in the full
orthogonal commutator; hyperbolic tail maps preserve injectivity. Central
scalar kernels cannot collapse any nontrivial element of this subgroup.
Thus every odd-characteristic minus carrier of rank at least three contains
an elementary eight. Source: GLS3 §2.7; Aschbacher–Smith A.2.12, printed p.36.
-/
@[expose] public noncomputable section
namespace ClassicalOrthogonal.TwoRank
open Theory.AlgebraicGroup Fundamental.SplitOddBlocks Theory.GroupTheory
variable {F : Type} [Field F]

abbrev anisotropicLine (a : F) : QuadraticForm F F :=
  (-(a+(1/4:F))) • QuadraticMap.sq

def fiveMinusLineLinear (_h2 : (2:F) ≠ 0) :
    (VectorB 2 F × F) ≃ₗ[F] Minus.Space F 2 where
  toFun v := ((fun i => (v.1.1 (.inl i),v.1.1 (.inr i))), (v.1.2-v.2/2,v.2))
  invFun x := ((Sum.elim (fun i => (x.1 i).1) (fun i => (x.1 i).2),x.2.1+x.2.2/2),x.2.2)
  left_inv v := by
    apply Prod.ext
    · apply Prod.ext
      · funext i; cases i <;> rfl
      · simp
    · rfl
  right_inv x := by
    apply Prod.ext
    · funext i; rfl
    · apply Prod.ext
      · simp
      · rfl
  map_add' v w := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · dsimp; ring
      · rfl
  map_smul' c v := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · dsimp; ring
      · rfl

def fiveMinusLine (h2 : (2:F) ≠ 0) (a : F) :
    ((formB 2 F).prod (anisotropicLine a)).IsometryEquiv (Minus.form F 2 a) where
  __ := fiveMinusLineLinear h2
  map_app' v := by
    simp only [Minus.form_apply,Minus.plane_apply,QuadraticMap.prod_apply,formB_apply,
      formD_apply]
    change (∑ i, v.1.1 (.inl i)*v.1.1 (.inr i)) +
      ((v.1.2-v.2/2)^2+(v.1.2-v.2/2)*v.2-a*v.2^2) =
      ((∑ i, v.1.1 (.inl i)*v.1.1 (.inr i))+v.1.2^2) + (-(a+1/4))*(v.2*v.2)
    have h4 : (4:F) ≠ 0 := by convert mul_ne_zero h2 h2 using 1; norm_num
    field_simp [h2,h4]
    ring

def fiveInMinusFull (h2 : (2:F) ≠ 0) (a : F) :
    OmegaOdd 2 F →* Minus.Orthogonal F (Minus.Space F 2) (Minus.form F 2 a) :=
  (elementarySubgroup _).subtype.comp
    ((blockMap _ _ _ (fiveMinusLine h2 a)).comp (MonoidHom.inl _ _))

theorem fiveInMinusFull_injective (h2 : (2:F) ≠ 0) (a : F) :
    Function.Injective (fiveInMinusFull h2 a) :=
  Subtype.val_injective.comp ((blockMap_injective _ _ _ _).comp (fun _ _ h => congrArg Prod.fst h))

variable [Finite F]

theorem odd_five_perfect (h2 : (2:F) ≠ 0) : Group.IsPerfect (OmegaOdd 2 F) := by
  have hcard : 2 < Nat.card F := by
    let := Fintype.ofFinite F
    have hc : 1 < Nat.card F := by
      simpa only [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α:=F)
    have hn : Nat.card F ≠ 2 := by
      intro hc
      let : CharP F 2 := charP_of_card_eq_prime (show Fintype.card F=2 by simpa using hc)
      exact h2 CharTwo.two_eq_zero
    omega
  let := Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.perfect hcard
  exact Group.IsPerfect.ofSurjective (f := (OddFiveComparison.pspEquivElementary h2).toMonoidHom)
    (OddFiveComparison.pspEquivElementary h2).surjective

def fiveInMinus (h2 : (2:F) ≠ 0) (a : F) :
    OmegaOdd 2 F →* Minus.Omega F (Minus.Space F 2) (Minus.form F 2 a) :=
  (fiveInMinusFull h2 a).codRestrict _ (by
    intro g
    let := odd_five_perfect h2
    have h := map_derivedSeries_le_derivedSeries (fiveInMinusFull h2 a) 1
    rw [derivedSeries_one,derivedSeries_one,Group.IsPerfect.commutator_eq_top,
      ← MonoidHom.range_eq_map] at h
    exact h ⟨g,rfl⟩)

theorem fiveInMinus_injective (h2 : (2:F) ≠ 0) (a : F) :
    Function.Injective (fiveInMinus h2 a) := by
  intro x y h
  exact fiveInMinusFull_injective h2 a (congrArg
    (fun z : Minus.Omega F (Minus.Space F 2) (Minus.form F 2 a) => z.val) h)

omit [Finite F] in
theorem minus_projective_injective_of_centerless {V H : Type} [AddCommGroup V]
    [Module F V] [Group H] (Q : QuadraticForm F V)
    (f : H →* Minus.Omega F V Q) (hf : Function.Injective f)
    (hc : Subgroup.center H = ⊥) :
    Function.Injective ((QuotientGroup.mk' (Minus.scalarSubgroup F V Q)).comp f) := by
  apply (injective_iff_map_eq_one _).mpr
  intro h hh
  have hs : f h ∈ Minus.scalarSubgroup F V Q := (QuotientGroup.eq_one_iff _).mp hh
  have hz := Minus.scalarSubgroup_le_center F V Q hs
  have hh : h ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply hf
    simpa only [map_mul] using (Subgroup.mem_center_iff.mp hz) (f g)
  simpa only [hc,Subgroup.mem_bot] using hh

omit [Finite F] in
def minusFiveTail (a : F) : (n : ℕ) → Minus.Omega F (Minus.Space F 2) (Minus.form F 2 a) →*
    Minus.Omega F (Minus.Space F (2+n)) (Minus.form F (2+n) a)
  | 0 => MonoidHom.id _
  | n+1 => (A02ParabolicSections.MinusTail.tailHom (2+n) a).comp (minusFiveTail a n)

omit [Finite F] in
theorem minusFiveTail_injective (a : F) (n : ℕ) : Function.Injective (minusFiveTail a n) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih => exact (A02ParabolicSections.MinusTail.tailHom_injective _ a).comp ih

theorem minus_odd_three_le (h2 : (2:F) ≠ 0) {r : ℕ} (hr : 3 ≤ r) :
    3 ≤ primeRank 2 (ClassicalGroup.POmegaMinus r F) := by
  obtain ⟨n,rfl⟩ : ∃ n, r=2+n+1 := ⟨r-3,by omega⟩
  let f := (minusFiveTail (Minus.parameter F) n).comp (fiveInMinus h2 (Minus.parameter F))
  have hf : Function.Injective f :=
    (minusFiveTail_injective _ _).comp (fiveInMinus_injective h2 _)
  have hp := minus_projective_injective_of_centerless _ f hf (odd_five_center F h2)
  have hB : 3 ≤ primeRank 2 (OmegaOdd 2 F) := by
    rw [← primeRank_equiv 2 (OddFiveComparison.pspEquivElementary h2)]
    exact Theory.SpecificGroups.Symplectic.TwoRank.three_le F (by decide)
  have hb := hB.trans (primeRank_le_of_injective 2 _ hp)
  change 3 ≤ primeRank 2 (Minus.ProjectiveOmega F (Minus.Space F (2+n+1-1))
    (Minus.form F (2+n+1-1) (Minus.parameter F)))
  rw [show 2+n+1-1=2+n by omega]
  exact hb
end ClassicalOrthogonal.TwoRank

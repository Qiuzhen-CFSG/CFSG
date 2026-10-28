module

public import Theory.SpecificGroups.Triality.LeviTwistedDescent
public import Theory.SpecificGroups.SL2.PrimeToResidual
public import Theory.SpecificGroups.SL2.DefiningRank

/-!
# Elementary descent and residual rank for the odd triality centralizer

The marked fundamental subgroup is the descent of the central simple-root
subsystem. Its complementary subgroup is obtained from the three arms by
the Weyl word carrying the central root to the highest root. The definitions
retain the graph-field fixed points, the elementary group, and its central
quotient as distinct groups.

Transvection induction lifts both fixed SL₂ maps to the elementary group in
every characteristic. Quotient kernels are recorded as exact inverse images
of its center; odd-characteristic injectivity is not inferred from the
characteristic-two result. A commuting cubic-field SL₂ map lands in the
literal prime-to-p residual of the fundamental centralizer, and a faithful
such map gives defining-characteristic rank at least three times the exponent.

The pinned maps, odd quotient-kernel calculation, commutation, and full
centralizer identification are still explicit inputs. This module does not
assert the existence of those inputs or the complete source theorem.

Sources: GLS3 §§2.4 and 2.6, especially Proposition 2.6.2
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith, Lemma A.2.17,
printed p.39 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups

namespace Triality.Standard.OddFundamentalCentralizer
open Parabolics

/-- The marked fundamental subgroup, defined directly by the central root. -/
def fundamental (P : Parameters) : Subgroup (Carrier P) := levi P .central

/-- The literal O^{p′}(C(K)) in the source, with both subgroup inclusions retained. -/
def residual (P : Parameters) :=
  Subgroup.primeToResidual P.prime (Subgroup.centralizer (fundamental P : Set (Carrier P)))

/-- SL₂ maps into the elementary fixed group in the actual characteristic,
including characteristic three, where perfectness cannot be used. -/
theorem map_mem_elementary {F : Type*} [Field F] (P : Parameters) [CharP F P.prime]
    (f : SL(2, F) →* fixedSubgroup P) (g : SL(2, F)) :
    f g ∈ elementarySubgroup P := by
  apply Matrix.SL2.transvection_induction (fun g => f g ∈ elementarySubgroup P) ?_ ?_ g
  · intro i j hij t
    have hpow (n : ℕ) : SpecialLinearGroup.transvection hij t ^ n =
        SpecialLinearGroup.transvection hij (n • t) := by
      induction n with
      | zero => simp [SpecialLinearGroup.transvection_coeff_zero]
      | succ n ih =>
        rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add, succ_nsmul]
    apply mem_elementarySubgroup_of_pow P _ 1
    simpa [nsmul_eq_mul, CharP.cast_eq_zero F P.prime,
      SpecialLinearGroup.transvection_coeff_zero] using congrArg f (hpow P.prime)
  · intro a b ha hb
    simpa only [map_mul] using (elementarySubgroup P).mul_mem ha hb

/-- A fixed split-matrix SL₂ map, with its codomain restricted to elementary fixed points. -/
def elementaryLift {F : Type*} [Field F] (P : Parameters) [CharP F P.prime]
    (f : SL(2, F) →* SplitGroup P) (hfixed : ∀ a, f a ∈ fixedSubgroup P) :
    SL(2, F) →* ElementaryGroup P :=
  let f₀ := f.codRestrict (fixedSubgroup P) hfixed
  f₀.codRestrict (elementarySubgroup P) (map_mem_elementary P f₀)

@[simp] theorem elementaryInclusion_lift {F : Type*} [Field F]
    (P : Parameters) [CharP F P.prime] (f : SL(2, F) →* SplitGroup P)
    (hfixed : ∀ a, f a ∈ fixedSubgroup P) (a : SL(2, F)) :
    elementaryInclusion P (elementaryLift P f hfixed a) = f a := rfl

/-- The actual central quotient map on a specified elementary lift. -/
def descendedHom {F : Type*} [Field F] (P : Parameters) [CharP F P.prime]
    (f : SL(2, F) →* SplitGroup P) (hfixed : ∀ a, f a ∈ fixedSubgroup P) :
    SL(2, F) →* Carrier P := (toCarrier P).comp (elementaryLift P f hfixed)

/-- No center intersection is discarded during descent. -/
theorem descendedHom_ker {F : Type*} [Field F] (P : Parameters) [CharP F P.prime]
    (f : SL(2, F) →* SplitGroup P) (hfixed : ∀ a, f a ∈ fixedSubgroup P) :
    (descendedHom P f hfixed).ker =
      (Subgroup.center (ElementaryGroup P)).comap (elementaryLift P f hfixed) := by
  ext a
  exact toCarrier_eq_one P _

/-- Exact range after elementary restriction and central quotient, without any
assumption that the quotient is injective. -/
theorem range_descendedHom {F : Type*} [Field F] (P : Parameters) [CharP F P.prime]
    (f : SL(2, F) →* SplitGroup P) (hfixed : ∀ a, f a ∈ fixedSubgroup P)
    (H : Subgroup (SplitGroup P)) (hrange : f.range = H ⊓ fixedSubgroup P) :
    (descendedHom P f hfixed).range = descendSubgroup P H := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact ⟨elementaryLift P f hfixed a, (hrange.le ⟨a, rfl⟩).1, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    have hmem : elementaryInclusion P a ∈ f.range :=
      hrange.ge ⟨ha, (a : fixedSubgroup P).property⟩
    obtain ⟨b, hb⟩ := hmem
    refine ⟨b, ?_⟩
    exact congrArg (toCarrier P) (Subtype.ext (Subtype.ext hb))

variable {P : Parameters} (D : PinnedRankOneMaps P)

theorem centralFixed_mem (a : SL(2, GaloisField P.prime P.exponent)) :
    D.centralFixedEmbedding a ∈ fixedSubgroup P :=
  (D.range_centralFixedEmbedding.le ⟨a, rfl⟩).2

/-- The pinned central-root map into the literal adjoint carrier. -/
def fundamentalHom : SL(2, GaloisField P.prime P.exponent) →* Carrier P :=
  descendedHom P D.centralFixedEmbedding (centralFixed_mem D)

theorem range_fundamentalHom : (fundamentalHom D).range = fundamental P :=
  range_descendedHom P D.centralFixedEmbedding (centralFixed_mem D)
    (splitLevi P .central) D.range_centralFixedEmbedding

theorem fundamentalHom_ker : (fundamentalHom D).ker =
    (Subgroup.center (ElementaryGroup P)).comap
      (elementaryLift P D.centralFixedEmbedding (centralFixed_mem D)) :=
  descendedHom_ker P D.centralFixedEmbedding (centralFixed_mem D)

/-- Faithfulness identifies the root-defined subgroup itself, without changing
the ambient quotient or adding a quotient to the SL₂ factor. -/
def fundamentalEquiv (hf : Function.Injective (fundamentalHom D)) :
    SL(2, GaloisField P.prime P.exponent) ≃* fundamental P :=
  (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr (range_fundamentalHom D))

variable (C : ArmRootCommutation P)

/-- The Frobenius diagonal is fixed in every characteristic. Its injectivity
requires a separate center calculation in odd characteristic. -/
theorem armsFixed_mem (a : SL(2, ExtensionField P)) :
    D.armsFixedEmbedding C a ∈ fixedSubgroup P := by
  change graphFieldAutomorphism P (D.armsProduct C (PinnedRankOneMaps.armsDiagonal P a)) = _
  exact (D.graphField_armsProduct C (PinnedRankOneMaps.armsDiagonal P a)).trans
    (congrArg (D.armsProduct C)
      (Prod.ext (Prod.ext (sl2Frobenius_three P a) rfl) rfl))

/-- The three-arm Frobenius diagonal after the actual central quotient. -/
def armsHom : SL(2, ExtensionField P) →* Carrier P :=
  descendedHom P (D.armsFixedEmbedding C) (armsFixed_mem D C)

/-- The usual SL₂ Weyl matrix, expressed in the pinned transvections. -/
def weylMatrix (F : Type*) [Field F] : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) 1 *
    SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) (-1) *
    SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) 1

/-- The Weyl word s₁(s₀s₂s₃) carrying the central root to the highest root. -/
def highestWeyl : Carrier P :=
  fundamentalHom D (weylMatrix _) * armsHom D C (weylMatrix _)

/-- Conjugating the arm subsystem back gives the complementary map for the
central simple root. Commutation is a remaining root-matrix calculation. -/
def complementHom : SL(2, ExtensionField P) →* Carrier P :=
  (MulAut.conj (highestWeyl D C)⁻¹).toMonoidHom.comp (armsHom D C)

/-- Conjugation changes no quotient kernel. The odd scalar calculation must
prove that this precise inverse image of the ambient center is trivial. -/
theorem complementHom_ker : (complementHom D C).ker =
    (Subgroup.center (ElementaryGroup P)).comap
      (elementaryLift P (D.armsFixedEmbedding C) (armsFixed_mem D C)) := by
  rw [← descendedHom_ker P (D.armsFixedEmbedding C) (armsFixed_mem D C)]
  ext a
  change (MulAut.conj (highestWeyl D C)⁻¹) (armsHom D C a) = 1 ↔ armsHom D C a = 1
  constructor
  · intro h
    apply (MulAut.conj (highestWeyl D C)⁻¹).injective
    exact h.trans (map_one _).symm
  · intro h
    rw [h, map_one]

/-- The cubic-field map restricted to the literal fundamental centralizer. -/
def centralizerHom (j : SL(2, ExtensionField P) →* Carrier P)
    (hcomm : ∀ a b, Commute (fundamentalHom D a) (j b)) :
    SL(2, ExtensionField P) →* Subgroup.centralizer (fundamental P : Set (Carrier P)) :=
  j.codRestrict _ fun b => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := (range_fundamentalHom D).ge hx
    exact (hcomm a b).eq

/-- Transvections put the entire cubic-field SL₂ into O^{p′}(C(K)). -/
def residualHom (j : SL(2, ExtensionField P) →* Carrier P)
    (hcomm : ∀ a b, Commute (fundamentalHom D a) (j b)) :
    SL(2, ExtensionField P) →* residual P :=
  (centralizerHom D j hcomm).codRestrict _
    (Matrix.SL2.map_mem_primeToResidual P.prime (centralizerHom D j hcomm))

theorem residualHom_injective (j : SL(2, ExtensionField P) →* Carrier P)
    (hcomm : ∀ a b, Commute (fundamentalHom D a) (j b))
    (hj : Function.Injective j) : Function.Injective (residualHom D j hcomm) := by
  intro a b hab
  exact hj (congrArg (fun x : residual P => x.val.val) hab)

/-- A faithful noncommutative complementary factor proves properness of the
fundamental subgroup, without an ambient order formula. -/
theorem fundamental_ne_top (j : SL(2, ExtensionField P) →* Carrier P)
    (hcomm : ∀ a b, Commute (fundamentalHom D a) (j b))
    (hj : Function.Injective j) : fundamental P ≠ ⊤ := by
  intro htop
  let u : SL(2, ExtensionField P) := SpecialLinearGroup.transvection
    (i := (0 : Fin 2)) (j := 1) (by decide) 1
  have hu : u ∈ Subgroup.center SL(2, ExtensionField P) := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply hj
    simp only [map_mul]
    have hb : j b ∈ (fundamentalHom D).range := by
      rw [range_fundamentalHom, htop]
      trivial
    obtain ⟨a, ha⟩ := hb
    rw [← ha]
    exact (hcomm a u).eq
  exact one_ne_zero ((SpecialLinearGroup.transvection_mem_center_iff
    (by decide : (0 : Fin 2) ≠ 1) (1 : ExtensionField P)).mp hu)

private theorem sl2_center_cases {F : Type*} [Field F] (a : SL(2, F))
    (ha : a ∈ Subgroup.center SL(2, F)) : a = 1 ∨ a = -1 := by
  obtain ⟨r, hr, hra⟩ := SpecialLinearGroup.mem_center_iff.mp ha
  simp only [Fintype.card_fin] at hr
  rcases sq_eq_one_iff.mp hr with rfl | rfl
  · left
    apply Subtype.ext
    simpa using hra.symm
  · right
    apply Subtype.ext
    simpa [← Matrix.diagonal_neg] using hra.symm

/-- The exact intersection of the two factors is their common scalar center.
The equality of the marked scalar images remains a root-matrix input. -/
theorem mem_fundamental_inf_range_iff
    (j : SL(2, ExtensionField P) →* Carrier P)
    (hcomm : ∀ a b, Commute (fundamentalHom D a) (j b))
    (hk : Function.Injective (fundamentalHom D))
    (hneg : fundamentalHom D (-1) = j (-1)) (x : Carrier P) :
    x ∈ fundamental P ⊓ j.range ↔ x = 1 ∨ x = fundamentalHom D (-1) := by
  constructor
  · rintro ⟨hx, hjx⟩
    obtain ⟨a, rfl⟩ := (range_fundamentalHom D).ge hx
    obtain ⟨b, hb⟩ := hjx
    have ha : a ∈ Subgroup.center SL(2, GaloisField P.prime P.exponent) := by
      rw [Subgroup.mem_center_iff]
      intro t
      apply hk
      simpa only [map_mul, hb] using (hcomm t b).eq
    rcases sl2_center_cases a ha with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨(fundamental P).one_mem, j.range.one_mem⟩
    · exact ⟨(range_fundamentalHom D).le ⟨-1, rfl⟩, ⟨-1, hneg.symm⟩⟩

/-- A centralizer exhaustion calculation supplies only the reverse inclusion;
the p-element argument above supplies the entire forward inclusion. This
equivalence retains the literal residual inclusion as its underlying map. -/
def residualEquiv (j : SL(2, ExtensionField P) →* Carrier P)
    (hcomm : ∀ a b, Commute (fundamentalHom D a) (j b))
    (hj : Function.Injective j)
    (hcover : ∀ x : residual P, x.val.val ∈ j.range) :
    SL(2, ExtensionField P) ≃* residual P :=
  MulEquiv.ofBijective (residualHom D j hcomm) ⟨residualHom_injective D j hcomm hj, by
    intro x
    obtain ⟨a, ha⟩ := hcover x
    exact ⟨a, Subtype.ext (Subtype.ext ha)⟩⟩

@[simp] theorem residualEquiv_apply_val
    (j : SL(2, ExtensionField P) →* Carrier P)
    (hcomm : ∀ a b, Commute (fundamentalHom D a) (j b))
    (hj : Function.Injective j) (hcover : ∀ x : residual P, x.val.val ∈ j.range)
    (a : SL(2, ExtensionField P)) :
    (residualEquiv D j hcomm hj hcover a).val.val = j a := rfl

/-- The actual residual has rank at least 3e once the commuting cubic map is
proved faithful. No centralizer isomorphism is needed for this lower bound. -/
theorem three_mul_exponent_le_residual_rank
    (j : SL(2, ExtensionField P) →* Carrier P)
    (hcomm : ∀ a b, Commute (fundamentalHom D a) (j b))
    (hj : Function.Injective j) : 3 * P.exponent ≤ primeRank P.prime (residual P) := by
  apply SpecialLinearGroup.fieldExponent_le_primeRank_of_injective
    (K := ExtensionField P) ?_ (residualHom D j hcomm) (residualHom_injective D j hcomm hj)
  rw [card_extensionField, Parameters.q, ← pow_mul, Nat.mul_comm P.exponent 3]

end Triality.Standard.OddFundamentalCentralizer

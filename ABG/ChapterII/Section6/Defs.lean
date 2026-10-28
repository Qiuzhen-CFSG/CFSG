module

public import FeitThompson.Gorenstein.Chapter8_2

/-!
# ABG relative constraint and stability

These are the finite-group interfaces of Alperin--Brauer--Gorenstein,
Chapter II, Section 6, Definitions 1--2 (article pp. 51, 54--55;
`refs/latex/alperin-brauer-gorenstein-pages/page-052.tex`, `page-055.tex`,
and `page-056.tex`). Constraint reuses `PConstrainedGroup` and adds containment
of the p-prime core in either the odd core or the actual solvable radical,
defined as the join of the normal solvable subgroups.

Both ordinary and relative stability retain the source's odd-prime and
nontrivial p-core domain. Relative eligibility retains the Sylow intersection
condition and the disjunction between normality in a Sylow subgroup and
containment of every quotient's p-core in the quotient image of R.

The key well-definedness argument needs only that R is a p-subgroup:
coprime orders give `R ∩ O_{p'}(H) = 1`, hence
`R ∩ (O_{p'}(H)P) = P` whenever P lies in R. Normality of the product then
forces R to normalize P. Thus the quotient image uses the entire actor,
not an unproved normalizer-containment hypothesis or a truncated actor.
Mathlib identifies the kernel of normalizer conjugation with the centralizer;
the first isomorphism theorem identifies our quotient with its automorphism
image. The trivial-P clause has trivial quotient image, proving the bridge
to the library's broader `PStableGroup'` predicate. Ordinary stability then
restricts to every eligible R.

Source correction: Definition 2 prints `AC_H(P)/P`; the preceding ordinary
definition and the next-page comparison force `AC_H(P)/C_H(P)`, in the same
quotient as the right-hand side. This module uses that corrected denominator.
The page-55 Sylow comparison is a separate theorem task; the later Q/D-group
standing configurations impose additional hypotheses, not changes to these
definitions.
-/

@[expose] public section

namespace ABG

open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem inf_pPrimeCore_sup_eq (R P : Subgroup H)
    (hR : IsPGroup p R) (hPR : P ≤ R) : R ⊓ (pPrimeCore p H ⊔ P) = P := by
  have hdis : R ⊓ pPrimeCore p H = ⊥ := by
    apply (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨exponent, hcard⟩ := IsPGroup.iff_card.mp hR
    rw [hcard]
    exact (pPrimeCore_coprime_card (G := H) (p := p)).pow_left exponent
  apply le_antisymm
  · intro element helement
    obtain ⟨core, hcore, point, hpoint, heq⟩ :=
      Subgroup.mem_sup_of_normal_left.mp helement.2
    have hcoreR : core ∈ R := by
      have := R.mul_mem helement.1 (R.inv_mem (hPR hpoint))
      simpa [← heq] using this
    have hcoreOne : core = 1 := by
      have : core ∈ R ⊓ pPrimeCore p H := ⟨hcoreR, hcore⟩
      simpa [hdis] using this
    have hpointEq : point = element := by simpa [hcoreOne] using heq
    exact hpointEq ▸ hpoint
  · exact le_inf hPR le_sup_right

theorem relative_subgroup_normalized (R P : Subgroup H)
    (hR : IsPGroup p R) (hPR : P ≤ R)
    (hnormal : (pPrimeCore p H ⊔ P).Normal) :
    R ≤ Subgroup.normalizer (P : Set H) := by
  let := hnormal
  rw [← inf_pPrimeCore_sup_eq R P hR hPR]
  exact (le_inf Subgroup.le_normalizer (by rw [Subgroup.normalizer_eq_top]; exact le_top)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

/-- The solvable radical: the join of all normal solvable subgroups. -/
def solvableRadical (H : Type*) [Group H] : Subgroup H :=
  sSup {K : Subgroup H | K.Normal ∧ Group.IsSolvable K}

instance solvableRadical_normal : (solvableRadical H).Normal :=
  Subgroup.normal_sSup _ fun _ hK => hK.1

omit [Finite H] in
theorem le_solvableRadical (K : Subgroup H) (hnormal : K.Normal)
    (hsolvable : Group.IsSolvable K) : K ≤ solvableRadical H :=
  le_sSup ⟨hnormal, hsolvable⟩

/-- ABG II.6 Definition 1, with the actual odd core. -/
def PConstrainedWithinOddCore (p : ℕ) [Fact p.Prime] (H : Type*)
    [Group H] [Finite H] : Prop :=
  PConstrainedGroup (G := H) p ∧ pPrimeCore p H ≤ pPrimeCore 2 H

/-- ABG II.6 Definition 1, with the actual solvable radical. -/
def PConstrainedWithinSolvableRadical (p : ℕ) [Fact p.Prime] (H : Type*)
    [Group H] [Finite H] : Prop :=
  PConstrainedGroup (G := H) p ∧ pPrimeCore p H ≤ solvableRadical H

/-- Both alternatives of ABG II.6 Definition 2(b), without choosing one. -/
def RelativeStabilityAlternatives (p : ℕ) [Fact p.Prime] (R : Subgroup H) : Prop :=
  (∃ S : Sylow p H, R ≤ (S : Subgroup H) ∧
    (R.subgroupOf (S : Subgroup H)).Normal) ∨
  ∀ (K : Subgroup H) (_ : K.Normal),
    pCore p (H ⧸ K) ≤ R.map (QuotientGroup.mk' K)

/-- The p-subgroup and both eligibility clauses in Definition 2. -/
def RelativeStabilityEligible (p : ℕ) [Fact p.Prime] (R : Subgroup H) : Prop :=
  IsPGroup p R ∧
    (∃ S : Sylow p (Op_p'p p H),
      (S : Subgroup (Op_p'p p H)) = R.subgroupOf (Op_p'p p H)) ∧
    RelativeStabilityAlternatives p R

/-- The faithful normalizer action group `N_H(P)/C_H(P)`. -/
abbrev NormalizerAction (P : Subgroup H) :=
  (Subgroup.normalizer (P : Set H)) ⧸
    (Subgroup.centralizer (P : Set H)).subgroupOf
      (Subgroup.normalizer (P : Set H))

/-- The quotient is exactly the group of automorphisms induced by the normalizer. -/
noncomputable def normalizerActionEquivRange (P : Subgroup H) :
    NormalizerAction P ≃* P.normalizerMonoidHom.range :=
  (QuotientGroup.quotientMulEquivOfEq P.normalizerMonoidHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivRange P.normalizerMonoidHom)

/-- The entire actor maps to the quotient, not merely its intersection with the normalizer. -/
def normalizerActionHom (P A : Subgroup H)
    (hAP : A ≤ Subgroup.normalizer (P : Set H)) : A →* NormalizerAction P :=
  (QuotientGroup.mk' ((Subgroup.centralizer (P : Set H)).subgroupOf
    (Subgroup.normalizer (P : Set H)))).comp (Subgroup.inclusion hAP)

/-- The image is formed only after proving that the whole actor normalizes P. -/
def NormalizerActionImage (P A : Subgroup H)
    (_hAP : A ≤ Subgroup.normalizer (P : Set H)) : Subgroup (NormalizerAction P) :=
  (A.subgroupOf (Subgroup.normalizer (P : Set H))).map
    (QuotientGroup.mk' ((Subgroup.centralizer (P : Set H)).subgroupOf
      (Subgroup.normalizer (P : Set H))))

omit [Finite H] in
theorem normalizerActionHom_range (P A : Subgroup H)
    (hAP : A ≤ Subgroup.normalizer (P : Set H)) :
    (normalizerActionHom P A hAP).range = NormalizerActionImage P A hAP := by
  ext element
  constructor
  · rintro ⟨actor, rfl⟩
    exact ⟨Subgroup.inclusion hAP actor, actor.property, rfl⟩
  · rintro ⟨actor, hactor, rfl⟩
    exact ⟨⟨actor, hactor⟩, rfl⟩

/-- The nontrivial-subgroup clause of ordinary stability in the source. -/
def PStabilityClause (p : ℕ) (H : Type*) [Group H] [Finite H] : Prop :=
  ∀ P A : Subgroup H, P ≠ ⊥ → (pPrimeCore p H ⊔ P).Normal →
    IsPGroup p P → IsPGroup p A →
    ∀ hAP : A ≤ Subgroup.normalizer (P : Set H),
      ⁅⁅P, A⁆, A⁆ = ⊥ → NormalizerActionImage P A hAP ≤ pCore p (NormalizerAction P)

/-- Ordinary p-stability in the recalled ABG domain, not the broader library predicate. -/
def PStable (p : ℕ) [Fact p.Prime] (H : Type*) [Group H] [Finite H] : Prop :=
  p ≠ 2 ∧ pCore p H ≠ ⊥ ∧ PStabilityClause p H

/-- ABG II.6 Definition 2, using the corrected denominator `C_H(P)`. -/
def RelativePStable (p : ℕ) [Fact p.Prime] (R : Subgroup H) : Prop :=
  p ≠ 2 ∧ pCore p H ≠ ⊥ ∧ ∃ hR : RelativeStabilityEligible p R,
    ∀ P A : Subgroup H, P ≠ ⊥ → ∀ hPR : P ≤ R,
      ∀ hnormal : (pPrimeCore p H ⊔ P).Normal, ∀ hAR : A ≤ R,
        ⁅⁅P, A⁆, A⁆ = ⊥ →
          NormalizerActionImage P A
            (hAR.trans (relative_subgroup_normalized R P hR.1 hPR hnormal)) ≤
              pCore p (NormalizerAction P)

omit [Finite H] in
theorem normalizerActionImage_bot (A : Subgroup H)
    (hA : A ≤ Subgroup.normalizer ((⊥ : Subgroup H) : Set H)) :
    NormalizerActionImage ⊥ A hA = ⊥ := by
  apply (Subgroup.map_eq_bot_iff _).mpr
  intro actor _
  apply (QuotientGroup.eq_one_iff _).mpr
  change ∀ element ∈ (⊥ : Subgroup H), element * (actor : H) = (actor : H) * element
  intro element helement
  have heq : element = 1 := helement
  simp [heq]

omit [Fact p.Prime] in
theorem pStabilityClause_iff : PStabilityClause p H ↔ PStableGroup' (G := H) p := by
  constructor
  · intro hstable P A hnormal hP hA hAP hcomm
    by_cases hbot : P = ⊥
    · subst P
      change NormalizerActionImage ⊥ A hAP ≤ pCore p (NormalizerAction ⊥)
      rw [normalizerActionImage_bot]
      exact bot_le
    · exact hstable P A hbot hnormal hP hA hAP hcomm
  · intro hstable P A _ hnormal hP hA hAP hcomm
    exact hstable P A hnormal hP hA hAP hcomm

theorem pStable_iff : PStable p H ↔
    p ≠ 2 ∧ pCore p H ≠ ⊥ ∧ PStableGroup' (G := H) p := by
  rw [PStable, pStabilityClause_iff]

theorem PStable.relative (hstable : PStable p H) (R : Subgroup H)
    (hR : RelativeStabilityEligible p R) : RelativePStable p R := by
  refine ⟨hstable.1, hstable.2.1, hR, ?_⟩
  intro P A hP hPR hnormal hAR hcomm
  exact hstable.2.2 P A hP hnormal (hR.1.to_le hPR) (hR.1.to_le hAR)
    (hAR.trans (relative_subgroup_normalized R P hR.1 hPR hnormal)) hcomm

end ABG

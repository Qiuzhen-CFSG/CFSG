module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Basic
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.SourceFactors.Permutation
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source
public import Theory.Quasithin.Rank

/-!
# The solvable quotient input in 15.4.12

This file records the two earlier source interfaces used in the first
paragraph of the proof of Lemma 15.4.12.  The quotient is the literal
`M / O₂(M)` used by `FamilySource.quotientMap`; the Sylow subgroup is mapped
through that same homomorphism.  The B.2.16 alternative is extracted only
from its universal source contract, and the noncentrality premise is kept
explicit.  In particular, this module does not assume a nonempty family,
normality of a member, a rank bound for the resulting `Xbar`, or a
classification of its images.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 15.4.12, printed pp. 1160--1161 (PDF pp. 1177--1178), together with
Lemma A.1.31(1), printed p. 28, and Theorem B.2.16, printed p. 79.
-/

@[expose] public section

set_option linter.style.haveILetI false

open Subgroup Stellmacher
open scoped Pointwise
open CFSG.Quasithin.Chapter1.RadicalNormalizers.ThompsonSource
open CFSG.Quasithin.Chapter15.Section04

namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.QuotientStructure

universe u

/-! The exact universal premise of A.1.31(1). -/

/--
The first clause of A.1.31, with the source rank bound on the prequotient
group.  `N` is the normal subgroup used to form the quotient, and `R` is the
nontrivial two-subgroup in the quotient.  The conclusion is the literal
cyclicity of `C_{O_p(G/N)}(R)`.

This is a parameter for source applications; it is deliberately not a
replacement theorem whose conclusion is built into a local setup record.
-/
def A131One : Prop :=
  ∀ {H : Type u} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] {N : Subgroup H} [N.Normal],
    primeRank p H ≤ 2 → Odd p →
      Theory.GroupTheory.generalizedFitting (H ⧸ N) = pCore p (H ⧸ N) →
      ∀ R : Subgroup (H ⧸ N), IsPGroup 2 R → R ≠ ⊥ →
        IsCyclic (pCore p (H ⧸ N) ⊓ centralizer (R : Set (H ⧸ N)) :
          Subgroup (H ⧸ N))

/-- Applying the A.1.31(1) parameter to one concrete quotient. -/
theorem a131One_centralizer
    (hA : A131One.{u}) {H : Type u} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] {N : Subgroup H} [N.Normal]
    (hrank : primeRank p H ≤ 2) (hp : Odd p)
    (hgf : Theory.GroupTheory.generalizedFitting (H ⧸ N) = pCore p (H ⧸ N))
    (R : Subgroup (H ⧸ N)) (hR : IsPGroup 2 R) (hRne : R ≠ ⊥) :
    IsCyclic (pCore p (H ⧸ N) ⊓ centralizer (R : Set (H ⧸ N)) :
      Subgroup (H ⧸ N)) := by
  exact hA hrank hp hgf R hR hRne

variable {G : Type*} [Group G]

/-- The Sylow subgroup in the actual `M / O₂(M)` quotient. -/
noncomputable def quotientSylow [Finite G] (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) : Sylow 2 (CoreQuotient M) :=
  (T.subtype hTM).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 M))

@[simp] theorem quotientSylow_coe [Finite G] (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) :
    ((quotientSylow T M hTM : Subgroup (CoreQuotient M))) =
      (T.subtype hTM : Subgroup M).map (quotientMap M) := by
  rfl

/-- The quotient map used by `quotientSylow` is the map already fixed in
`SourceConstruction.Basic`; no alternate quotient or conjugate Sylow is
introduced by the source extraction. -/
theorem quotientSylow_map_eq [Finite G] (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) :
    ((quotientSylow T M hTM : Subgroup (CoreQuotient M))) =
      image M (T : Subgroup G) := by
  rw [quotientSylow_coe]
  rfl

/-! The fixed quotient coordinates agree with the centralizer quotient. -/

/--
The kernel of the fixed map `M → M/O₂(M)` is the centralizer in `M` of the
actual local module `V(M)`.  This is the subgroup form of 15.4.11(1), with
the ambient equality transported through `M.subtype`.
-/
theorem quotientMap_kernel_eq_localV_centralizer [Finite G]
    (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) =
      (T : Subgroup G)) :
    (quotientMap M).ker =
      centralizer ((localV (T : Subgroup G) M).subgroupOf M : Set M) := by
  rw [quotientMap, QuotientGroup.ker_mk']
  apply map_injective M.subtype_injective
  rw [Subgroup.map_centralizer_subtype]
  rw [show (pCore 2 M).map M.subtype = M.pCoreIn 2 from rfl]
  have hvle : localV (T : Subgroup G) M ≤ M := map_subtype_le _
  rw [map_subgroupOf_eq_of_le hvle]
  exact (localV_centralizer T M hTM hC).symm

/-! The B.2.16 extraction. -/

/--
The noncentral alternative of B.2.16.  The source noncentrality condition is
kept as a statement about the actual Thompson subgroup and the actual
normal closure in the quotient.  Once it is supplied, the first alternative
of B.2.16 is eliminated and the exceptional factor datum is obtained.
-/
theorem exceptional_of_noncentral
    (hB : TheoremB216.{u}) (Q : Type u) [Group Q] [Finite Q]
    (hsolv : Group.IsSolvable Q)
    (hgf : Theory.GroupTheory.generalizedFitting Q = pCore 2 Q)
    (S : Sylow 2 Q)
    (hnoncentral : ¬ elementaryAbelianMaxJ (S : Subgroup Q) ≤
      centralizer (closure S : Set Q)) :
    ∃ hE : IsElementaryAbelian 2 (closure S),
      ∃ d : @Exceptional Q _ S hE, Nonempty (Fin d.count) := by
  have h := hB Q hsolv hgf S
  refine ⟨h.elementary, ?_⟩
  letI : IsElementaryAbelian 2 (closure S) := h.elementary
  have halt := h.alternatives
  rcases halt with hfirst | hd
  · exact (hnoncentral hfirst.1).elim
  · rcases hd with ⟨d⟩
    exact ⟨d, Exceptional.nonempty_factors d⟩

/-- Every factor supplied by the exceptional B.2.16 alternative is the
literal `PSL₂(2)` model, hence has order six. -/
theorem exceptional_factor_card
    {Q : Type u} [Group Q] [Finite Q] {S : Sylow 2 Q}
    [IsElementaryAbelian 2 (closure S)] (d : Exceptional S)
    (i : Fin d.count) : Nat.card (d.factor i) = 6 := by
  have hmodel := d.factorModel i
  have hcard : Nat.card
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    calc
      _ = Nat.card (Equiv.Perm (Fin 3)) := Nat.card_congr
        (Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two.symm.trans e).toEquiv
      _ = 6 := by rw [Nat.card_perm, Nat.card_fin]; decide
  exact (Nat.card_congr hmodel.toEquiv).trans hcard

/--
The exceptional branch has a genuine three divisor in the ambient solvable
quotient.  This is the source divisibility alternative used when the
factorization branch of B.2.16 is ruled out by the quotient order.
-/
theorem exceptional_three_dvd_card
    {Q : Type u} [Group Q] [Finite Q] {S : Sylow 2 Q}
    [IsElementaryAbelian 2 (closure S)] (d : Exceptional S) :
    3 ∣ Nat.card Q := by
  exact d.three_dvd_card

/--
The exact B.2.16 dichotomy in a quotient: either the normalizer/centralizer
factorization holds, or the exceptional branch forces divisibility by three.
No conclusion about the family `Y` is folded into this earlier-source
alternative.
-/
theorem quotient_factorization_or_three_dvd
    (hB : TheoremB216.{u}) (Q : Type u) [Group Q] [Finite Q]
    (hsolv : Group.IsSolvable Q)
    (hgf : Theory.GroupTheory.generalizedFitting Q = pCore 2 Q)
    (S : Sylow 2 Q) :
    ((Set.univ : Set Q) =
        (normalizer (elementaryAbelianMaxJ (S : Subgroup Q) : Set Q) : Set Q) *
        (centralizer (omegaOneCenterAmbient (S : Subgroup Q) : Set Q) : Set Q)) ∨
      3 ∣ Nat.card Q := by
  have h := hB Q hsolv hgf S
  letI : IsElementaryAbelian 2 (closure S) := h.elementary
  have halt := h.alternatives
  rcases halt with hfirst | hd
  · exact Or.inl hfirst.2
  · rcases hd with ⟨d⟩
    exact Or.inr d.three_dvd_card

/-- The canonical quotient candidate from `Basic` is exactly the source
commutator expression; this theorem is intentionally just the definitional
comparison, so later applications cannot silently replace the actual map. -/
theorem xbar_eq_source_commutator (T M : Subgroup G) :
    Xbar T M = ⁅pCore 3 (CoreQuotient M), image M (elementaryAbelianMaxJ T)⁆ := by
  rfl

end CFSG.Quasithin.Chapter15.Section04.FamilySource.QuotientStructure

end

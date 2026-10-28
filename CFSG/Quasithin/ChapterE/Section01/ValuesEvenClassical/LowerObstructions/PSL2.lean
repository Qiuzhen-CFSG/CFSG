module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSL2.RankOne
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.PrimeRankFixedJoin
public import GorensteinWalter.PSL2PerfectOfCard
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The PSL₂ lower obstruction in E.1.14(1)

For a finite field of order 2^f, f ≥ 2, a normal simple subgroup isomorphic
to the actual PSL₂ matrix quotient prevents E-generation at rank f - 1.
In particular this applies to L = F*(G) under the source SQTK and G = LT
hypotheses; the lower obstruction does not need those two additional guards.

The upper unipotents are elementary abelian of order 2^f. The proved matrix
Borel geometry puts every proper overgroup of this Sylow subgroup inside its
proper normalizer. Transport through the actual model isomorphism supplies
these facts to the rank-one obstruction. Perfectness excludes solvable kernels.
This argument works in the ambient extension itself and includes outer
2-automorphisms without requiring a separate automorphism classification.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.1--6 and E.1.14(1), printed pp.209--211, 214. The latter cites
Aschbacher (1982), Lemma 4.7; here the lower bound is proved directly using
the concrete PSL₂ Borel calculation also used for F.1.3(1).
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical
open Subgroup BenderSuzuki.Converse CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] [Finite G]

private theorem projectiveSylow_elementary (F : Type*) [Field F] [Finite F] [CharP F 2] :
    IsElementaryAbelian 2 (Linear.projectiveSylow F) := by
  let : IsElementaryAbelian 2 (Multiplicative F) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro a
        change 2 • a.toAdd = 0
        exact CharTwo.two_nsmul a.toAdd }
  let : IsElementaryAbelian 2 (Unip F) :=
    IsElementaryAbelian.of_surjective (uniHom F).rangeRestrict
      (uniHom F).rangeRestrict_surjective
  change IsElementaryAbelian 2 (Linear.projectiveSylow F : Subgroup (PSL2 F))
  rw [Linear.projectiveSylow_coe]
  exact IsElementaryAbelian.map (pi F)

/-- The PSL₂ lower obstruction for every finite ambient extension of the
normal simple model, including all outer 2-automorphisms. -/
theorem not_isEGenerated_of_normal_psl2 (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    {F : Type*} [Field F] [Finite F] {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card F = 2 ^ f)
    (e : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    ¬ IsEGenerated (f - 1) G := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let P₀ := Linear.projectiveSylow F
  let P : Sylow 2 L := P₀.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hP : RankOneSylowFacts P :=
    Linear.transport e.symm P₀ P rfl (Linear.projective_facts F f (by omega) hcard P₀)
  let : IsElementaryAbelian 2 P₀ := projectiveSylow_elementary F
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map e.symm.toMonoidHom
  have hc : Nat.card P = 2 ^ f := by
    change Nat.card ((P₀ : Subgroup (PSL2 F)).map e.symm.toMonoidHom) = _
    rw [← Nat.card_congr ((P₀ : Subgroup (PSL2 F)).equivMapOfInjective
      e.symm.toMonoidHom e.symm.injective).toEquiv]
    change Nat.card (Linear.projectiveSylow F : Subgroup (PSL2 F)) = _
    rw [Linear.projectiveSylow_coe, PUnip_card, hcard]
  have hperf := GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by
    rw [hcard]
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hf
    omega)
  let : Group.IsPerfect L := @Group.IsPerfect.ofSurjective
    (PSL2 F) L _ _ e.symm.toMonoidHom hperf e.symm.surjective
  apply not_isEGenerated_of_normal_rankOne L (Group.IsPerfect.not_isSolvable L) P
    (fun H hPH hH => hP.unique_maximal H hPH (lt_top_iff_ne_top.mpr hH)) hP.proper.ne
  have hr := IsElementaryAbelian.rank_ge_of_card (p := 2) hc
  omega

/-- The lower obstruction in E.1.14(1), using the literal generalized Fitting
subgroup and an actual projective matrix-group isomorphism. -/
theorem not_isEGenerated_of_psl2 [IsSimpleGroup (Theory.GroupTheory.generalizedFitting G)]
    {F : Type*} [Field F] [Finite F] {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card F = 2 ^ f)
    (e : Theory.GroupTheory.generalizedFitting G ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    ¬ IsEGenerated (f - 1) G :=
  not_isEGenerated_of_normal_psl2 _ hf hcard e

/-- Adapter for the concrete model predicate used by the classical-value assembly. -/
theorem not_isEGenerated_of_isPSL2
    [IsSimpleGroup (Theory.GroupTheory.generalizedFitting G)]
    {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSL (Theory.GroupTheory.generalizedFitting G) 2 (2 ^ f)) :
    ¬ IsEGenerated (f - 1) G := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hmodel
  exact not_isEGenerated_of_psl2 hf hcard e

end CFSG.Quasithin.ChapterE.ValuesEvenClassical

module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.SeedAction
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.PairApplications
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaStarSetup
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaCyclicExtension
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.OddCyclicThreeNormalizer

/-!
# The cubic seed relation and its characteristic-two consumer

In the cubic branch, the original Y has order-three image in M/O₂(M).
A two-perfect seed acts trivially on that cubic. The original O₂(M)
lies in S and normalizes the seed, so normalizer lifting proves that
Y normalizes Y₁. Consequently Y₁ is normal in YY₁. Every element
normalizing that literal join gives the same-family conjugate commutator
relation required by the characteristic-two normalizer argument.

Changing the outside element of T does not change either residual factor.
The consumer therefore retains the supplied K₁ and K₂ when using a
Frattini actor. The choice of that actor remains explicit here; this module
does not assert unconditional 15.2.22. Earlier Omega and plane inputs retain
their existing producers and final discharge by the plane-uniqueness owner.

Source: Aschbacher--Smith 15.2.22, printed pp.1114--1115, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding.OmegaAction
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_centralizes_perfect (A B : Subgroup G)
    (hA : Nat.card A = 3) (hB : IsPPerfect 2 B)
    (hn : B ≤ normalizer (A : Set G)) : A ≤ centralizer (B : Set G) := by
  let : IsCyclic A := isCyclic_of_prime_card hA
  have hc : Nat.card (MulAut A) = 2 := by
    rw [IsCyclic.card_mulAut,hA,Nat.totient_prime Nat.prime_three]
  let f : B →* MulAut A := A.normalizerMonoidHom.comp (inclusion hn)
  have hf := hB.hom_eq_one_of_isPGroup (IsPGroup.of_card (p := 2) (n := 1) hc) f
  intro a ha b hb
  have he := congrArg (fun g : B →* MulAut A => (g ⟨b,hb⟩ ⟨a,ha⟩ : G)) hf
  change b * a * b⁻¹ = a at he
  exact mul_inv_eq_iff_eq_mul.mp he

variable {T : Sylow 2 G} {M Mc V H ZS I E : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original two-core lies in the literal centralizer S=C_T(ZS). -/
theorem omega_core_le_planeSylow :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    M.pCoreIn 2 ≤ smallActionS T ZS := by
  let := hsource.prepared.elementary
  intro ho
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hsource.maximal.1.2] using
      pCoreIn_le_sylow M (T.subtype hsource.maximal.1.2)
  refine le_inf hQT ?_
  rintro x ⟨q,hq,rfl⟩
  have hh := source_omega_core_le_kernel hsource.prepared.normalized ho hq
  change q ∈ (action hsource).ker at hh
  rw [action_ker] at hh
  exact centralizer_le d.geometry.plane_le hh

/-- The normal cubic star residual normalizes every corrected seed. -/
theorem Seed.cubic_residual_normalizes
    (s : Seed M I (smallActionS T ZS) E) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 3 →
    Y ≤ normalizer (E : Set G) := by
  let := hsource.prepared.elementary
  intro ho
  dsimp only
  intro hYbar
  let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
  let A := Y.subgroupOf M
  let B := E.subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  have hEM : E ≤ M := s.le_NI.trans inf_le_left
  have hYM : Y ≤ M := source_omega_caseIIResidual_le T hsource.maximal.1.2
    hsource.prepared.normalized ho
  let : A.Normal := source_omega_lemma_15_2_3_2 T hsource.maximal.1.2
    hsource.prepared.normalized ho
  let : (A.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hp : IsPPerfect 2 B := s.perfect.of_surjective
    (subgroupOfEquivOfLe hEM).symm.toMonoidHom (subgroupOfEquivOfLe hEM).symm.surjective
  have hc := cubic_centralizes_perfect (A.map q) (B.map q)
    (source_omega_cyclic_star_card T hsource.maximal.1.2 hsource.partner
      hsource.prepared ho hYbar)
    (hp.of_surjective (q.subgroupMap B) (q.subgroupMap_surjective B))
    le_normalizer_of_normal
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hn : q.ker ≤ normalizer (B : Set M) := by
    rw [QuotientGroup.ker_mk', ←subgroupOf_normalizer_eq hEM]
    intro x hx
    exact s.normalized (omega_core_le_planeSylow d ho (mem_map_of_mem M.subtype hx))
  have hAB : A ≤ normalizer (B : Set M) := by
    rw [←comap_normalizer_map_of_pPerfect q B hp hk hn]
    exact map_le_iff_le_comap.mp (hc.trans (Subgroup.centralizer_le_normalizer _))
  rw [←subgroupOf_normalizer_eq hEM] at hAB
  intro y hy
  exact hAB (show (⟨y,hYM hy⟩ : M) ∈ A from hy)

/-- Relative normality in the actual product YY₁. -/
theorem Seed.cubic_join_normal
    (s : Seed M I (smallActionS T ZS) E) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 3 →
    (E.subgroupOf (Y ⊔ E)).Normal := by
  let := hsource.prepared.elementary
  intro ho
  dsimp only
  intro hYbar
  exact normal_subgroupOf_of_le_normalizer
    (sup_le (s.cubic_residual_normalizes d ho hYbar) E.le_normalizer)

/-- A normalizer of YY₁ supplies the source conjugate-seed relation. -/
theorem Seed.cubic_residual_conjugate_commutator
    (s : Seed M I (smallActionS T ZS) E) (t : G) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 3 →
    t ∈ normalizer ((Y ⊔ E : Subgroup G) : Set G) →
    ⁅E,E.map (MulAut.conj t).toMonoidHom⁆ ≤ E ⊓ E.map (MulAut.conj t).toMonoidHom := by
  let := hsource.prepared.elementary
  intro ho
  dsimp only
  intro hYbar htD
  let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
  let D := Y ⊔ E
  have hDE : D ≤ normalizer (E : Set G) :=
    sup_le (s.cubic_residual_normalizes d ho hYbar) E.le_normalizer
  have hED : E ≤ D := le_sup_right
  have hEtD : E.map (MulAut.conj t).toMonoidHom ≤ D :=
    (map_mono hED).trans_eq (mem_normalizer_iff_map_conj_eq.mp htD)
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp (hEtD.trans hDE))
    (le_normalizer_iff_commutator_le_right.mp
      (hED.trans (normalizes_conjugate_of_normalizes htD hDE)))

omit d [Finite G] in
/-- Every element of the outside coset exchanges the same two residual
factors. Thus choosing the Frattini actor does not change their marking. -/
theorem ResidualPair.conjugate_by_outside {A S K : Subgroup G} {t : G}
    (p : ResidualPair A S K t) (hSA : S ≤ A) (hi : S.relIndex A = 2)
    (u : G) (hu : u ∈ A) (huS : u ∉ S) :
    p.K₁.map (MulAut.conj u).toMonoidHom = p.K₂ := by
  have hv : u * t⁻¹ ∈ S := by
    apply ((S.subgroupOf A).mul_mem_iff_of_index_two hi
      (a := ⟨u,hu⟩) (b := ⟨t⁻¹,A.inv_mem p.t_mem⟩)).mpr
    change u ∈ S ↔ t⁻¹ ∈ S
    simp only [huS,inv_mem_iff,p.t_not_mem]
  have he : p.K₁.map (MulAut.conj u).toMonoidHom =
      (p.K₁.map (MulAut.conj t).toMonoidHom).map
        (MulAut.conj (u * t⁻¹)).toMonoidHom := by
    change p.K₁.conjBy u = (p.K₁.conjBy t).conjBy (u*t⁻¹)
    rw [conjBy_conjBy,inv_mul_cancel_right]
  rw [he,p.conjugate]
  exact mem_normalizer_iff_map_conj_eq.mp ((p.second_normalized hSA hi) hv)

/-- The cubic branch with a specified Frattini actor. The actor normalizes
the literal YY₁, and the original residual factors are retained. -/
theorem source_15_2_22_of_cubic_actor
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (s : Seed M I (smallActionS T ZS) E)
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    {t : G} (p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t)
    (u : G) (hu : u ∈ (T : Subgroup G)) (huS : u ∉ smallActionS T ZS) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 3 →
    u ∈ normalizer ((Y ⊔ E : Subgroup G) : Set G) →
    ¬ ⁅E,p.K₂⁆ ≤ E ⊓ p.K₂ := by
  let := hsource.prepared.elementary
  intro ho
  dsimp only
  intro hc hn
  let q : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) u := {
    K₁ := p.K₁
    K₂ := p.K₂
    t_mem := hu
    t_not_mem := huS
    first := p.first
    second := p.second
    span := p.span
    conjugate := p.conjugate_by_outside inf_le_left (d.escape_index hI).2 u hu huS
    normalized := p.normalized }
  exact commutator_exclusion_of_residualPair d hI hfit q s hC
    (s.cubic_residual_conjugate_commutator d u ho hc hn)

/-- Construct the actual pair from reducibility and consume the cubic
normalization result. Only selection of the Frattini actor is still explicit. -/
theorem exists_pair_exclusion_of_cubic_actor
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    (s : Seed M I (smallActionS T ZS) E)
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T ZS) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 3 →
    (∃ u : G, u ∈ (T : Subgroup G) ∧ u ∉ smallActionS T ZS ∧
      u ∈ normalizer ((Y ⊔ E : Subgroup G) : Set G)) →
    ∃ p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t,
      ¬ ⁅E,p.K₂⁆ ≤ E ⊓ p.K₂ := by
  let := hsource.prepared.elementary
  intro ho
  dsimp only
  rintro hc ⟨u,hu,huS,hn⟩
  obtain ⟨p⟩ := exists_residualPair d hI hnot t ht htS
  exact ⟨p,source_15_2_22_of_cubic_actor d hI hfit s hC p u hu huS ho hc hn⟩

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource

module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.Inputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.Residual
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.Theta

/-!
# Constructing the Borel intermediate data

Write A = O²(Y₊ ∩ L) and B = N_L(S ∩ L). Restrict the local Sylow
subgroup to the relatively normal component and use the original quotient
marking L/O₂(L) ≃ PSL₃(F). The entire two-kernel lies in S ∩ L, so
projective Sylow invariance lifts to G and identifies B with the literal
preimage of its projective normalizer. Source 15.3.33(1) then places B in
M ∩ I. The exponent-three quotient gives θ(A) = A; source 15.3.11(6)
gives θ(B) = A. The outer cubic actor forces 3 ∤ n before the theta-core
and quotient calculations are applied.

For the normalizer equality, the uniform earlier 15.3.34 input excludes a
second ordinary component: its element of order three would centralize L
and violate m₃(I) ≤ 2. The intrinsic central-cover normalizer calculation
and 15.3.33(1) give N_I(B) ≤ M ∩ I. Conversely, M ∩ I normalizes A,
hence O₂(A) = S ∩ L and B. All three projective image equalities use the
same marking, including the theta image obtained by lifting order-three
elements through a two-group kernel.

This is a conditional construction. `ProjectiveBorelCalculations` contains
the solvable projective stabilizer and outer cubic parameter calculations.
`CentralCoverBorelCalculations` contains the intrinsic characteristic-two,
theta-core, theta-quotient and overgroup-normalizer calculations, each for
literal preimages under `projectiveMap`. These model inputs and uniform
15.3.34 must still be supplied by the source assembly. They contain no
local plane, placement, invariance, or n = 2 hypothesis. In particular,
O²(B) is never identified with θ(B).

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.11, 15.3.33--34 and the opening of the proof of 15.3.38,
printed pp.1121--1125 and 1134--1136.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

/-- Pull back a subgroup through the specified projective quotient, then embed in G. -/
def projectivePreimage {q : ℕ} (c : ProjectiveMarking L q)
    (H : Subgroup PSL(3,c.F)) : Subgroup G :=
  (H.comap (projectiveMap c)).map L.subtype

/-- Intrinsic projective calculations, with no local module or plane choices. -/
structure ProjectiveBorelCalculations {n : ℕ} (c : ProjectiveMarking L (2 ^ n)) : Prop where
  solvable : 0 < n → Even n → ∀ P : Sylow 2 PSL(3,c.F),
    ∀ A : Subgroup (MulAut PSL(3,c.F)), Group.IsSolvable A →
    (P : Subgroup PSL(3,c.F)).map MulAut.conj ≤ A →
    ∀ α ∈ A, (P : Subgroup PSL(3,c.F)).map α.toMonoidHom = P
  parameter : 0 < n → Even n → ∀ P : Sylow 2 PSL(3,c.F),
    ∀ a : Matrix.GeneralLinearGroup (Fin 3) c.F,
    let α := Matrix.PSL3.OuterSolvable.linearConj c.F a
    α ∉ MulAut.innerSubgroup PSL(3,c.F) → α ^ 3 = 1 →
    (P : Subgroup PSL(3,c.F)).map α.toMonoidHom = P → ¬ 3 ∣ n

/-- Central-cover Borel calculations through the actual quotient map.
The last clause concerns any overgroup with this unique ordinary component.
None of these clauses asserts local placement or invariance. -/
structure CentralCoverBorelCalculations {n : ℕ} (c : ProjectiveMarking L (2 ^ n)) : Prop where
  characteristic_two : pCore 2 L ≤ center L → ∀ P : Sylow 2 PSL(3,c.F),
    generalizedFitting (projectivePreimage c (normalizer (P : Set PSL(3,c.F)))) =
      pCore 2 (projectivePreimage c (normalizer (P : Set PSL(3,c.F))))
  theta_core : 0 < n → Even n → Group.IsPerfect L → pCore 2 L ≤ center L → ¬ 3 ∣ n →
    ∀ P : Sylow 2 PSL(3,c.F),
    (theta (projectivePreimage c (normalizer (P : Set PSL(3,c.F))))).pCoreIn 2 =
      projectivePreimage c P
  theta_quotient : 0 < n → Even n → Group.IsPerfect L → pCore 2 L ≤ center L → ¬ 3 ∣ n →
    ∀ P : Sylow 2 PSL(3,c.F),
    Nat.card (theta (projectivePreimage c (normalizer (P : Set PSL(3,c.F)))) ⧸
      pCore 2 (theta (projectivePreimage c (normalizer (P : Set PSL(3,c.F)))))) = 3
  normalizer_characteristic_two : ∀ J : Subgroup G, L ≤ J →
    (L.subgroupOf J).Normal → IsComponent J (L.subgroupOf J) →
    (∀ K : Subgroup J, IsComponent J K → K = L.subgroupOf J) →
    pPrimeCore 2 J = ⊥ → pCore 2 L ≤ center L → ∀ P : Sylow 2 PSL(3,c.F),
    generalizedFitting (J ⊓ normalizer
      (projectivePreimage c (normalizer (P : Set PSL(3,c.F))) : Set G) : Subgroup G) =
    pCore 2 (J ⊓ normalizer
      (projectivePreimage c (normalizer (P : Set PSL(3,c.F))) : Set G) : Subgroup G)

omit [Finite G] in
theorem projectiveMap_surjective {q : ℕ} (c : ProjectiveMarking L q) :
    Function.Surjective (projectiveMap c) :=
  c.equivalence.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The exponent-three two-core quotient identifies the component residual with its theta subgroup. -/
theorem component_residual_generated (e : Earlier d) :
    theta (componentPart d.Yplus L) = componentPart d.Yplus L := by
  let X := d.Yplus ⊓ L
  let f := (QuotientGroup.mk' (pCore 2 d.Yplus)).comp (inclusion (show X ≤ d.Yplus from inf_le_left))
  have ht : componentPart d.Yplus L = theta X := by
    apply FusionCore.CosetSetup.ExtraspecialLocal.twoResidual_eq_theta_of_exponent_three X f
    · change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 d.Yplus)).ker.comap (inclusion _))
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
    · intro x
      exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp e.quotient_exponent) (f x)
  rw [ht, theta_idempotent]

/-- The positive-three-order clause of 15.3.34 excludes every second ordinary component. -/
theorem Setup.unique_component (h : Setup d I L) (e : Earlier d)
    (h34 : ∀ K : Subgroup I, IsComponent I K → 3 ∣ Nat.card K)
    {K : Subgroup I} (hK : IsComponent I K) : K = L.subgroupOf I := by
  by_contra hn
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 (h34 K hK)
  have hc := commutator_eq_bot_iff_le_centralizer.mp
    (hK.commutator_eq_bot_of_ne h.component hn)
  apply no_centralizing_three (e.rank I h.outside)
    (show 2 ≤ primeRank 3 (L.subgroupOf I) from ?_)
    (component_center_eq_twoCore h.component (e.odd I h.outside)).le
    ((Subgroup.orderOf_coe x).trans hx) (hc x.property)
  rw [primeRank_equiv 3 (subgroupOfEquivOfLe h.component_le), h.component_rank]

/-- The actual local Sylow maps onto a projective Sylow and is its full preimage. -/
theorem Setup.projective_sylow (h : Setup d I L) (e : Earlier d)
    {q : ℕ} (c : ProjectiveMarking L q) :
    ∃ P : Sylow 2 PSL(3,c.F), (d.S.subgroupOf L).map (projectiveMap c) = P ∧
      projectivePreimage c P = d.S ⊓ L := by
  obtain ⟨T, hT⟩ := e.sylow I h.outside
  obtain ⟨P, hP⟩ := Candidates.LinearCore.MatrixImage.quotient_sylow
    h.component_le (h.normal e).isSubnormal T hT c.equivalence
  refine ⟨P, hP.symm, ?_⟩
  have hker : (projectiveMap c).ker ≤ d.S.subgroupOf L := by
    rw [projectiveMap_ker]
    have hp : (pCore 2 L).map L.subtype ≤ d.S := by
      have hn : L ≤ I := h.component_le
      have hh : L.pCoreIn 2 ≤ I.pCoreIn 2 :=
        pCoreIn_mono_of_normalizes hn (h.normalizes_component e)
      exact hh.trans (hT ▸ pCoreIn_le_sylow I T)
    intro x hx
    exact hp (mem_map_of_mem L.subtype hx)
  unfold projectivePreimage
  rw [hP]
  change (((d.S.subgroupOf L).map (projectiveMap c)).comap (projectiveMap c)).map L.subtype = _
  rw [comap_map_eq_self hker, subgroupOf_map_subtype]

omit [Finite G] in
/-- The local Borel is the full preimage of the projective Sylow normalizer. -/
theorem borel_eq_projectivePreimage {q : ℕ} (c : ProjectiveMarking L q)
    (P : Sylow 2 PSL(3,c.F))
    (hP : projectivePreimage c P = d.S ⊓ L) :
    borel d.S L = projectivePreimage c (normalizer (P : Set PSL(3,c.F))) := by
  unfold projectivePreimage at hP ⊢
  change borel d.S L = ((normalizer ((P : Subgroup PSL(3,c.F)) : Set PSL(3,c.F))).comap (projectiveMap c)).map L.subtype
  rw [comap_normalizer_eq_of_surjective (P : Subgroup PSL(3,c.F)) (projectiveMap_surjective c)]
  let H := (P : Subgroup PSL(3,c.F)).comap (projectiveMap c)
  have hh : normalizer H = (normalizer (H.map L.subtype)).subgroupOf L := by
    rw [subgroupOf_normalizer_eq (map_subtype_le H)]
    exact congrArg (fun K : Subgroup L => normalizer (K : Set L)) (comap_map_eq_self_of_injective L.subtype_injective H).symm
  rw [hh, subgroupOf_map_subtype, hP]
  exact inf_comm _ _

/-- The solvable local action contains the inner image of the entire projective Sylow. -/
theorem projective_sylow_invariant (h : Setup d I L) (e : Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (m : ProjectiveBorelCalculations c) (P : Sylow 2 PSL(3,c.F))
    (hP : (d.S.subgroupOf L).map (projectiveMap c) = P) :
    ∀ g : (d.Yplus ⊔ d.S : Subgroup G),
      (P : Subgroup PSL(3,c.F)).map
        (markedAction c ⟨g, h.normalizes_component e (h.outside.1.2 g.property)⟩).toMonoidHom = P := by
  let f := (markedAction c).comp (inclusion (h.outside.1.2.trans (h.normalizes_component e)))
  have hs : Group.IsSolvable f.range := by
    let := e.solvable
    exact Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hp : (P : Subgroup PSL(3,c.F)).map MulAut.conj ≤ f.range := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hP] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    refine ⟨⟨l, mem_sup_right hl⟩, ?_⟩
    exact markedAction_on_component c l
  intro g
  exact m.solvable hn heven P f.range hs hp (f g) ⟨g, rfl⟩

/-- Projective invariance lifts because the full two-kernel is in S ∩ L. -/
theorem component_sylow_invariant (h : Setup d I L) (e : Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (m : ProjectiveBorelCalculations c) (P : Sylow 2 PSL(3,c.F))
    (hP : (d.S.subgroupOf L).map (projectiveMap c) = P)
    (hpre : projectivePreimage c P = d.S ⊓ L) :
    d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  rw [← hpre] at hx ⊢
  obtain ⟨l, hl, rfl⟩ := hx
  let a : normalizer (L : Set G) := ⟨g, h.normalizes_component e (h.outside.1.2 hg)⟩
  refine ⟨L.normalizerMonoidHom a l, ?_, rfl⟩
  change projectiveMap c (L.normalizerMonoidHom a l) ∈ (P : Subgroup PSL(3,c.F))
  rw [← markedAction_apply]
  have hi := projective_sylow_invariant h e hn heven c m P hP ⟨g, hg⟩
  rw [← hi]
  exact mem_map_of_mem _ hl

/-- An outer cubic matrix actor preserving a Sylow forces the necessary parameter restriction. -/
theorem three_not_dvd_parameter (h : Setup d I L) (e : Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (m : ProjectiveBorelCalculations c) (P : Sylow 2 PSL(3,c.F))
    (hP : (d.S.subgroupOf L).map (projectiveMap c) = P)
    {y : G} (hy : y ∈ d.Yplus) (hdiag : c.Diagonal y) : ¬ 3 ∣ n := by
  obtain ⟨hy3, a, ha, hr⟩ := hdiag
  let yn : normalizer (L : Set G) :=
    ⟨y, h.normalizes_component e (h.outside.1.2 (mem_sup_left hy))⟩
  have heq := markedAction_eq_of_realizes c yn hr
  apply m.parameter hn heven P a ha
  · rw [← heq, ← map_pow]
    have hyc : yn ^ 3 = 1 := by
      apply Subtype.ext
      exact hy3 ▸ pow_orderOf_eq_one y
    rw [hyc, map_one]
  · rw [← heq]
    exact projective_sylow_invariant h e hn heven c m P hP ⟨y, mem_sup_left hy⟩

omit [Finite G] in
theorem projectivePreimage_image {q : ℕ} (c : ProjectiveMarking L q)
    (H : Subgroup PSL(3,c.F)) :
    ((projectivePreimage c H).subgroupOf L).map (projectiveMap c) = H := by
  unfold projectivePreimage subgroupOf
  rw [comap_map_eq_self_of_injective L.subtype_injective,
    map_comap_eq_self (by intro x _; exact projectiveMap_surjective c x)]

/-- Order-three lifting identifies the theta image, without a two-residual shortcut. -/
theorem theta_projective_image {q : ℕ} (c : ProjectiveMarking L q)
    {B : Subgroup G} (hBL : B ≤ L) :
    ((theta B).subgroupOf L).map (projectiveMap c) =
      theta ((B.subgroupOf L).map (projectiveMap c)) := by
  have ht : (theta B).subgroupOf L = theta (B.subgroupOf L) := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((theta_le B).trans hBL),
      theta_map_of_injective L.subtype L.subtype_injective,
      map_subgroupOf_eq_of_le hBL]
  rw [ht]
  apply FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.theta_map_of_twoGroup_ker
  rw [projectiveMap_ker]
  exact pCore_isPGroup

/-- Conditional construction of the Borel output from precise intrinsic calculations.
The uniform positive-three-order input is the earlier 15.3.34, applied to
ordinary components of I. It is used to discharge uniqueness in the
central-cover normalizer calculation. -/
theorem borelStep_of_calculations (h : Setup d I L) (e : Earlier d)
    (h34 : ∀ K : Subgroup I, IsComponent I K → 3 ∣ Nat.card K)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    {y : G} (hy : y ∈ d.Yplus) (hdiag : c.Diagonal y)
    (hproduct : (d.Yplus : Set G) = (componentPart d.Yplus L : Set G) * (zpowers y : Set G))
    (m : ProjectiveBorelCalculations c) (k : CentralCoverBorelCalculations c) :
    Nonempty (BorelStep d I L c) := by
  obtain ⟨P, hP, hpre⟩ := h.projective_sylow e c
  have hB := borel_eq_projectivePreimage c P hpre
  have hnL := h.outside.1.2.trans (h.normalizes_component e)
  have hnSL := component_sylow_invariant h e hn heven c m P hP hpre
  have hinv : d.Yplus ⊔ d.S ≤ normalizer (borel d.S L : Set G) :=
    le_normalizer_inf hnL (hnSL.trans (normalizer ((d.S ⊓ L : Subgroup G) : Set G)).le_normalizer)
  have hchar : generalizedFitting (borel d.S L) = pCore 2 (borel d.S L) :=
    hB ▸ k.characteristic_two (h.core_central e) P
  have hBM : borel d.S L ≤ d.M ⊓ I := by
    let := e.solvable
    exact lemma_15_3_33_1 h.outside e.sylow e.exclusion e.odd
      (inf_le_left.trans h.component_le) hinv hchar
  have hAY : componentPart d.Yplus L ≤ d.Yplus := by
    intro a ha
    change a ∈ (d.Yplus : Set G)
    rw [hproduct]
    exact ⟨a, ha, 1, one_mem _, mul_one a⟩
  have hAB : componentPart d.Yplus L ≤ borel d.S L :=
    le_inf ((map_subtype_le _).trans inf_le_right) ((hAY.trans le_sup_left).trans hnSL)
  have hgen : theta (componentPart d.Yplus L) = componentPart d.Yplus L :=
    component_residual_generated e
  have htheta : theta (borel d.S L) = componentPart d.Yplus L := by
    apply le_antisymm
    · apply (closure_le _).mpr
      rintro x ⟨hx, hx3⟩
      exact Candidates.LinearCore.MatrixImage.order_three_mem_componentPart
        (e.theta_eq I h.outside ▸ subset_closure ⟨hBM hx, hx3⟩) hx.1 hx3
    · exact hgen.ge.trans (theta_mono hAB)
  have hparam := three_not_dvd_parameter h e hn heven c m P hP hy hdiag
  have hcore : (theta (borel d.S L)).pCoreIn 2 = d.S ⊓ L := by
    rw [hB, k.theta_core hn heven h.perfect (h.core_central e) hparam P, hpre]
  have hquot : Nat.card (theta (borel d.S L) ⧸ pCore 2 (theta (borel d.S L))) = 3 := by
    rw [hB]
    exact k.theta_quotient hn heven h.perfect (h.core_central e) hparam P
  have hNM : I ⊓ normalizer (borel d.S L : Set G) ≤ d.M ⊓ I := by
    let := e.solvable
    apply lemma_15_3_33_1 h.outside e.sylow e.exclusion e.odd inf_le_left
    · exact (le_inf h.outside.1.2 hinv).trans (I ⊓ normalizer (borel d.S L : Set G)).le_normalizer
    · rw [hB]
      exact k.normalizer_characteristic_two I h.component_le (h.normal e) h.component
        (fun _ hK => h.unique_component e h34 hK) (e.odd I h.outside) (h.core_central e) P
  have hMN : d.M ⊓ I ≤ I ⊓ normalizer (borel d.S L : Set G) := by
    apply le_inf inf_le_right
    have hMIY : d.M ⊓ I ≤ normalizer (d.Yplus : Set G) :=
      (e.normalizer_eq I h.outside).ge.trans inf_le_right
    have hMIL : d.M ⊓ I ≤ normalizer (L : Set G) :=
      inf_le_right.trans (h.normalizes_component e)
    have hMIA : d.M ⊓ I ≤ normalizer (componentPart d.Yplus L : Set G) := by
      change d.M ⊓ I ≤ normalizer (Stellmacher.twoResidualAmbient (d.Yplus ⊓ L) : Set G)
      rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
      exact (le_normalizer_inf hMIY hMIL).trans
        (normalizer_le_normalizer_characteristic_image _ (pResidual 2 (d.Yplus ⊓ L : Subgroup G)))
    have hMISL : d.M ⊓ I ≤ normalizer (d.S ⊓ L : Subgroup G) := by
      rw [← hcore, htheta]
      exact hMIA.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (componentPart d.Yplus L)))
    exact le_normalizer_inf hMIL (hMISL.trans (normalizer ((d.S ⊓ L : Subgroup G) : Set G)).le_normalizer)
  have himage : ((borel d.S L).subgroupOf L).map (projectiveMap c) =
      normalizer (P : Set PSL(3,c.F)) := by
    rw [hB, projectivePreimage_image]
  exact ⟨{
    invariant := hinv
    characteristic_two := hchar
    residual_le := hAB
    residual_generated := hgen
    theta_core := hcore
    theta_quotient := hquot
    normalizer_eq := le_antisymm hNM hMN
    P := P
    sylow_image := hP
    borel_image := himage
    theta_image := (theta_projective_image c (B := borel d.S L) inf_le_left).trans (congrArg theta himage)
  }⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel

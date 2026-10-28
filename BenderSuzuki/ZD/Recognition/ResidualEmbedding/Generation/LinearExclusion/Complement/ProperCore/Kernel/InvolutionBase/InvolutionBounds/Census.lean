module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.Distinguished
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.Reduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Geometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Degree
public import Theory.GroupTheory.ConjugacyOrderCensus
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The involution orbit in the linear centralizer closure

Write `q = 2^n`, `A = ⟨Z ∩ M⟩`, `L = residualGenerated M z t`,
`D = residualPairStabilizer M t`, `J = C_G(L)` and `R = ⟨Jᴹ⟩`.
All normality and conjugacy in the census are relative to M.

The permitted centralizer-closure collapse gives `N_M(J) = N_M(L)`.
Since J has order two, D fixes its nonidentity element. The genuine PSL₂
Borel localization `C_V(J) ≤ AJ`, together with the permitted supplement
`M = DV`, then gives `N_M(J) = AD`. The odd order of `D ∩ L` separates
A from D. Thus this normalizer has order `q |D|`; the proved coset-degree
formula gives `|M| = q³ |D|` and hence exactly q² conjugates.

These conjugates lie in the literal normal closure R and avoid the normal
subgroup A. Their disjoint union with A injects into the square-one elements
of R, including identity, giving the lower bound `q² + q` used by
`linear_involutionBase_of_torus_section_and_involution_bounds`. We use only
`A ≤ [R,K]` from the permitted section premises. No involution fusion,
abelian base, or identification with the source's intermediate R₁ is assumed.
The source assembly retains discharge of the collapse, supplement and section
premises; this module proves their conditional census consequence.

Source: GLS, Volume 4, Chapter 2, Lemma 15.2(c,d,f,h) and the counting
paragraphs of Lemma 15.6, `refs/KGroup/GLS4/Chapter2.tex`, lines 2703–2745.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory

private theorem card_two_centralizer_facts
    {H : Type*} [Group H] (J : Subgroup H) (hJ : Nat.card J = 2)
    {u : H} (hu : u ∈ J) (hu1 : u ≠ 1) :
    u ^ 2 = 1 ∧ centralizer ({u} : Set H) = centralizer (J : Set H) ∧
      normalizer (J : Set H) = centralizer (J : Set H) := by
  obtain ⟨v, _, hv⟩ := (Nat.card_eq_two_iff' (1 : J)).mp hJ
  have hchoices : ∀ j ∈ J, j = 1 ∨ j = u := by
    intro j hj
    by_cases hj1 : j = 1
    · exact Or.inl hj1
    · exact Or.inr (congrArg Subtype.val ((hv ⟨j, hj⟩
        (fun he => hj1 (congrArg Subtype.val he))).trans
        (hv ⟨u, hu⟩ (fun he => hu1 (congrArg Subtype.val he))).symm))
  have hC : centralizer ({u} : Set H) = centralizer (J : Set H) := by
    apply le_antisymm
    · intro x hx j hj
      rcases hchoices j hj with rfl | rfl
      · simp
      · exact (mem_centralizer_singleton_iff.mp hx).symm
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx u hu).symm
  refine ⟨congrArg Subtype.val (hJ ▸ pow_card_eq_one' (x := (⟨u, hu⟩ : J))), hC, ?_⟩
  apply le_antisymm _ (Subgroup.centralizer_le_normalizer _)
  intro x hx
  rw [← hC]
  have hxu : x * u * x⁻¹ ∈ J := (mem_normalizer_iff.mp hx u).mp hu
  have hne : x * u * x⁻¹ ≠ 1 := by
    intro he
    exact hu1 ((MulAut.conj x).injective (he.trans (map_one (MulAut.conj x)).symm))
  exact mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp ((hchoices _ hxu).resolve_left hne))

private theorem centralizer_eq_sup_of_supplement
    {H : Type*} [Group H] (V A D J : Subgroup H) [V.Normal] [A.Normal]
    (hDV : D ⊔ V = ⊤) (hJD : J ≤ D)
    (hAC : A ≤ centralizer (J : Set H)) (hDC : D ≤ centralizer (J : Set H))
    (hlocal : V ⊓ centralizer (J : Set H) ≤ A ⊔ J) :
    centralizer (J : Set H) = A ⊔ D := by
  apply le_antisymm _ (sup_le hAC hDC)
  intro x hx
  have hxDV : x ∈ D ⊔ V := hDV.symm ▸ mem_top x
  obtain ⟨d, hd, v, hv, rfl⟩ := mem_sup_of_normal_right.mp hxDV
  have hvC : v ∈ centralizer (J : Set H) := by
    simpa only [inv_mul_cancel_left] using
      (centralizer (J : Set H)).mul_mem ((centralizer (J : Set H)).inv_mem (hDC hd)) hx
  exact (A ⊔ D).mul_mem ((show D ≤ A ⊔ D from le_sup_right) hd)
    ((sup_le le_sup_left (hJD.trans le_sup_right)) (hlocal ⟨hv, hvC⟩))

variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem distinguished_disjoint_pair_of_squares
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hAsq : ∀ a ∈ (closure (Z ∩ (M : Set G))).subgroupOf M, a ^ 2 = 1) :
    Disjoint ((closure (Z ∩ (M : Set G))).subgroupOf M)
      ((residualPairStabilizer M t).subgroupOf M) := by
  apply disjoint_def.mpr
  intro a ha hd
  let K := residualPairStabilizer M t ⊓ residualGenerated M z t
  let aK : K := ⟨a, hd, hAL ha⟩
  have haG2 : (a : G) ^ 2 = 1 := congrArg (fun x : M => (x : G)) (hAsq a ha)
  have ha2 : aK ^ 2 = 1 := Subtype.ext haG2
  have hodd : Odd (Nat.card K) := pair_inf_proper_residualGenerated_odd
    h r hz hzM ht htM hL
  have ho : orderOf aK = 1 := Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right
    (orderOf_dvd_natCard aK) (orderOf_dvd_of_pow_eq_one ha2)
  have haG1 : (a : G) = 1 := congrArg (fun x : K => (x : G)) (orderOf_eq_one_iff.mp ho)
  exact Subtype.ext haG1

/-- The normalizer of the literal order-two centralizer in M is `AD`, of
order `q |D|`. Localization comes from the permitted centralizer collapse;
the supplement and distinguished Borel geometry then determine its order. -/
public theorem linear_centralizer_normalizer_card_of_centralizerClosure_and_supplement
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hDV : (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t) :
    normalizer ((centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M) =
      (normalizer (residualGenerated M z t : Set G)).subgroupOf M ∧
    normalizer ((centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M) =
      (closure (Z ∩ (M : Set G))).subgroupOf M ⊔ (residualPairStabilizer M t).subgroupOf M ∧
    Nat.card (normalizer ((centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M)) =
      2 ^ n * Nat.card (residualPairStabilizer M t) := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let D := (residualPairStabilizer M t).subgroupOf M
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  let V := pCore 2 M
  let : A.Normal := distinguishedClosure_normal h.disconnected
  have hJcard : Nat.card J = 2 := linearCentralizer_subgroupOf_card h.disconnected hz hzM hJ
  obtain ⟨u, hu1, _⟩ := (Nat.card_eq_two_iff' (1 : J)).mp hJcard
  obtain ⟨_, _, hNC⟩ := card_two_centralizer_facts J hJcard u.property
    (fun he => hu1 (Subtype.ext he))
  have hJD : J ≤ D := fun _ hj => centralizer_residualGenerated_le_pairStabilizer
    h.disconnected hz hzM hj
  have hJV : J ≤ V := linearCentralizer_subgroupOf_le_twoCore hR
  obtain ⟨hAsq, hAc, hAcard⟩ := linear_distinguishedClosure_internal_facts
    h.disconnected r hz hzM ht htM hL hn e hAL
  have hAC : A ≤ centralizer (J : Set M) := by
    intro a ha j hj
    exact mem_centralizer_iff.mp (hAc ha) j (hJV hj)
  have hDC : D ≤ centralizer (J : Set M) := by
    rw [← hNC]
    apply le_normalizer_iff.mpr
    intro d hd j hj
    exact (mem_normalizer_iff.mp
      (normalizer_le_normalizer_centralizer (residualGenerated M z t) (hDN hd)) j).mp hj
  have hlocal := linear_involution_localization_of_centralizerClosure h.disconnected r
    hz hzM ht htM hL hn e hAL hJ hcollapse
  have hsup : centralizer (J : Set M) = A ⊔ D :=
    centralizer_eq_sup_of_supplement V A D J hDV hJD hAC hDC hlocal
  have hdis : Disjoint A D := distinguished_disjoint_pair_of_squares
    h.disconnected r hz hzM ht htM hL hAL hAsq
  have hDcard : Nat.card D = Nat.card (residualPairStabilizer M t) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hJM : centralizer (residualGenerated M z t : Set G) ≤ M :=
    (centralizer_residualGenerated_le_pairStabilizer h.disconnected hz hzM).trans inf_le_left
  have hNN : normalizer (centralizer (residualGenerated M z t : Set G) : Set G) =
      normalizer (residualGenerated M z t : Set G) :=
    le_antisymm (linear_centralizer_normalizer_le_of_centralizerClosure
      h.disconnected hz hzM hJ hcollapse)
      (normalizer_le_normalizer_centralizer (residualGenerated M z t))
  refine ⟨(subgroupOf_normalizer_eq hJM).symm.trans
    (congrArg (fun P : Subgroup G => P.subgroupOf M) hNN), hNC.trans hsup, ?_⟩
  change Nat.card (normalizer (J : Set M)) = _
  rw [hNC, hsup, card_sup_eq_mul_of_normalizes_of_disjoint A D le_normalizer_of_normal hdis,
    hAcard, hDcard]

/-- Every nonidentity element of the literal `J_M` has exactly `q²`
M-conjugates, all square-one elements of `R ∖ A_M`. No involution-fusion
premise or identification of R with the source normalizer R₁ is used. -/
public theorem linear_involution_conjugacy_census_of_centralizerClosure_and_supplement
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hDV : (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t)
    {u : M} (hu : u ∈ (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hu1 : u ≠ 1) :
    Nat.card (ConjClasses.mk u).carrier = (2 ^ n) ^ 2 ∧
      ∀ x ∈ (ConjClasses.mk u).carrier,
        x ∈ linearCentralizerClosure M z t ∧
        x ∉ (closure (Z ∩ (M : Set G))).subgroupOf M ∧ x ^ 2 = 1 := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  let R := linearCentralizerClosure M z t
  let : A.Normal := distinguishedClosure_normal h.disconnected
  let : R.Normal := normalClosure_normal
  have hJcard : Nat.card J = 2 := linearCentralizer_subgroupOf_card h.disconnected hz hzM hJ
  obtain ⟨hu2, hCu, hNJ⟩ := card_two_centralizer_facts J hJcard hu hu1
  have hNc := (linear_centralizer_normalizer_card_of_centralizerClosure_and_supplement
    h r hz hzM ht htM hL hn e hJ hR hAL hDN hDV hcollapse).2.2
  have hMcard := linear_stabilizer_card_of_centralizerClosure
    h r ha hz hzM ht htM hL hn e hAL hJ hcollapse
  have hc : Nat.card (centralizer ({u} : Set M)) =
      2 ^ n * Nat.card (residualPairStabilizer M t) := by
    rw [hCu, ← hNJ]
    exact hNc
  have horbit : Nat.card (ConjClasses.mk u).carrier = (2 ^ n) ^ 2 := by
    have hpos : 0 < 2 ^ n * Nat.card (residualPairStabilizer M t) :=
      Nat.mul_pos (pow_pos (by decide : 0 < 2) n) Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      Nat.card (ConjClasses.mk u).carrier * (2 ^ n * Nat.card (residualPairStabilizer M t)) =
          Nat.card M := hc ▸ ConjClasses.nat_card_carrier_mul_card_centralizer u
      _ = (2 ^ n) ^ 3 * Nat.card (residualPairStabilizer M t) := hMcard
      _ = (2 ^ n) ^ 2 * (2 ^ n * Nat.card (residualPairStabilizer M t)) := by ring
  have hAsq := (linear_distinguishedClosure_internal_facts h.disconnected r
    hz hzM ht htM hL hn e hAL).1
  have hdis := distinguished_disjoint_pair_of_squares h.disconnected r
    hz hzM ht htM hL hAL hAsq
  have huA : u ∉ A := fun huA => hu1 (disjoint_def.mp hdis huA
    (centralizer_residualGenerated_le_pairStabilizer h.disconnected hz hzM hu))
  refine ⟨horbit, ?_⟩
  intro x hx
  have hxconj : IsConj u x :=
    (ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mem_carrier_iff_mk_eq.mp hx)).symm
  obtain ⟨m, rfl⟩ := isConj_iff.mp hxconj
  refine ⟨(inferInstance : R.Normal).conj_mem u (subset_normalClosure hu) m, ?_, ?_⟩
  · intro hm
    exact huA ((mem_normalizer_iff.mp
      (show m ∈ normalizer (A : Set M) from le_normalizer_of_normal (mem_top m)) u).mpr hm)
  · change (MulAut.conj m u) ^ 2 = 1
    rw [← map_pow, hu2, map_one]

private theorem square_card_ge_of_conjugacy_class
    {H : Type*} [Group H] [Finite H] (A R : Subgroup H)
    (hAR : A ≤ R) (hAsq : ∀ a ∈ A, a ^ 2 = 1)
    (u : H) (hclass : ∀ x ∈ (ConjClasses.mk u).carrier,
      x ∈ R ∧ x ∉ A ∧ x ^ 2 = 1) :
    Nat.card (ConjClasses.mk u).carrier + Nat.card A ≤ Nat.card {x : R // x ^ 2 = 1} := by
  let f : (ConjClasses.mk u).carrier ⊕ A → {x : R // x ^ 2 = 1} :=
    Sum.elim
      (fun x => ⟨⟨x, (hclass x x.property).1⟩, Subtype.ext (hclass x x.property).2.2⟩)
      (fun a => ⟨⟨a, hAR a.property⟩, Subtype.ext (hAsq a a.property)⟩)
  have hf : Function.Injective f := by
    intro x y he
    have he' := congrArg (fun a : {x : R // x ^ 2 = 1} => (a.val : H)) he
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext he')
      | inr y => exact ((hclass x x.property).2.1 (he'.symm ▸ y.property)).elim
    | inr x =>
      cases y with
      | inl y => exact ((hclass y y.property).2.1 (he' ▸ x.property)).elim
      | inr y => exact congrArg Sum.inr (Subtype.ext he')
  simpa only [Nat.card_sum] using Nat.card_le_card_of_injective f hf

/-- The `q²` conjugates and the q elements of the distinguished closure
supply the exact square-one lower bound consumed by involution-base extraction.
The displayed containment is one of the permitted earlier section premises. -/
public theorem linear_square_one_census_of_centralizerClosure_and_section
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hDV : (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t)
    (hAB : (closure (Z ∩ (M : Set G))).subgroupOf M ≤ linearCommutatorKernel M z t) :
    (2 ^ n) ^ 2 + 2 ^ n ≤ Nat.card {x : linearCentralizerClosure M z t // x ^ 2 = 1} := by
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  have hJcard : Nat.card J = 2 := linearCentralizer_subgroupOf_card h.disconnected hz hzM hJ
  obtain ⟨u, hu1, _⟩ := (Nat.card_eq_two_iff' (1 : J)).mp hJcard
  obtain ⟨hcount, hclass⟩ := linear_involution_conjugacy_census_of_centralizerClosure_and_supplement
    h r ha hz hzM ht htM hL hn e hJ hR hAL hDN hDV hcollapse
    u.property (fun he => hu1 (Subtype.ext he))
  obtain ⟨hAsq, _, hAcard⟩ := linear_distinguishedClosure_internal_facts h.disconnected r
    hz hzM ht htM hL hn e hAL
  have hh := square_card_ge_of_conjugacy_class
    ((closure (Z ∩ (M : Set G))).subgroupOf M) (linearCentralizerClosure M z t)
    (hAB.trans linearCommutatorKernel_le_closure) hAsq u hclass
  simpa only [hcount, hAcard] using hh

end BenderSuzuki.ZD

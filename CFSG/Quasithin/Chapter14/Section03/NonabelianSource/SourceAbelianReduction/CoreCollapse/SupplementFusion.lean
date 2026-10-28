module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.SupplementSpan
public import Theory.GroupTheory.WeakClosureSetFusion

/-!
# Normalizer factorization and the three supplement conjugates

For the original supplement D and its abelian conjugate span X, every element
of N_G(X) lies in M and carries the marked point to a nonidentity vector of V.
The transitive L-action corrects it by l⁻¹ into H ∩ M, proving the literal
product N_G(X) = L N_{H ∩ M}(X) by witnesses in both directions.

Burnside set fusion replaces any ambient conjugator between members of the
weakly closed abelian span by an element of N_G(X). The product formula and
H-normality of D reduce this to L-conjugacy. A cyclic conjugate is determined
by its unique involution; the bijection with V minus the identity gives three.

The export retains exactly the context and explicit cyclicity hypothesis of
source_supplement_span_of_cyclic. The original 14.3.22 assembly still owns
cyclicity and the subsequent contradiction. Conjugation is x ↦ g * x * g⁻¹.

Source: Aschbacher--Smith, 14.3.22, printed p.998 (PDF p.1015).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

private theorem normalizer_product_of_rankTwo
    {T : Sylow 2 G} {L M : Subgroup G}
    (h : RankTwoHypothesis KnownSimple.IsKnownSimple T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (X : Subgroup G)
    (hLN : L ≤ normalizer (X : Set G)) (hNM : normalizer (X : Set G) ≤ M) :
    ∀ a : G, a ∈ normalizer (X : Set G) ↔
      ∃ l ∈ L, ∃ b ∈ F.H ⊓ M, b ∈ normalizer (X : Set G) ∧ a = l * b := by
  have hzcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp (show F.Vi 1 ≠ ⊥ by
    intro he; simp [he] at hzcard)
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  have hgen : F.Vi 1 = zpowers (z : G) := by
    have hh := congrArg (map (F.Vi 1).subtype) (zpowers_eq_top_of_prime_card hzcard hz)
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype,
      Subgroup.subtype_apply] using hh.symm
  intro a
  constructor
  · intro ha
    have haz : a * (z : G) * a⁻¹ ∈ rankTwoSeed T M :=
      (mem_normalizer_iff.mp (RankTwoHypothesis.M_normalizes_seed (hNM ha)) z).mp
        (F.le_seed 1 z.property)
    have haz1 : a * (z : G) * a⁻¹ ≠ 1 := by
      intro he
      apply hz1
      exact (MulAut.conj a).injective (he.trans (map_one _).symm)
    obtain ⟨l, hl, he⟩ := h.nonidentity_transitive z (a * (z : G) * a⁻¹)
      (F.le_seed 1 z.property) haz hz1 haz1
    have hbfix : MulAut.conj (l⁻¹ * a) (z : G) = z := by
      change (l⁻¹ * a) * (z : G) * (l⁻¹ * a)⁻¹ = z
      calc
        _ = l⁻¹ * (a * (z : G) * a⁻¹) * l := by group
        _ = l⁻¹ * (l * (z : G) * l⁻¹) * l := by rw [he]
        _ = z := by group
    refine ⟨l, hl, l⁻¹ * a, ⟨?_, M.mul_mem (M.inv_mem (h.L_le hl)) (hNM ha)⟩,
      (normalizer (X : Set G)).mul_mem ((normalizer (X : Set G)).inv_mem (hLN hl)) ha, ?_⟩
    · change l⁻¹ * a ∈ normalizer (F.Vi 1 : Set G)
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [hgen, MonoidHom.map_zpowers]
      exact congrArg zpowers hbfix
    · group
  · rintro ⟨l, hl, b, _, hb, rfl⟩
    exact (normalizer (X : Set G)).mul_mem (hLN hl) hb

private theorem family_eq_residual_orbit
    (T : Sylow 2 G) (D L H M : Subgroup G)
    (hDX : D ≤ supplementSpan D T)
    (hab : IsMulCommutative (supplementSpan D T))
    (hLN : L ≤ normalizer (supplementSpan D T : Set G))
    (hHD : H ≤ normalizer (D : Set G))
    (hproduct : ∀ a : G, a ∈ normalizer (supplementSpan D T : Set G) ↔
      ∃ l ∈ L, ∃ b ∈ H ⊓ M, b ∈ normalizer (supplementSpan D T : Set G) ∧ a = l * b) :
    tightConjugateFamily ⊤ D T = {B | ∃ l ∈ L, conjSubgroup D l = B} := by
  let X := supplementSpan D (T : Subgroup G)
  let := hab
  have hXT : X ≤ (T : Subgroup G) := conjugateSpanIn_le _ _
  have hnorm {B : Subgroup G} (hBX : B ≤ X) : X ≤ normalizer (B : Set G) :=
    ((le_centralizer X).trans (centralizer_le hBX)).trans (Subgroup.centralizer_le_normalizer _)
  ext B
  constructor
  · rintro ⟨hBT, a, _, rfl⟩
    obtain ⟨n, hn, he⟩ := T.weakly_closed_normalizer_controls_set_fusion X hXT
      (fun c hc => mem_normalizer_iff_map_conj_eq.mpr (conjugateSpanIn_weakly_closed c hc))
      (D : Set G) (conjSubgroup D a : Set G) (hnorm hDX)
      (hnorm (conjugate_le_conjugateSpanIn a hBT)) a rfl
    have heq : conjSubgroup D n = conjSubgroup D a := SetLike.coe_injective he
    obtain ⟨l, hl, b, hb, _, rfl⟩ := (hproduct n).mp hn
    refine ⟨l, hl, ?_⟩
    rw [← conjSubgroup_conjSubgroup,
      show conjSubgroup D b = D from mem_normalizer_iff_map_conj_eq.mp (hHD hb.1)] at heq
    exact heq
  · rintro ⟨l, hl, rfl⟩
    refine ⟨?_, l, mem_top _, rfl⟩
    exact (conjSubgroup_mono hDX l).trans
      ((mem_normalizer_iff_map_conj_eq.mp (hLN hl)).le.trans hXT)

private theorem cyclic_conjugates_eq_iff_involutions_eq
    (D : Subgroup G) [IsCyclic D] (z : G) (hzD : z ∈ D) (hz2 : orderOf z = 2)
    (hfix : centralizer ({z} : Set G) ≤ normalizer (D : Set G)) (a b : G) :
    conjSubgroup D a = conjSubgroup D b ↔ MulAut.conj a z = MulAut.conj b z := by
  constructor
  · intro he
    let A := conjSubgroup D a
    let : IsCyclic A := isCyclic_of_surjective _
      (D.equivMapOfInjective _ (MulAut.conj a).injective).surjective
    let x : A := ⟨MulAut.conj a z, mem_map_of_mem _ hzD⟩
    let y : A := ⟨MulAut.conj b z, by
      change MulAut.conj b z ∈ conjSubgroup D a
      rw [he]
      exact mem_map_of_mem (MulAut.conj b).toMonoidHom hzD⟩
    have hx : orderOf x = 2 := by
      rw [← orderOf_coe]
      exact ((MulAut.conj a).orderOf_eq z).trans hz2
    have hy : orderOf y = 2 := by
      rw [← orderOf_coe]
      exact ((MulAut.conj b).orderOf_eq z).trans hz2
    exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two hx hy)
  · intro he
    have hc : MulAut.conj (b⁻¹ * a) z = z := by
      change (b⁻¹ * a) * z * (b⁻¹ * a)⁻¹ = z
      calc
        _ = b⁻¹ * (a * z * a⁻¹) * b := by group
        _ = b⁻¹ * (b * z * b⁻¹) * b := by rw [show a*z*a⁻¹=b*z*b⁻¹ from he]
        _ = z := by group
    have hn : b⁻¹ * a ∈ normalizer (D : Set G) := hfix <|
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hc)
    have hh := congrArg (fun A => conjSubgroup A b)
      (show conjSubgroup D (b⁻¹ * a) = D from mem_normalizer_iff_map_conj_eq.mp hn)
    simpa only [conjSubgroup_conjSubgroup, mul_inv_cancel_left] using hh

private theorem residual_orbit_ncard_three
    {T : Sylow 2 G} {L M : Subgroup G}
    (h : RankTwoHypothesis KnownSimple.IsKnownSimple T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (D : Subgroup G) [IsCyclic D]
    (hZD : F.Vi 1 ≤ D) (hHD : F.H ≤ normalizer (D : Set G)) :
    {B | ∃ l ∈ L, conjSubgroup D l = B}.ncard = 3 := by
  classical
  have hzcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp (show F.Vi 1 ≠ ⊥ by
    intro he; simp [he] at hzcard)
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  have hgen : F.Vi 1 = zpowers (z : G) := by
    have hh := congrArg (map (F.Vi 1).subtype) (zpowers_eq_top_of_prime_card hzcard hz)
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype,
      Subgroup.subtype_apply] using hh.symm
  have hz2 : orderOf (z : G) = 2 := by rw [← Nat.card_zpowers, ← hgen, hzcard]
  have hfix : centralizer ({(z : G)} : Set G) ≤ normalizer (D : Set G) := by
    apply le_trans _ hHD
    change centralizer ({(z : G)} : Set G) ≤ normalizer (F.Vi 1 : Set G)
    calc
      _ ≤ normalizer (zpowers (z : G) : Set G) :=
        (normalizer_zpowers_eq_centralizer_of_order_two (z : G) hz2).symm.le
      _ = normalizer (F.Vi 1 : Set G) :=
        congrArg (fun A : Subgroup G => normalizer (A : Set G)) hgen.symm
  let V := rankTwoSeed T M
  let S : Set V := {1}ᶜ
  have hmove (v : V) (hv : v ∈ S) : ∃ l ∈ L, MulAut.conj l (z : G) = v :=
    h.nonidentity_transitive z v (F.le_seed 1 z.property) v.property hz1
      (fun he => hv (Subtype.ext he))
  let f (v : V) (hv : v ∈ S) := conjSubgroup D (hmove v hv).choose
  have hf (v : V) (hv : v ∈ S) : (hmove v hv).choose ∈ L ∧
      MulAut.conj (hmove v hv).choose (z : G) = v := (hmove v hv).choose_spec
  have hcount : S.ncard = {B | ∃ l ∈ L, conjSubgroup D l = B}.ncard := by
    apply Set.ncard_congr f
    · intro v hv
      exact ⟨_, (hf v hv).1, rfl⟩
    · intro v w hv hw he
      apply Subtype.ext
      exact (hf v hv).2.symm.trans
        (((cyclic_conjugates_eq_iff_involutions_eq D z (hZD z.property) hz2 hfix _ _).mp he).trans
          (hf w hw).2)
    · rintro B ⟨l, hl, rfl⟩
      let v : V := ⟨MulAut.conj l z,
        (mem_normalizer_iff.mp (h.L_normalizes_seed hl) z).mp (F.le_seed 1 z.property)⟩
      have hv : v ∈ S := by
        intro he
        apply hz1
        exact (MulAut.conj l).injective ((congrArg Subtype.val he).trans (map_one _).symm)
      refine ⟨v, hv, ?_⟩
      exact (cyclic_conjugates_eq_iff_involutions_eq D z (hZD z.property) hz2 hfix _ _).mpr
        (hf v hv).2
  rw [← hcount]
  change (({1} : Set V)ᶜ).ncard = 3
  rw [Set.ncard_compl, show Nat.card V = 4 from rankTwoSeed_card h, Set.ncard_singleton]

/-- The source normalizer product, exact L-fusion, and three-conjugate count,
conditional only on the original explicit cyclicity premise. -/
theorem source_supplement_fusion_of_cyclic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hproper : F.Vi 1 < F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G))
    (hcyclic : IsCyclic (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) : Subgroup G)) :
    let D := F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)
    let X := supplementSpan D (T : Subgroup G)
    (∀ a : G, a ∈ normalizer (X : Set G) ↔
      ∃ l ∈ sourceResidual M Mc, ∃ b ∈ F.H ⊓ M,
        b ∈ normalizer (X : Set G) ∧ a = l * b) ∧
    tightConjugateFamily ⊤ D T =
      {B | ∃ l ∈ sourceResidual M Mc, conjSubgroup D l = B} ∧
    (tightConjugateFamily ⊤ D T).ncard = 3 := by
  intro D X
  let := hcyclic
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨_, _, hab, _, _, _, _, hJN, hNM⟩ := source_supplement_span_of_cyclic
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hproper hcyclic
  have hLN : sourceResidual M Mc ≤ normalizer (X : Set G) := le_sup_left.trans hJN
  have hproduct := normalizer_product_of_rankTwo h F X hLN hNM
  have hHD : F.H ≤ normalizer (D : Set G) := by
    apply le_trans _ inf_normalizer_le_normalizer_inf
    apply le_inf
    · exact F.H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
    · exact (le_normalizer_conjugateSpanBy (rankTwoSeed T M) F.H).trans
        (normalizer_le_normalizer_centralizer F.U)
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
    have hh := pCoreIn_le_sylow F.H (T.subtype hTH)
    change F.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hDT : D ≤ (T : Subgroup G) := inf_le_left.trans hQT
  have hf := family_eq_residual_orbit T D (sourceResidual M Mc) F.H M
    (le_conjugateSpanIn hDT) hab hLN hHD hproduct
  refine ⟨hproduct, hf, ?_⟩
  rw [hf]
  exact residual_orbit_ncard_three h F D hproper.le hHD

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse

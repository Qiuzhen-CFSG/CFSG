module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.OddRank
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverUnitaryBinary
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverSingerLinear

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Complete

/-!
# The complete split-prime source for the ordinary-root Cartan extension

`alternatives_source` supplies the proved normal split-prime specialization
of A.3.18 to the original `alternatives_of_normal_split_prime` consumer.
The actual Cartan element generates K_Z ⊔ ⟨a⟩; its inherited SQTK hypothesis,
relative C-component membership, and literal two-core quotient discharge
all inputs. No earlier-classification parameter remains in this application.

The earlier partial reductions are retained as public intermediate APIs.
The completed application includes the full central cover, signed congruence,
marked outer diagonal action, exact residual and disjoint complement,
Singer centralizer order, and conjugacy of every outside cubic subgroup.

Source: Aschbacher–Smith A.3.18, printed pp.51–53, and 4.3.6, printed p.615.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
open ChapterA.Section03.OddPrime.SourceModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

/-- Apply the proved source reduction to the literal Cartan extension. The
second branch remains an obligation of the normal split-prime source owner. -/
theorem alternatives_or_source_remaining
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        NormalSplitPrime.Remaining p (KZ.subgroupOf (KZ ⊔ zpowers a))) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.alternatives_or_remaining hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen

/-- Apply the complete catalogue reduction to the same Cartan extension.
Only the even-characteristic actors and the classical or Mathieu cubic covers
remain; their source alternatives are still owned by the split-prime proof. -/
theorem alternatives_or_even_or_cubic_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      let K := KZ.subgroupOf (KZ ⊔ zpowers a)
      Alternatives p K ∨
        (Nat.Coprime p (Nat.card (center (NormalSplitPrime.twoCoreComponent K))) ∧
          NormalSplitPrime.EvenLieModel ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K))) ∨
        (p = 3 ∧ Nat.card (center (NormalSplitPrime.twoCoreComponent K)) = 3 ∧
          ((∃ (unitary : Bool) (q : ℕ),
            Chapter1.Section02.LocalModels.CoverParameter unitary q ∧
            Chapter1.Section02.LocalModels.IsSLSign (NormalSplitPrime.twoCoreComponent K)
              unitary 3 q) ∨
            Chapter1.Section02.LocalModels.IsM22Cover (NormalSplitPrime.twoCoreComponent K))) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.alternatives_or_even_or_cubic_center hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen

/-- The proved odd-prime ternary rows give the full original alternative on
the literal Cartan extension. The marking is on the original intrinsic quotient. -/
theorem alternatives_of_odd_ternary_secondary
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ)
    (hm : NormalSplitPrime.OddTernaryModel (KZ ⧸ pCore 2 KZ) p) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.alternatives_of_odd_ternary_model hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK (hm.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))) a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen

/-- The binary source construction suffices for the exact original alternative
on the selected extension, without a universal classification callback. -/
theorem alternatives_of_binary_secondary
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ)
    (hm : NormalSplitPrime.BinaryModel (KZ ⧸ pCore 2 KZ) p) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) := by
  obtain ⟨a, haN, ha, haK, halt⟩ := alternatives_or_source_remaining m hn h KZ hK hcomp
    hquasi hnormal p hp ho hd hrank
  refine ⟨a, haN, ha, haK, ?_⟩
  rcases halt with h | h
  · exact h
  · let e : KZ.subgroupOf (KZ ⊔ zpowers a) ≃* KZ := subgroupOfEquivOfLe le_sup_left
    exact (h.nonbinary (hm.of_mulEquiv
      (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)))).elim

/-- Apply the fixed-subfield, mixed-linear and Mathieu-cover source increment
to the actual Cartan extension. The surviving cubic cases are odd-degree PSU₃
and genuine classical cubic covers; noncubic even-field actors remain explicit. -/
theorem alternatives_or_actor_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        NormalSplitPrime.ActorRemainder p (KZ.subgroupOf (KZ ⊔ zpowers a))) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.alternatives_or_actor_remainder hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen


/-- Apply the full symplectic and noncubic linear/G₂ exclusions to the original
Cartan extension. Every retained field or covering case is still an explicit
obligation of the normal split-prime source theorem. -/
theorem alternatives_or_reduced_actor_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        NormalSplitPrime.ReducedActorRemainder p (KZ.subgroupOf (KZ ⊔ zpowers a))) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.alternatives_or_reduced_actor_remainder hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen


/-- The actual Cartan extension satisfies the source alternatives or one of
the still-owned exceptional field and classical-cover obligations. Every
unitary actor, including mixed cubic actors, has been discharged. -/
theorem alternatives_or_exceptional_or_cover_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        NormalSplitPrime.ExceptionalOrCoverRemainder p (KZ.subgroupOf (KZ ⊔ zpowers a))) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.alternatives_or_exceptional_or_cover hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen


/-- The original Cartan actor cannot act inner on a linear cubic cover.
The remaining inner unitary case retains its genuine order-nine implementer
and nontrivial central cube; exceptional field and outer cover cases remain. -/
theorem alternatives_or_cover_action_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        NormalSplitPrime.CoverActionRemainder p (KZ.subgroupOf (KZ ⊔ zpowers a))
          ⟨a, (le_sup_right : zpowers a ≤ KZ ⊔ zpowers a) (mem_zpowers a)⟩) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.alternatives_or_cover_action hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen


/-- The original Cartan actor acts outer on every remaining central cubic
cover. Both linear and unitary inner actors are excluded using the actual
implementer's fixed torus. Exceptional field and outer cover cases remain. -/
theorem alternatives_or_outer_cover_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        NormalSplitPrime.OuterCoverRemainder p (KZ.subgroupOf (KZ ⊔ zpowers a))
          ⟨a, (le_sup_right : zpowers a ≤ KZ ⊔ zpowers a) (mem_zpowers a)⟩) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.alternatives_or_outer_cover hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen
/-- Apply the exceptional fixed split-torus exclusions to the literal
Cartan extension. The remaining exceptional primes avoid q - 1; the outer
central cubic-cover branch keeps its original actor and quotient maps. -/
theorem alternatives_or_nonsplit_or_cover_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        NormalSplitPrime.NonsplitOrCoverRemainder p (KZ.subgroupOf (KZ ⊔ zpowers a))
          ⟨a, (le_sup_right : zpowers a ≤ KZ ⊔ zpowers a) (mem_zpowers a)⟩) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.alternatives_or_nonsplit_or_cover hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen

/-- Apply the fixed quadratic triality subsystem to the original Cartan
extension. The remaining triality primes divide the original field exponent
and a third or sixth cyclotomic factor; all literal quotient maps are retained. -/
theorem alternatives_or_refined_nonsplit_or_cover_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        NormalSplitPrime.RefinedNonsplitOrCoverRemainder p (KZ.subgroupOf (KZ ⊔ zpowers a))
          ⟨a, (le_sup_right : zpowers a ≤ KZ ⊔ zpowers a) (mem_zpowers a)⟩) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.alternatives_or_refined_nonsplit_or_cover hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen


/-- The fixed-subfield construction excludes every remaining triality actor
on the literal Cartan extension. Nonsplit Ree actors and the complete outer
central cubic-cover clauses remain explicit source obligations. -/
theorem alternatives_or_ree_or_cover_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        NormalSplitPrime.ReeOrCoverRemainder p (KZ.subgroupOf (KZ ⊔ zpowers a))
          ⟨a, (le_sup_right : zpowers a ≤ KZ ⊔ zpowers a) (mem_zpowers a)⟩) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.alternatives_or_ree_or_cover hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen


/-- The actual Cartan extension has no remaining exceptional field actors.
Only the complete outer central cubic-cover clauses remain to be proved. -/
theorem alternatives_or_outer_cubic_cover_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        (p = 3 ∧ NormalSplitPrime.OuterCubicCoverActor
          (NormalSplitPrime.twoCoreComponent (KZ.subgroupOf (KZ ⊔ zpowers a)))
          (QuotientGroup.mk' (pCore 2 ↥(KZ ⊔ zpowers a))
            ⟨a, (le_sup_right : zpowers a ≤ KZ ⊔ zpowers a) (mem_zpowers a)⟩))) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.alternatives_or_outer_cubic_cover hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen


/-- The original odd-rank Cartan prime is necessarily three. All exceptional
field rows are excluded using fixed subgroups of the same actual actor. -/
theorem prime_eq_three_of_odd_rank_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) : p = 3 := by
  obtain ⟨a, _, ha, haK, halt | hcover⟩ :=
    alternatives_or_outer_cubic_cover_source m hn h KZ hK hcomp hquasi hnormal p hp ho hd hrank
  · let E := KZ ⊔ zpowers a
    let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
    have ha' : orderOf a' = p :=
      (orderOf_injective E.subtype E.subtype_injective a').symm.trans ha
    rcases (NormalSplitPrime.alternatives_iff a' ha' haK).mp halt with hp | hc
    · exact hp.1
    · exact hc.1
  · exact hcover.1

/-- The literal Cartan extension retains its central cubic cover in the
source star quotient. Its residual product and disjoint complement are
proved, and every odd-prime cover row has the required matrix marking.
Binary diagonal analysis, the Singer centralizer and conjugacy remain. -/
theorem alternatives_or_marked_star_cover_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        (p = 3 ∧ NormalSplitPrime.CoverDiagonal.MarkedStarCover
          (KZ.subgroupOf (KZ ⊔ zpowers a))
          ⟨a, (le_sup_right : zpowers a ≤ KZ ⊔ zpowers a) (mem_zpowers a)⟩)) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.CoverDiagonal.alternatives_or_marked_star_cover hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen

/-- The original star cover has the precise signed parameter, residual
product and disjoint complement. All linear cover actions are diagonal;
binary unitary actions and the Singer/conjugacy clauses remain. -/
theorem alternatives_or_linear_marked_star_cover_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        (p = 3 ∧ NormalSplitPrime.CoverBinary.MarkedStarCover
          (KZ.subgroupOf (KZ ⊔ zpowers a))
          ⟨a, (le_sup_right : zpowers a ≤ KZ ⊔ zpowers a) (mem_zpowers a)⟩)) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.CoverBinary.alternatives_or_marked_star_cover hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen


/-- The literal Cartan extension retains the complete central cover and
an actual diagonal marking for either sign. Its residual product, disjoint
complement and signed parameter are proved; Singer centralizer and fusion
remain the final source obligations. -/
theorem alternatives_or_diagonal_star_cover_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        (p = 3 ∧ NormalSplitPrime.CoverUnitaryBinary.MarkedStarCover
          (KZ.subgroupOf (KZ ⊔ zpowers a))
          ⟨a, (le_sup_right : zpowers a ≤ KZ ⊔ zpowers a) (mem_zpowers a)⟩)) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.CoverUnitaryBinary.alternatives_or_marked_star_cover hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen


/-- The literal Cartan extension now satisfies the complete source alternatives
in every linear-cover row, including the exact Singer centralizer and fusion
of all outside cubics. Only the genuine unitary cover branch remains. -/
theorem alternatives_or_unitary_star_cover_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      (Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) ∨
        (p = 3 ∧ NormalSplitPrime.CoverSingerLinear.UnitaryStarCover
          (KZ.subgroupOf (KZ ⊔ zpowers a))
          ⟨a, (le_sup_right : zpowers a ≤ KZ ⊔ zpowers a) (mem_zpowers a)⟩)) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact NormalSplitPrime.CoverSingerLinear.alternatives_or_unitary_star_cover hsq
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hp ho hpK a' ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha)
    haK hgen

/-- The original Cartan extension satisfies A.3.18, with the earlier
normal split-prime classification premise fully discharged. -/
theorem alternatives_source
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      Alternatives p (KZ.subgroupOf (KZ ⊔ zpowers a)) :=
  alternatives_of_normal_split_prime m hn h KZ hK hcomp hquasi hnormal
    p hp ho hd hrank NormalSplitPrime.normal_split_prime

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF

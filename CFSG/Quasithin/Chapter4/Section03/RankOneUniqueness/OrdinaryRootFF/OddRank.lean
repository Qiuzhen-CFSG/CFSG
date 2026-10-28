module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.Action
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
public import Theory.SpecificGroups.SymplecticFour.RootTori

/-!
# The actual split prime extensions in the ordinary root argument

Embed the root torus through the original symplectic marking. Its faithful
action on the root separates it from KZ, which centralizes that root. For
each prime dividing 2ⁿ − 1, Cauchy's theorem gives an actual outside actor
of order p. The generated overgroup is SQTK, and KZ remains its normal
C-component with the original quasisimple two-core quotient.

This supplies the domain for the normal split-prime specialization of
A.3.18. Its source alternatives remain an explicit earlier theorem input;
the present module does not claim their classification.

Source: Aschbacher--Smith 4.3.6, printed pp.614--615, and A.3.18, pp.51--53.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
open Theory.SpecificGroups.SymplecticFour
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

def rootTorus : Subgroup G := (RootTori.torus (F := m.Field) 0).map m.modelEmbedding

theorem rootTorus_le_normalizer : rootTorus m ≤ m.rootNormalizer := by
  have hn := (map_mono (f := m.modelEmbedding) (RootTori.torus_le_normalizer (F := m.Field) 0)).trans
    (le_normalizer_map m.modelEmbedding)
  rwa [m.root_image] at hn

theorem rootTorus_card : Nat.card (rootTorus m) = 2 ^ n - 1 := by
  rw [rootTorus, card_map_of_injective m.modelEmbedding_injective,
    Nat.card_congr (RootTori.cyclicEquiv 0 m.card).toEquiv]
  exact Nat.card_zmod _

theorem rootTorus_inf_centralizer :
    rootTorus m ⊓ centralizer (m.root : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  rintro x ⟨⟨a, ha, rfl⟩, hc⟩
  have hac : a ∈ centralizer (RootSubgroup.group (F := m.Field) 0 : Set (Sp m.Field)) := by
    intro z hz
    apply m.modelEmbedding_injective
    simpa only [map_mul] using hc (m.modelEmbedding z)
      (m.root_image.le (mem_map_of_mem _ hz))
  have hbot := (RootTori.centralizer_inf_torus (F := m.Field) 0).le ⟨hac, ha⟩
  simpa only [mem_bot.mp hbot, map_one] using (⊥ : Subgroup G).one_mem

/-- A prime divisor of the Cartan order supplies a genuine outside element,
not merely a prime-order class in an automorphism quotient. -/
theorem exists_outside_prime_actor (KZ : Subgroup G)
    (hK : KZ ≤ centralizer (m.root : Set G)) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (rootTorus m) := Finite.of_equiv (RootTori.torus (F := m.Field) 0)
    ((RootTori.torus (F := m.Field) 0).equivMapOfInjective
      m.modelEmbedding m.modelEmbedding_injective).toEquiv
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := rootTorus m) p
    (by rwa [rootTorus_card m])
  refine ⟨a, rootTorus_le_normalizer m a.property, ?_, ?_⟩
  · simpa only [orderOf_submonoid] using ha
  · intro hk
    have h1 : (a : G) = 1 := mem_bot.mp
      ((rootTorus_inf_centralizer m).le ⟨a.property, hK hk⟩)
    have ha1 : a = 1 := Subtype.ext h1
    rw [ha1, orderOf_one] at ha
    exact hp.ne_one ha.symm

/-- The C-component condition is inherited through the normal root centralizer
and then restricted to the literal prime extension. -/
theorem secondary_cComponent_in_extension (KZ E : Subgroup G)
    (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hKE : KZ ≤ E) (hEN : E ≤ m.rootNormalizer) :
    (KZ.subgroupOf E).IsCComponent := by
  let C := centralizer (m.root : Set G)
  have hCN : C ≤ m.rootNormalizer := Subgroup.centralizer_le_normalizer _
  have hcc : (C.subgroupOf m.rootNormalizer).Normal :=
    normal_subgroupOf_centralizer_normalizer (m.root : Set G)
  have hres := hcomp.map_equiv (subgroupOfEquivOfLe hCN).symm
  have he : (KZ.subgroupOf C).map (subgroupOfEquivOfLe hCN).symm.toMonoidHom =
      (KZ.subgroupOf m.rootNormalizer).subgroupOf (C.subgroupOf m.rootNormalizer) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hx
      exact ⟨⟨x, x.property⟩, hx, rfl⟩
  rw [he] at hres
  have hm := hres.map_subtype hcc.isSubnormal
  rw [map_subgroupOf_eq_of_le (show KZ.subgroupOf m.rootNormalizer ≤
    C.subgroupOf m.rootNormalizer from fun _ hk => hK hk)] at hm
  exact hm.subgroupOf_of_le hKE hEN

/-- Apply a normal split-prime A.3.18 theorem to an actual Cartan extension.
The earlier theorem is an explicit obligation, not a source assertion here. -/
theorem alternatives_of_normal_split_prime
    [Finite G] (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hrank : 1 < primeRank p KZ)
    (earlier : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK KnownSimple.IsKnownSimple H → ∀ (K : Subgroup H), K.Normal →
      K.IsCComponent → IsQuasisimple (K ⧸ pCore 2 K) →
      ∀ (p : ℕ), p.Prime → Odd p → 1 < primeRank p K →
      ∀ a : H, orderOf a = p → a ∉ K → K ⊔ zpowers a = ⊤ →
      ChapterA.Section03.OddPrime.SourceModels.Alternatives p K) :
    ∃ a : G, a ∈ m.rootNormalizer ∧ orderOf a = p ∧ a ∉ KZ ∧
      ChapterA.Section03.OddPrime.SourceModels.Alternatives p
        (KZ.subgroupOf (KZ ⊔ zpowers a)) := by
  obtain ⟨a, haN, ha, haK⟩ := exists_outside_prime_actor m KZ hK hp hd
  let E := KZ ⊔ zpowers a
  have hEN : E ≤ m.rootNormalizer := sup_le
    (hK.trans (Subgroup.centralizer_le_normalizer _)) (zpowers_le.mpr haN)
  let K := KZ.subgroupOf E
  let e : K ≃* KZ := subgroupOfEquivOfLe (show KZ ≤ E from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hEN.trans hnormal)
  let := hquasi
  have hq : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hEN)).mp
      ((h.simpleQTKE.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)).subgroup
        (E.subgroupOf m.rootNormalizer))
  have hpK : 1 < primeRank p K := by
    rwa [primeRank_congr p e]
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  have hgen : K ⊔ zpowers a' = ⊤ := by
    apply (map_injective E.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  refine ⟨a, haN, ha, haK, ?_⟩
  exact earlier E hsq K inferInstance
    (secondary_cComponent_in_extension m KZ E hK hcomp le_sup_left hEN)
    hq p hp ho hpK a'
    ((orderOf_injective E.subtype E.subtype_injective a').symm.trans ha) haK hgen

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF

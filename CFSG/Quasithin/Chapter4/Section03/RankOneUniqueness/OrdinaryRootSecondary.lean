module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootSecondary.Model
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootSecondary.Selection
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation

/-!
# The ordinary secondary root component

The root centralizer is normal in the root normalizer. The original 1.2.1
component-layer generation theorem, with its A/C inputs discharged, places
the simple Levi in that layer. The faithful scalar torus supplies an external
odd prime element centralizing the Levi. The rank-two obstruction selects one
component and proves its normality in the root normalizer, retaining the
possible two-component orbit in the argument of 1.2.2.

The Levi normally generates the actual point residual, so the selected
component contains the literal second subgroup. Its binary Levi survives the
two-core quotient and excludes the odd-SL₂ alternatives. The result retains
all ambient inclusions, relative component membership, and normal generation.
The terminal application leaves the earlier root-core and later FF-module
premises explicit; it does not assert the unconditional theorem 4.3.6.

Source: Aschbacher--Smith 1.2.1--2 and 4.3.6, printed pp.504--505, 614--615.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

namespace OrdinaryRootSecondary

private theorem quotient_sqtk {X : Type*} [Group X] [Finite X]
    (h : IsSQTK KnownSimple.IsKnownSimple X) :
    IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
  refine ⟨?_, h.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 X) pCore_isPGroup).trans
    (h.stronglyQuasithin p hp ho)

private theorem layer_eq_residual {X : Type*} [Group X] [Finite X]
    (h : IsSQTK KnownSimple.IsKnownSimple X) :
    cComponentLayer X = solvableResidual X :=
  Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
    (fun _Y _ _ hY hO =>
      ChapterA.Section03.SourceComponents.generation
        (fun Z _ _ => ChapterA.Section02.theoremA_knownSimple (G := Z))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Z _ _ => ChapterA.Section02.theoremC_knownSimple (G := Z))) hY hO)
    (quotient_sqtk h)

end OrdinaryRootSecondary

namespace OrdinarySymplecticMarking
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The actual secondary component of the root centralizer, with the ambient
normalizer and normal-generation conclusions of source 4.3.6. -/
theorem exists_secondary_component (m : OrdinarySymplecticMarking c n)
    (hn : 1 < n) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) :
    ∃ KZ : Subgroup G,
      KZ ≤ centralizer (m.root : Set G) ∧
      (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent ∧
      m.second ≤ KZ ∧ IsQuasisimple (KZ ⧸ pCore 2 KZ) ∧
      m.rootNormalizer ≤ normalizer (KZ : Set G) ∧
      conjugateSpanBy m.second KZ = KZ := by
  classical
  let N := m.rootNormalizer
  let C0 := centralizer (m.root : Set G)
  have hCN : C0 ≤ N := Subgroup.centralizer_le_normalizer _
  let C := C0.subgroupOf N
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_le_normalizer_centralizer m.root)
  let S0 := m.leviEmbedding.range
  have hS0C : S0 ≤ C0 :=
    (m.leviEmbedding_range_le_second hn).trans (m.second_le_rootCentralizer hn)
  have hS0N := hS0C.trans hCN
  let S := S0.subgroupOf N
  let eS : Matrix.SpecialLinearGroup (Fin 2) m.Field ≃* S :=
    (MonoidHom.ofInjective m.leviEmbedding_injective).trans
      (subgroupOfEquivOfLe hS0N).symm
  let := m.levi_simple hn
  let := m.levi_perfect hn
  let : IsSimpleGroup S := eS.symm.isSimpleGroup
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective (f := eS.toMonoidHom) eS.surjective
  have hSC : S ≤ C := comap_mono hS0C
  have hN : IsSQTK KnownSimple.IsKnownSimple N :=
    hG.twoLocal_sqtk (m.rootNormalizer_twoLocal hn)
  have hC := hN.subgroup C
  have hSlayer : S.subgroupOf C ≤ cComponentLayer C := by
    let e := subgroupOfEquivOfLe hSC
    let : Group.IsPerfect (S.subgroupOf C) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    rw [OrdinaryRootSecondary.layer_eq_residual hC]
    exact le_solvableResidual_of_isPerfect _
  have hq : 2 < 2 ^ n :=
    (show 2 = 2 ^ 1 by decide).trans_lt (Nat.pow_lt_pow_right (by decide) hn)
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (by omega : 2 ^ n - 1 ≠ 1)
  let : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (2 ^ n - 1) := by
    rw [Nat.odd_iff]
    have hmod := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : n ≠ 0))
    omega
  have hpo : Odd p := hodd.of_dvd_nat hd
  have hdc : p ∣ Nat.card m.cartan := by
    rw [Nat.card_congr m.cartanEquiv.toEquiv]
    change p ∣ Nat.card (ZMod (2 ^ n - 1))
    rw [Nat.card_zmod]
    exact hd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hdc
  let yN : N := ⟨y, m.cartan_le_rootNormalizer y.property⟩
  have hyN : orderOf yN = p := by
    rw [← orderOf_injective N.subtype N.subtype_injective yN]
    exact (orderOf_injective m.cartan.subtype m.cartan.subtype_injective y).trans hy
  have hyC : yN ∉ C := by
    intro hyC
    have hy1 : (y : G) = 1 := mem_bot.mp (m.cartan_faithful ▸ ⟨y.property, hyC⟩)
    have hy1' : y = 1 := Subtype.ext hy1
    rw [hy1', orderOf_one] at hy
    exact hp.ne_one hy.symm
  have hyS : yN ∈ centralizer (S : Set N) := by
    intro s hs
    apply Subtype.ext
    exact m.cartan_centralizes_levi y.property s.val hs
  have hdS : p ∣ Nat.card S := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hS0N).toEquiv]
    exact m.scalar_prime_dvd_levi hd
  obtain ⟨K, hKC, hK, hSK, hKN⟩ :=
    OrdinaryRootSecondary.normal_component_of_external_scalar hpo C S hSC hSlayer hdS
      (hN.stronglyQuasithin p hp hpo) yN hyN hyC hyS
      (fun B hB => Chapter1.Section02.proposition_1_2_1_three_orbit_source
        (OrdinaryRootSecondary.quotient_sqtk hN) hB)
  let KZ := K.map N.subtype
  have hKZC : KZ ≤ C0 := by
    rintro x ⟨k, hk, rfl⟩
    exact hKC hk
  have hnormal : N ≤ normalizer (KZ : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact mem_map.mpr ⟨⟨g * k * g⁻¹, N.mul_mem (N.mul_mem hg k.property) (N.inv_mem hg)⟩,
      hKN.conj_mem k hk ⟨g, hg⟩, rfl⟩
  have hS0KZ : S0 ≤ KZ := by
    have hm := map_mono (f := N.subtype) hSK
    change (S0.subgroupOf N).map N.subtype ≤ KZ at hm
    rwa [map_subgroupOf_eq_of_le hS0N] at hm
  have hsecond : m.second ≤ KZ := by
    rw [← m.levi_generates_second hn]
    exact conjugateSpanBy_le hS0KZ
      (((m.second_le_rootCentralizer hn).trans hCN).trans hnormal)
  let eC : C ≃* C0 := subgroupOfEquivOfLe hCN
  have hcomp : (KZ.subgroupOf C0).IsCComponent := by
    have hh := hK.map_equiv eC
    have he : (K.subgroupOf C).map eC.toMonoidHom = KZ.subgroupOf C0 := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact mem_map.mpr ⟨k.val, hk, rfl⟩
      · rintro ⟨k, hk, he⟩
        exact mem_map.mpr ⟨⟨k, hKC hk⟩, hk, Subtype.ext he⟩
    rwa [he] at hh
  have hC0 : IsSQTK KnownSimple.IsKnownSimple C0 :=
    (IsSQTK.equiv eC).mp hC
  exact ⟨KZ, hKZC, hcomp, hsecond,
    m.containing_component_quasisimple hn C0 KZ hKZC hsecond hcomp
      (OrdinaryRootSecondary.quotient_sqtk hC0),
    hnormal, m.second_generates_containing_component hn C0 KZ hKZC hsecond hcomp⟩

end OrdinarySymplecticMarking

/-- Conditional application of the constructed secondary component to the
ordinary terminal contradiction. The root-core and FF-module conclusions
remain explicit for their source owners to discharge. -/
theorem SourceConfiguration.ordinary_false_of_secondary_component
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n) (m : OrdinarySymplecticMarking c n)
    (hT : (T : Subgroup G) ≤ m.rootNormalizer)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (hFF : ∀ KZ : Subgroup G,
      KZ ≤ centralizer (m.root : Set G) →
      (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent →
      m.second ≤ KZ → IsQuasisimple (KZ ⧸ pCore 2 KZ) →
      m.rootNormalizer ≤ normalizer (KZ : Set G) →
      conjugateSpanBy m.second KZ = KZ →
      m.rootSpan = m.second.pCoreIn 2 ∧ KZ ≤ m.second ⊔ m.rootCore) : False := by
  obtain ⟨KZ, hKC, hcomp, hsecond, hquasi, hnormal, hgen⟩ :=
    m.exists_secondary_component hn h.simpleQTKE
  obtain ⟨hU, himage⟩ := hFF KZ hKC hcomp hsecond hquasi hnormal hgen
  exact c.ordinary_false_of_root_module D hn m KZ hT hseed hU hQ hgen himage hnormal

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness

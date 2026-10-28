module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.Contracts

/-!
# Excluding the alternating-five second centralizer

The marked component of a root-five normalizer has order sixty. Its source
vertex generation therefore supplies a vertex inside that normalizer.
Since the normalizer has only one factor of three in its order, Sylow
conjugacy makes every cubic subgroup there a source vertex. The other
five-normalizer has order one hundred and contains no cubic element.

Consequently a cubic element centralizing any five-element is in 3A, with
centralizer order 1080. This rules out the order-180 centralizer C₃ × A₅
in the second-class recognition alternative. The argument uses the actual
47.2 component embedding and vertex generation; no second-normalizer
conclusion or separation of the cubic classes is assumed.

The 47.2 contract and first-class centralizer calculation remain explicit
inputs, with their independent source producers retaining responsibility
for construction. The second-centralizer alternative is still unproved.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3, printed p.262,
the paragraph excluding C_G(Y) ≅ C₃ × A₅ using 47.2.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer
open FiveLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem component_card {E : Subgroup G} (W : RootFiveWitness D E) :
    Nat.card (fiveComponent E) = 60 := by
  have hf : Function.Injective ((normalizer (E : Set G)).subtype.comp
      W.equiv.symm.toMonoidHom) :=
    (normalizer (E : Set G)).subtype_injective.comp W.equiv.symm.injective
  rw [← W.component_factor, card_map_of_injective hf,
    Nat.card_congr (prodEquiv (⊥ : Subgroup (DihedralGroup 5))
      (⊤ : Subgroup (alternatingGroup (Fin 5)))).toEquiv,
    Nat.card_prod, card_bot, card_top, one_mul, nat_card_alternatingGroup]
  norm_num

private theorem root_normalizer_card {E : Subgroup G} (W : RootFiveWitness D E) :
    Nat.card (normalizer (E : Set G)) = 600 := by
  rw [Nat.card_congr W.equiv.toEquiv, Nat.card_prod,
    Nat.card_eq_fintype_card (α := DihedralGroup 5), DihedralGroup.card,
    nat_card_alternatingGroup]
  norm_num

private theorem exists_vertex_in_normalizer {E : Subgroup G} (W : RootFiveWitness D E) :
    ∃ A : Subgroup G, A ∈ MulAction.orbit (ConjAct G) D.X ∧
      A ≤ normalizer (E : Set G) := by
  by_contra h
  have hempty : {A : Subgroup G | A ∈ MulAction.orbit (ConjAct G) D.X ∧
      A ≤ normalizer (E : Set G)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro A hA
    exact h ⟨A, hA⟩
  have he : fiveComponent E = ⊥ := by
    rw [W.generation, orbitGenerated, hempty, sSup_empty]
  have hc := component_card W
  rw [he, card_bot] at hc
  omega

/-- The source generation marking, followed by Sylow conjugacy inside the
literal five-normalizer, identifies every cubic subgroup there as a vertex. -/
theorem vertex_of_le_root_normalizer {E A : Subgroup G} (W : RootFiveWitness D E)
    (hA : Nat.card A = 3) (hAN : A ≤ normalizer (E : Set G)) :
    A ∈ MulAction.orbit (ConjAct G) D.X := by
  obtain ⟨B, hB, hBN⟩ := exists_vertex_in_normalizer W
  let N := normalizer (E : Set G)
  have hc (T : Subgroup G) (hT : Nat.card T = 3) (hTN : T ≤ N) :
      Nat.card (T.subgroupOf N) = 3 ^ (Nat.card N).factorization 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv, hT, root_normalizer_card W]
    decide +kernel
  have hBc : Nat.card B = 3 := D.vertex_card ⟨B, hB⟩
  let P : Sylow 3 N := Sylow.ofCard (B.subgroupOf N) (hc B hBc hBN)
  let Q : Sylow 3 N := Sylow.ofCard (A.subgroupOf N) (hc A hA hAN)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N P Q
  have he := congrArg (fun R : Sylow 3 N => (R : Subgroup N)) hg
  change MulAut.conj g • B.subgroupOf N = A.subgroupOf N at he
  rw [conj_smul_subgroupOf hBN g] at he
  have hm := congrArg (fun R : Subgroup N => R.map N.subtype) he
  rw [map_subgroupOf_eq_of_le (conj_smul_le_of_le hBN g),
    map_subgroupOf_eq_of_le hAN] at hm
  exact hm ▸ MulAction.mem_orbit_of_mem_orbit (ConjAct.toConjAct (g : G)) hB

/-- Only the root-five family can have a cubic subgroup in its normalizer;
its source generation identifies that subgroup with a source vertex. -/
theorem threeA_of_normalizes_five {t : G} (F : SourceConclusion D t)
    {y : G} (hy : orderOf y = 3) {E : Subgroup G} (hE : Nat.card E = 5)
    (hyN : y ∈ normalizer (E : Set G)) : ThreeA D y := by
  rcases F.sylow.coverage E hE with hr | hz
  · obtain ⟨W⟩ := F.root E hr
    exact ⟨hy, vertex_of_le_root_normalizer W (by rw [Nat.card_zpowers, hy])
      (zpowers_le.mpr hyN)⟩
  · obtain ⟨e⟩ := F.twoCentral.normalizer E hz
    have hd := orderOf_dvd_natCard (⟨y, hyN⟩ : normalizer (E : Set G))
    have ho : orderOf (⟨y, hyN⟩ : normalizer (E : Set G)) = 3 :=
      (orderOf_coe _).symm.trans hy
    rw [ho, Nat.card_congr e.toEquiv, Nat.card_prod,
      Nat.card_eq_fintype_card (α := DihedralGroup 5), DihedralGroup.card] at hd
    norm_num at hd

/-- The first-class centralizer order is transported from the literal seed
centralizer, using the already proved element fusion. -/
theorem threeA_centralizer_card (H : CentralizerCalculation D)
    {y : G} (hy : ThreeA D y) : Nat.card (centralizer (zpowers y : Set G)) = 1080 := by
  obtain ⟨a, ha, _⟩ := exists_threeA D
  have hgen : zpowers (a : G) = D.X :=
    eq_of_le_of_card_ge (zpowers_le.mpr a.property)
      (by rw [Nat.card_zpowers, orderOf_coe, ha, D.card_X])
  obtain ⟨g, hg⟩ := isConj_iff.mp (threeA_isConj D H a ha hy)
  let e := MulAut.conj g
  have he : e (a : G) = y := hg
  have hcard : Nat.card (centralizer ({(a : G)} : Set G)) =
      Nat.card (centralizer ({y} : Set G)) := by
    apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
    intro c
    change c ∈ centralizer ({(a : G)} : Set G) ↔ e c ∈ centralizer ({y} : Set G)
    simp only [mem_centralizer_singleton_iff, ← he, ← map_mul, e.injective.eq_iff]
  rw [← centralizer_closure, ← zpowers_eq_closure, hgen] at hcard
  rw [zpowers_eq_closure, centralizer_closure, ← hcard]
  exact H.centralizer_card

/-- A cubic element whose centralizer contains a five-element belongs to 3A.
Both subgroup inclusions use the original ambient centralizers. -/
theorem threeA_of_five_dvd_centralizer {t : G} (F : SourceConclusion D t)
    {y : G} (hy : orderOf y = 3)
    (hfive : 5 ∣ Nat.card (centralizer (zpowers y : Set G))) : ThreeA D y := by
  let L := centralizer (zpowers y : Set G)
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' (G := L) 5 hfive
  let E := zpowers (f : G)
  have hE : Nat.card E = 5 := by rw [Nat.card_zpowers, orderOf_coe, hf]
  apply threeA_of_normalizes_five F hy hE
  apply Subgroup.centralizer_le_normalizer
  change y ∈ centralizer (zpowers (f : G) : Set G)
  rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
  exact f.property y (mem_zpowers y)

/-- The exceptional second-centralizer order in 47.3 cannot occur. -/
theorem centralizer_card_ne_180 (H : CentralizerCalculation D)
    {t : G} (F : SourceConclusion D t) {y : G} (hy : orderOf y = 3) :
    Nat.card (centralizer (zpowers y : Set G)) ≠ 180 := by
  intro hc
  have ha := threeA_of_five_dvd_centralizer F hy (by rw [hc]; norm_num)
  have hcard := threeA_centralizer_card H ha
  omega

/-- This excludes the actual C₃ × A₅ alternative, without any identification
of the second normalizer among the assumptions. -/
theorem not_centralizer_equiv_cyclic_three_alternating_five
    (H : CentralizerCalculation D) {t : G} (F : SourceConclusion D t)
    {y : G} (hy : orderOf y = 3) :
    ¬ Nonempty (centralizer (zpowers y : Set G) ≃*
      (Multiplicative (ZMod 3) × alternatingGroup (Fin 5))) := by
  rintro ⟨e⟩
  apply centralizer_card_ne_180 H F hy
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card (α := Multiplicative (ZMod 3))]
  norm_num

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer

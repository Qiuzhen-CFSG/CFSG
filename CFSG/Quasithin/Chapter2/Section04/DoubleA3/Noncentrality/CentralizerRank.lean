module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.AmbientNonfusion
public import Theory.GroupTheory.DihedralCoreCentralPoint
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.PSL3Two.Automorphisms

/-!
# The three-rank of the second marked centralizer

The component centralizer lies in the original characteristic-two
intersection. Its marked central involution and dihedral core embedding force
it to be a two-group. The faithful component action modulo that kernel then
bounds the three-rank by that of Aut(PSL₃(2)), whose order is 336.

This is the remaining ambient nonfusion calculation in Aschbacher--Smith
2.4.34, printed p.548. The dihedral embedding is on the actual core, so the
paired-model source construction supplies it without a Sylow replacement.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private theorem three_rank_le_one_of_card_aut
    {H : Type*} [Group H] [Finite H] (hc : Nat.card H = 336) : primeRank 3 H ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le H).mpr
  intro E hE
  obtain ⟨n, hn⟩ := (hE.isPGroup 3 E).exists_card_eq
  have hd : 3 ^ n ∣ 336 := hn ▸ (hc ▸ E.card_subgroup_dvd_card)
  have hsmall : n ≤ 1 := by
    by_contra h
    have hdiv : 9 ∣ 336 := (pow_dvd_pow 3 (by omega : 2 ≤ n)).trans hd
    norm_num at hdiv
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hsmall

/-- The actual normal component centralizer is a two-group once its core
embeds in the other dihedral Sylow factor. -/
theorem source_component_centralizer_isTwoGroup
    {M : Subgroup G} {d : MinimalBlockSetup M} {T : Sylow 2 G}
    {c : SourcePairCoordinates d T} (g : SourceCentralizerGeometry c)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂)) [K.Normal]
    (hz₁ : ∃ hz : g.z₁ ∈ involutionCentralizer g.z₂, (⟨g.z₁,hz⟩ : involutionCentralizer g.z₂) ∈ K)
    (f : pCore 2 (centralizer (K : Set (involutionCentralizer g.z₂))) →* DihedralGroup 4)
    (hf : Function.Injective f) :
    IsPGroup 2 (centralizer (K : Set (involutionCentralizer g.z₂))) := by
  let H := involutionCentralizer g.z₂
  let C : Subgroup H := centralizer (K : Set H)
  let M₂ : Subgroup H := M.subgroupOf H
  have hCM : C ≤ M₂ := by
    intro a ha
    apply h.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    obtain ⟨hz,hzK⟩ := hz₁
    have ha₁ : Commute (a : G) g.z₁ := by
      exact (congrArg Subtype.val (mem_centralizer_iff.mp ha ⟨g.z₁,hz⟩ hzK)).symm
    have ha₂ : Commute (a : G) g.z₂ := mem_centralizer_singleton_iff.mp a.property
    exact (ha₁.mul_right ha₂).eq
  have hCMchar : HasCharacteristicTwo (C.subgroupOf M₂) :=
    normal_core_selfCentralizing h.intersection_characteristicTwo (C.subgroupOf M₂)
  have hC : HasCharacteristicTwo C := hCMchar.of_equiv (subgroupOfEquivOfLe hCM)
  have hz₂H : g.z₂ ∈ H := mem_centralizer_singleton_iff.mpr rfl
  have hz₂C : (⟨g.z₂,hz₂H⟩ : H) ∈ C := by
    intro a _
    exact Subtype.ext (mem_centralizer_singleton_iff.mp a.property)
  let i : C := ⟨⟨g.z₂,hz₂H⟩,hz₂C⟩
  have hi : i ≠ 1 := by
    intro he
    have hz : g.z₂ = 1 := congrArg (fun a : C => ((a : H) : G)) he
    have hh := g.order_second
    rw [hz,orderOf_one] at hh
    omega
  have hic : i ∈ center C := by
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (a : H).property
  exact isTwoGroup_of_dihedral_core_and_central_point hC i hi hic f hf

/-- The literal second centralizer has three-rank at most one in the
PSL₃(2) branch. -/
theorem source_second_centralizer_three_rank_le_one
    {M : Subgroup G} {d : MinimalBlockSetup M} {T : Sylow 2 G}
    {c : SourcePairCoordinates d T} (g : SourceCentralizerGeometry c)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂)) [K.Normal]
    (hz₁ : ∃ hz : g.z₁ ∈ involutionCentralizer g.z₂, (⟨g.z₁,hz⟩ : involutionCentralizer g.z₂) ∈ K)
    (e : K ≃* Matrix.PSL3Two.PSL)
    (f : pCore 2 (centralizer (K : Set (involutionCentralizer g.z₂))) →* DihedralGroup 4)
    (hf : Function.Injective f) : primeRank 3 (involutionCentralizer g.z₂) ≤ 1 := by
  let H := involutionCentralizer g.z₂
  let a : H →* MulAut K := MulAut.conjNormal
  have hker : IsPGroup 2 a.ker := by
    dsimp only [a]
    rw [MulAut.conjNormal_ker_eq_centralizer]
    exact source_component_centralizer_isTwoGroup g h K hz₁ f hf
  have hzero : primeRank 3 a.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨n, hn⟩ := hker.exists_card_eq
    apply Nat.prime_three.coprime_iff_not_dvd.mp
    rw [hn]
    exact Nat.Coprime.pow_right n (by decide)
  have hAut : primeRank 3 (MulAut K) ≤ 1 := three_rank_le_one_of_card_aut
    ((Nat.card_congr (MulAut.congr e).toEquiv).trans Matrix.PSL3Two.Automorphisms.card_aut)
  have hb := primeRank_le_ker_add (p := 3) a
  rw [hzero,zero_add] at hb
  exact hb.trans hAut

/-- The graph actor's rank-two centralizer cannot fuse with the second mark. -/
theorem source_actor_not_conj_second
    {M : Subgroup G} {d : MinimalBlockSetup M} {T : Sylow 2 G}
    {c : SourcePairCoordinates d T} (g : SourceCentralizerGeometry c)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂)) [K.Normal]
    (hz₁ : ∃ hz : g.z₁ ∈ involutionCentralizer g.z₂, (⟨g.z₁,hz⟩ : involutionCentralizer g.z₂) ∈ K)
    (e : K ≃* Matrix.PSL3Two.PSL)
    (f : pCore 2 (centralizer (K : Set (involutionCentralizer g.z₂))) →* DihedralGroup 4)
    (hf : Function.Injective f)
    (x : G) (hx : 2 ≤ primeRank 3 (centralizer ({x} : Set G))) : ¬ IsConj x g.z₂ := by
  intro hconj
  obtain ⟨a, ha⟩ := isConj_iff.mp hconj
  have hb := source_second_centralizer_three_rank_le_one g h K hz₁ e f hf
  have hr := primeRank_equiv 3 (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj a) x)
  change primeRank 3 (centralizer ({x} : Set G)) =
    primeRank 3 (centralizer ({a*x*a⁻¹} : Set G)) at hr
  rw [ha] at hr
  change primeRank 3 (centralizer ({g.z₂} : Set G)) ≤ 1 at hb
  omega

end CFSG.Quasithin.Chapter2.DoubleA3

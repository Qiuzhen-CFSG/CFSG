module
public import Theory.SpecificGroups.Suzuki.SplitOuter
public import Theory.GroupTheory.TwoOrbitOddPrime.SplitOuter
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SuzukiBounds

/-!
# Suzuki component primes in the original Hall action kernel

The actual Suzuki outer quotient has a homomorphic section. The odd-rank
bound on the original local group therefore makes the index of its two
Suzuki components prime to every odd component prime, including primes
shared with the field degree. The original seed is separated in this row;
its opposite component acts trivially on W = [V_M,L]. The faithful image of
the first component consequently has the same index bound. Its centralizer
is the literal quotient-action kernel, so that kernel has order prime to
every odd Suzuki component prime.

In particular no five-divisible subgroup can support the remaining Suzuki
starred actors. The final theorem connects this exclusion to the unchanged
Hall carrier B. Large three-divisible, five-free support and nonseparated
even-linear seeds remain to be excluded before final source assembly.
Source: Aschbacher--Smith 1.2.2(a), 10.1.3 and10.2.3,
printed pp.504,742,745; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
private theorem source_local_sqtk (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsSQTK KnownSimple.IsKnownSimple D.maximalLocal := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  exact D.simpleQTKE.twoLocal_sqtk hu.normalizer_maximal.1


variable (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- Every odd component prime is absent above the original Suzuki pair. -/
theorem original_suzuki_orbit_index_coprime
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    Nat.Coprime p ((localOrbit T L).subgroupOf D.maximalLocal).index := by
  let M := D.maximalLocal
  let A := L.subgroupOf M
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hlocal := source_local_sqtk D
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hlocal.isKGroup.quotient _⟩
    intro r hr ho
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans
      (hlocal.stronglyQuasithin r hr ho)
  have hnot : ¬ A.Normal := fun ha =>
    hn (hTM.trans ((normal_subgroupOf_iff_le_normalizer hLM).mp ha))
  obtain ⟨hi,_⟩ := (proposition_1_2_1_three_index_knownSimple hQ
    D.component_in_maximalLocal).resolve_left hnot
  let a : (A ⧸ pCore 2 A) ≃* (L ⧸ pCore 2 L) := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLM) (pCore_map_iso 2 _)
  let := D.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv a.symm
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let tM : M := ⟨t,hTM ht⟩
  have htnM : tM ∉ normalizer (A : Set M) := by
    rw [←subgroupOf_normalizer_eq hLM]
    exact htn
  have hmap : (A ⊔ A.conjBy tM).map M.subtype = localOrbit T L := by
    rw [Subgroup.map_sup]
    change A.map M.subtype ⊔ (A.map (MulAut.conj tM).toMonoidHom).map M.subtype = _
    rw [map_map,show M.subtype.comp (MulAut.conj tM).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp M.subtype from rfl,←map_map,
      map_subgroupOf_eq_of_le hLM,←hpair]
  have he : A ⊔ A.conjBy tM = (localOrbit T L).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [hmap,map_subgroupOf_eq_of_le (localOrbit T L).le_normalizer]
  rw [←he]
  refine TwoOrbitOddPrime.splitOuter_cComponent_pair_index_coprime p hp
    D.component_in_maximalLocal hi tM htnM ?_ ?_
    (hlocal.stronglyQuasithin p Fact.out ((Fact.out : p.Prime).odd_of_ne_two hp))
    (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (BenderSuzuki.MatrixGroups.suzukiOuterSection m hm)
    (BenderSuzuki.MatrixGroups.suzukiOuterSection_rightInverse m hm) (a.trans e)
  · apply _root_.eq_bot_iff.mpr
    intro x hx
    have hz : a x ∈ center (L ⧸ pCore 2 L) := (centerCongr a ⟨x,hx⟩).property
    rw [source_nonnormal_component_core_center D hn,mem_bot] at hz
    exact a.map_eq_one_iff.mp hz
  · rwa [Nat.card_congr a.toEquiv]

local instance suzukiPrimeElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
/-- Every odd Suzuki component prime is absent from the exact moved quotient-action kernel. -/
theorem original_suzuki_quotient_kernel_coprime
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    Nat.Coprime p (Nat.card (originalMovedQuotientAction D c.nonnormal).ker) := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hsep := original_seed_separated_of_suzuki D c m hm e ht htn
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let R := (localOrbit T L).subgroupOf N
  let ρ := movedStabilizerAction D
  let f := actionHom ρ
  let α := originalMovedQuotientAction D c.nonnormal
  let S := movedStabilizerComponentImage D
  have hLN : L ≤ N := le_inf
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
  have hRN : localOrbit T L ≤ N := le_inf (localOrbit T L).le_normalizer
    (source_nonnormal_orbit_le_normalizer D c.nonnormal)
  have hpair : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 c.nonnormal)
      inf_le_right ht htn
  have hLtN : L.map (MulAut.conj t).toMonoidHom ≤ N :=
    (le_sup_right.trans hpair.symm.le).trans hRN
  have hkill : (L.map (MulAut.conj t).toMonoidHom).subgroupOf N ≤ f.ker := by
    intro l hl
    apply (actionHom_eq_one_iff ρ l).mpr
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * (w.toMul : G) * (l : G)⁻¹ = (w.toMul : G)
    have hc := mem_centralizer_iff.mp
      (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep w.toMul.property) l hl
    rw [hc,mul_assoc,mul_inv_cancel,mul_one]
  have hRS : R.map f = S := by
    change ((localOrbit T L).subgroupOf N).map f = _
    rw [hpair,subgroupOf_sup hLN hLtN,Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff (f := f) _).mpr hkill,sup_bot_eq]
    change (L.subgroupOf N).map f = ((actionHom ρ).comp (movedStabilizerComponent D).subtype).range
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let eS := originalMovedComponentEquiv D c.nonnormal
  let : IsSimpleGroup S := eS.isSimpleGroup
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv eS.symm
  have hdis : S ⊓ α.ker = ⊥ := by
    rw [show α.ker = centralizer (S : Set (actionImage ρ)) from
      originalMovedQuotientAction_kernel D c.nonnormal]
    apply bot_unique
    rintro a ⟨ha,hac⟩
    have hz : (⟨a,ha⟩ : S) ∈ center S := by
      apply mem_center_iff.mpr
      intro s
      exact Subtype.ext (mem_centralizer_iff.mp hac s s.property)
    rw [center_eq_bot_of_simple_perfect] at hz
    exact congrArg Subtype.val (mem_bot.mp hz)
  have hc : Nat.card α.ker ∣ S.index := by
    have hh := S.relIndex_dvd_index_of_normal α.ker
    rwa [←inf_relIndex_right,hdis,relIndex_bot_left] at hh
  have hindex : R.index ∣ ((localOrbit T L).subgroupOf D.maximalLocal).index := by
    change (localOrbit T L).relIndex N ∣ _
    rw [←relIndex_subgroupOf (H := localOrbit T L) (L := D.maximalLocal) inf_le_left]
    exact relIndex_dvd_index_of_le (subgroupOf_mono D.maximalLocal hRN)
  have hS : S.index ∣ ((localOrbit T L).subgroupOf D.maximalLocal).index := by
    rw [←hRS]
    exact (R.index_map_dvd ρ.asGroupHom.rangeRestrict_surjective).trans hindex
  exact (original_suzuki_orbit_index_coprime D c.nonnormal m hm e p hp hd).of_dvd_right
    (hc.trans hS)
/-- The original Suzuki kernel has no factor five, including field degrees divisible by five. -/
theorem original_suzuki_quotient_kernel_five_free
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    Nat.Coprime 5 (Nat.card (originalMovedQuotientAction D c.nonnormal).ker) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply original_suzuki_quotient_kernel_coprime D c m hm e 5 (by decide)
  rw [Nat.card_congr e.toEquiv]
  exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_five_dvd m hm

/-- A five-divisible support subgroup cannot lie in the actual Suzuki action kernel. -/
theorem original_suzuki_no_five_support
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (J : Subgroup (actionImage (movedStabilizerAction D)))
    (hJ : J ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hfive : 5 ∣ Nat.card J) : False :=
  Nat.prime_five.coprime_iff_not_dvd.mp
    ((original_suzuki_quotient_kernel_five_free D c m hm e).of_dvd_right
      (card_dvd_of_le hJ)) hfive

/-- The literal Hall consumer retains only nonseparated even-linear seeds or
large Suzuki support of order prime to five. The latter exclusion applies to
the whole quotient kernel and hence to every component in its moved orbit. -/
theorem original_hall_conclusion_or_five_free_remaining_cases
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      OriginalNonseparatedEvenCase D ∨
      (OriginalSuzukiLargeCentralizingSupport D c.nonnormal ∧
        Nat.Coprime 5 (Nat.card (originalMovedQuotientAction D c.nonnormal).ker)) := by
  rcases original_hall_conclusion_or_large_remaining_cases D c with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨m,hm,⟨e⟩,hrest⟩ := h
    exact Or.inr (Or.inr ⟨⟨m,hm,⟨e⟩,hrest⟩,
      original_suzuki_quotient_kernel_five_free D c m hm e⟩)
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules

module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OrdinaryFinite
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.BinaryClosure
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.Suzuki.OddSubgroups
/-!
# Excluding the ordinary large Ree row

The literal nontrivial radical intersection has a normalizer lying in a
full Ree parabolic. The actual Levi projection has a two-group kernel.
Perfectness kills its field-torus coordinate, leaving SL₂ or Suzuki,
whose odd Sylow subgroups are cyclic. Thus the source span has odd rank
at most one, forcing the original centerless seed to be normal.

OrdinaryModels and OrdinarySource apply this to the genuine covering
and elementary Hall-kernel configurations.
Source: Aschbacher--Smith C.3.5 and C.4.8, pp.150--154, using the
full Ree parabolic geometry in F.1.12, pp.263--264.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28

private theorem perfect_two_kernel_product_rank
    {X S A : Type*} [Group X] [Finite X] [Group S] [Finite S] [CommGroup A]
    [Group.IsPerfect X] (f : X →* S × A) (hk : IsPGroup 2 f.ker)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : primeRank p S ≤ 1) :
    primeRank p X ≤ 1 := by
  let f₂ := (MonoidHom.snd S A).comp f
  let : Group.IsPerfect f₂.range := Group.IsPerfect.range f₂
  have hsecond (x : X) : (f x).2 = 1 :=
    congrArg Subtype.val (Subsingleton.elim (f₂.rangeRestrict x) 1)
  let g := (MonoidHom.fst S A).comp f
  have he : g.ker = f.ker := by
    ext x
    constructor
    · intro hx
      exact Prod.ext hx (hsecond x)
    · intro hx
      exact congrArg Prod.fst hx
  have hz : primeRank p g.ker = 0 := by
    rw [he]
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    intro hd
    have hp2 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hd)
    subst p
    exact ho.not_two_dvd_nat (dvd_refl 2)
  have hb := primeRank_le_ker_add (p := p) g
  omega

private theorem perfect_parabolic_rank
    {X S A : Type*} [Group X] [Finite X] [Group S] [Finite S] [CommGroup A]
    (P U : Subgroup X) (hPU : P ≤ U) [Group.IsPerfect P]
    (π : U →* S × A) (hk : IsPGroup 2 π.ker)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : primeRank p S ≤ 1) :
    primeRank p P ≤ 1 := by
  let f := π.comp (inclusion hPU)
  have hf : IsPGroup 2 f.ker := hk.comap_of_injective (inclusion hPU) (inclusion_injective _)
  exact perfect_two_kernel_product_rank f hf ho hr

private theorem ree_perfect_two_normalizer_rank
    {m : ℕ} (hm : 1 ≤ m) (A P : Subgroup (ReeF4.Model m))
    (hA : Group.IsPerfect A) (hP : IsPGroup 2 P) (hne : P ≠ ⊥)
    (hn : A ≤ normalizer (P : Set (ReeF4.Model m)))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) : primeRank p A ≤ 1 := by
  let := hA
  obtain ⟨g,s,hs⟩ := ReeF4.ConverseParabolics.normalizer_cover hm P hne hP
  let A' := A.map (MulAut.conj g).toMonoidHom
  have hA' : A' ≤ ReeF4.ConverseParabolics.parabolic m s := (map_mono hn).trans hs
  let : Group.IsPerfect A' := Group.IsPerfect.map _
  rw [primeRank_congr p ((MulAut.conj g).subgroupMap A)]
  cases s with
  | linear =>
    exact perfect_parabolic_rank A' _ hA' (ReeF4.ConverseParabolics.linearProjection hm)
      (ReeF4.ConverseParabolics.linearProjection_ker_isPGroup hm) ho
      (Matrix.SL2.binary_odd_primeRank_le_one ho)
  | suzuki =>
    apply perfect_parabolic_rank A' _ hA' (ReeF4.ConverseParabolics.suzukiProjection hm)
      (ReeF4.ConverseParabolics.suzukiProjection_ker_isPGroup hm) ho
    let S : Sylow p (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := Classical.choice inferInstance
    have hc := BenderSuzuki.MatrixGroups.suzukiSylow_isCyclic_of_ne_two (by omega : 0 < m)
      (by intro he; subst p; exact ho.not_two_dvd_nat (dvd_refl 2)) S
    exact S.primeRank_le_one_of_isCyclic hc

theorem ordinary_span_primeRank_le_one_of_ree
    {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    {m : ℕ} (hm : 1 ≤ m) (e : K ⧸ center K ≃* ReeF4.Model m)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (conjugateSpanBy L M) ≤ 1 := by
  apply h.ordinary_span_primeRank_le_of_model_two_normalizers K hK e ho
  intro A P hA hP hne hn
  exact ree_perfect_two_normalizer_rank hm A P hA hP hne hn ho

/-- The ordinary large Ree central quotient forces normalization of the
original centerless seed, with both full parabolic rows discharged. -/
theorem normalizes_of_simple_ordinary_ree
    {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : IsComponent H K)
    {m : ℕ} (hm : 1 ≤ m) (e : K ⧸ center K ≃* ReeF4.Model m) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_of_simple_span_odd_ranks hz Nat.prime_three
  intro p hp ho _
  let : Fact p.Prime := ⟨hp⟩
  exact h.ordinary_span_primeRank_le_one_of_ree K hK hm e ho

end CFSG.Quasithin.ChapterC.HypothesisC28

namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The same full-parabolic bound excludes a large Ree component containing
  the literal odd-actor residual, without imposing an A₅ marking. -/
theorem source_nonnormal_oddNormalizer_no_placed_ree_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {m : ℕ} (hm : 1 ≤ m) (e : K ⧸ center K ≃* ReeF4.Model m) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_local_rank_bound
    D hn B hBC hodd hBV K hFK e
  intro A P hA hP hne hN p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact ChapterC.HypothesisC28.ree_perfect_two_normalizer_rank hm A P hA hP hne hN ho

/-- The actual large Ree model supplies its soluble outer action and
  residual placement once the original covering subgroup is unique. -/
theorem source_nonnormal_oddNormalizer_no_ree_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {m : ℕ} (hm : 1 ≤ m) (e : K ⧸ center K ≃* ReeF4.Model m) : False := by
  have hmodel : ChapterA.Section02.IsTheoremCModel (K ⧸ center K) :=
    .rank_two (2 * m + 1) (.ree_f4 m hm rfl ⟨e⟩)
  exact source_nonnormal_oddNormalizer_no_placed_ree_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout hmodel)
    hm e

/-- The literal elementary Hall-kernel application retains only the earlier
  module fixation and covering uniqueness premises for the large Ree row. -/
theorem source_hall_kernel_no_ree_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (Y : Subgroup H)
    (hfix : Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsElementaryAbelian p A)
    (hAY : A ≤ Y.map H.subtype) (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (A : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (A : Set G))) D.maximalLocal)
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal)
    {m : ℕ} (hm : 1 ≤ m) (e : K ⧸ center K ≃* ReeF4.Model m) : False := by
  let := hA
  have ho : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  exact source_nonnormal_oddNormalizer_no_ree_component D hn A hAC ho
    ((le_inf hAY hAC).trans hfix) hu K hK hout hm e
end CFSG.Quasithin.Chapter10

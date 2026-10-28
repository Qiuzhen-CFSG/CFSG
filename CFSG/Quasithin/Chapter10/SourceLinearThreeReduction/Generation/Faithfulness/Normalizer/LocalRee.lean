module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalBinaryExclusions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OrdinaryRee
/-!
# Ree parabolic exclusion with a fixed local module

The quotient image of the local module is nonzero. Its normalizer lies in
a Ree parabolic; the perfect residual has cyclic odd Sylow images there,
contradicting its two original simple factors.
Source: Aschbacher--Smith 4.4.12 and 10.2.3(2), pp.622,745.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04
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

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
/-- A fixed local orbit suffices for the large Ree exclusion. -/
theorem source_nonnormal_oddNormalizer_no_placed_ree_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {m : ℕ} (hm : 1 ≤ m) (e : K ⧸ center K ≃* ReeF4.Model m) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_local_rank_bound
    D hn V hVV hne hVX hNV B hBC hodd hBV K hFK e
  intro A P hA hP hne hN p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact ree_perfect_two_normalizer_rank hm A P hA hP hne hN ho


end CFSG.Quasithin.Chapter10.LocalFixed

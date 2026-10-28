module
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.Enlargement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.PrimeRankZero
/-!
# Excluding actual rank-one normalizer enlargements

Every overgroup of an original A₅ conjugate retains a factor of five after
quotienting by its two-core. If a strict containing C-component has binary
SL₂ two-core quotient, restrict the original half-Sylow to it. The original
opposite factor remains a local C-component for this full Sylow. Proper Sylow
overgroups in the rank-one cover are solvable, whereas this local join is
nonsolvable, so component minimality contradicts strictness.

Source: Aschbacher–Smith 10.2.6, pp.748–749, using the rank-one
non-enlargement row of A.3.12, pp.47–48.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Every overgroup of an original A₅ conjugate retains a factor of five modulo its two-core. -/
theorem source_a5_conjugate_overgroup_five
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} {K : Subgroup G} (hBK : L.map (MulAut.conj t).toMonoidHom ≤ K) :
    5 ∣ Nat.card (K ⧸ pCore 2 K) := by
  have hL : primeRank 5 L = 1 := by
    rw [← primeRank_quotient_eq_of_isTwoGroup 5 (by decide) (pCore 2 L) pCore_isPGroup,
      primeRank_congr 5 e]
    exact GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 5 (by decide) (by decide)
  have hB : primeRank 5 (L.map (MulAut.conj t).toMonoidHom) = 1 := by
    exact (primeRank_congr 5 (L.equivMapOfInjective
      (MulAut.conj t).toMonoidHom (MulAut.conj t).injective)).symm.trans hL
  have hK := primeRank_mono 5 hBK
  have hQ : primeRank 5 (K ⧸ pCore 2 K) = primeRank 5 K :=
    primeRank_quotient_eq_of_isTwoGroup 5 (by decide) (pCore 2 K) pCore_isPGroup
  by_contra hn
  have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
  rw [hQ] at hz
  omega

include D in
private theorem source_conjugate_local {t : G} (ht : t ∈ (T : Subgroup G)) :
    L.map (MulAut.conj t).toMonoidHom ∈ localCComponents (T : Subgroup G) := by
  have hh := (Chapter1.mem_L_map_iff (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective).mpr D.maximal.1
  have he : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = T :=
    mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
  rw [he] at hh
  exact hh.1

include D in
/-- A genuine rank-one quotient contradicts the strict opposite enlargement. -/
theorem source_a5_strict_component_not_binary_rank_one
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn (normalizer (L : Set G)))
    (hBK : L.map (MulAut.conj t).toMonoidHom < K)
    (hQ : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (d : (K ⧸ pCore 2 K) ≃* SL(2,F)) : False := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let B := L.map (MulAut.conj t).toMonoidHom
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (source_a5_component_normalizer_sylow D e hn) hK.1 hK.2.subnormal
  have hSe : (S : Subgroup K) = R.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hS,subgroupOf_map_subtype]
  have hlocal : B.subgroupOf K ∈ localCComponents S := by
    rw [hSe]
    apply ChapterA.Section03.SourceEmbeddings.local_restrict
      (localCComponents_antitone inf_le_left (source_conjugate_local D ht)) hBK.le
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
  let : IsQuasisimple (K ⧸ pCore 2 K) := hQ
  let : Group.IsPerfect K := Group.IsPerfect.top_iff.mp htop.perfect
  let f : K →* SL(2,F) := d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hf : Function.Surjective f := d.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := B.subgroupOf K ⊔ (S : Subgroup K)
  have hp : ¬ Group.IsSolvable P := by
    intro hs
    let := hs
    exact hlocal.not_isSolvable inferInstance
  have heP : P = ⊤ := Matrix.SpecialLinearGroup.sylow_overgroup_eq_top_of_component_cover
    htop f hf S P le_sup_right hp
  have hBc : (B.subgroupOf K).IsCComponent := by
    change ((B.subgroupOf K).subgroupOf P).IsCComponent at hlocal
    rw [heP] at hlocal
    simpa only [map_subgroupOf_eq_of_le le_top] using
      hlocal.map_subtype (show (⊤ : Subgroup K).IsSubnormal from .top)
  have heB := hBc.eq_of_le htop le_top
  exact hBK.ne (le_antisymm hBK.le (subgroupOf_eq_top.mp heB))
end CFSG.Quasithin.Chapter10

module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneTorusGeometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2BorelResidual

/-!
# The field-four restriction in original15.3.18

The literal core-to-star map transports the marked C.2.7 Borel to the
natural block quotient. The orthogonal action of M on V has order72, so
its {2,3}-residual centralizes V. In fields larger than four the Borel
residual has no noncentral fixed vectors in the natural block module.
The actual Sylow-fixed span split therefore forces L to centralize V,
contradicting L outside M. Thus the original natural field degree is two.

Source: Aschbacher--Smith15.3.18, pp.1126--1127, using15.3.16 andB.2.14.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The literal core quotient map transports the marked C.2.7 Borel. -/
theorem natural_block_marked_borel
    {I L R M : Subgroup G} (h : Input KnownSimple.IsKnownSimple I R M L)
    (hb : IsRankOneBorel (starImage L R L) (starM L R M))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ∃ P : Sylow 2 SL(2,F),
      (M.subgroupOf L).map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
        normalizer (P : Set SL(2,F)) := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center SL(2,F) at hh
    rw [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hne : starImage L R L ≠ ⊥ :=
    ne_bot_of_gt (ChapterC.C27Source.star_thompson_intersection_from_source h).2
  let a := coreStarEquivOfCenterEqBot h.normalizes h.quasisimple hne hz
  let b := a.symm.trans e
  obtain ⟨S,hS⟩ := hb
  let P := S.mapSurjective (f := b.toMonoidHom) b.surjective
  refine ⟨P,?_⟩
  have hm : (M.subgroupOf L).map (toStarImage L R) =
      (starM L R M).subgroupOf (starImage L R L) := by
    ext x
    constructor
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,mem_sup_left l.property⟩,⟨hl,l.property⟩,rfl⟩
    · rintro ⟨l,hl,he⟩
      exact ⟨⟨l,hl.2⟩,hl.1,Subtype.ext he⟩
  have hSM : (starM L R M).subgroupOf (starImage L R L) = normalizer (S : Set (starImage L R L)) := by
    rw [hS]
    exact comap_map_eq_self_of_injective (starImage L R L).subtype_injective _
  have hq : b.toMonoidHom.comp (toStarImage L R) =
      e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)) := by
    apply MonoidHom.ext
    intro l
    change e (a.symm (a (QuotientGroup.mk' (pCore 2 L) l))) = _
    rw [a.symm_apply_apply]
    rfl
  rw [←hq,←Subgroup.map_map,hm,hSM]
  exact map_normalizer_eq_of_bijective (S : Subgroup (starImage L R L)) b.bijective

/-- The actual orthogonal action has only the primes two and three. -/
theorem orthogonalActor_twoThree : IsPiGroup twoThreePrimes OrthogonalActor := by
  have hc : Nat.card OrthogonalActor = 72 := by
    have hs : Nat.card OrthogonalPlaneActor = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [RegularWreathProduct.card,hs]
    norm_num [OrthogonalPlaneIndex,Nat.card_eq_fintype_card]
  apply (IsPiGroup_iff _ _).mpr
  intro p hp
  rw [hc] at hp
  have hh : (p : ℕ) ∣ 2 ^ 3 * 3 ^ 2 := by norm_num at *; exact hp
  rcases p.property.dvd_mul.mp hh with h2 | h3
  · have he : (p : ℕ) = 2 := (Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow h2)
    exact Or.inl he
  · have he : (p : ℕ) = 3 := (Nat.prime_dvd_prime_iff_eq p.property Nat.prime_three).mp
      (p.property.dvd_of_dvd_pow h3)
    exact Or.inr he

omit [Finite G] in
/-- Every actual subgroup of M has its {2,3}-residual in C_G(V). -/
theorem orthogonal_residual_centralizes
    (d : LocalData G) (B : Subgroup G) (hBM : B ≤ d.M) :
    (piResidual twoThreePrimes B).map B.subtype ≤ centralizer (d.V : Set G) := by
  let a := d.action.actor.comp (inclusion hBM)
  have hp : IsPiGroup twoThreePrimes a.range :=
    orthogonalActor_twoThree.of_injective a.range.subtype a.range.subtype_injective
  have hk := piResidual_le_ker_of_range twoThreePrimes a hp
  rintro _ ⟨b,hb,rfl⟩
  have he : d.action.actor (inclusion hBM b) = 1 := hk hb
  have hh : inclusion hBM b ∈ d.action.actor.ker := he
  rw [d.action.ker_actor] at hh
  exact hh
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Subgroup Theory.GroupTheory ChapterC
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open scoped Pointwise MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- Original15.3.18 forces the natural rank-one field to have four elements.
The actual Borel residual fixes V, while for larger fields its fixed vectors
in the natural block module are central. The Sylow-fixed span split then
forces L to centralize V, contrary to its original outside condition. -/
theorem source_15_3_18_field_degree
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hSyl : Chapter1.IsSylowIn 2 d.R (c.L ⊔ d.R))
    (hborel : IsRankOneBorel (starImage c.L d.R c.L) (starM c.L d.R (d.MI I)))
    {n : ℕ} (hn : IsL2EvenBlock c.L n) : n = 2 := by
  have hnlow := hn.1
  by_contra hne
  have hnlarge : 2 < n := by omega
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have hC : centralizer (d.V : Set G) ≤ d.M := by
    exact (Subgroup.centralizer_le_normalizer _).trans
      (InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1).ge
  have hW := RankTwoElimination.OriginalSource.source_lemma_15_3_16_span_isR2
    hG d hempty hM hu hmany hI htwo hf c
  have hWL : d.componentSpan c.L ≤ c.L ⊔ d.R :=
    conjugateSpanBy_le ((V_le_R d htwo.2.2.2.2.1).trans le_sup_right)
      (le_sup_left.trans (c.L ⊔ d.R).le_normalizer)
  have hU := natural_block_support d c h.normalizes hW hWL hC hn.2.1
  have hsplit := natural_block_span_split d c h.normalizes htwo.2.2.2.2.1 hSyl hn.2.1 hU
  obtain ⟨_,hs,F,_,_,hF,_,r,⟨m⟩,hr⟩ := hn
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let B := (d.MI I).subgroupOf c.L
  obtain ⟨P,hP⟩ := natural_block_marked_borel h hborel m.quotientIso
  let N := (piResidual twoThreePrimes B).map B.subtype
  have hNV : N.map c.L.subtype ≤ centralizer (d.V : Set G) := by
    have hBM : B.map c.L.subtype ≤ d.M := by
      rintro _ ⟨b,hb,rfl⟩
      exact hb.1
    have hh := orthogonal_residual_centralizes d (B.map c.L.subtype) hBM
    rw [←map_embedded_piResidual twoThreePrimes B c.L.subtype] at hh
    exact hh
  have hfixed := natural_block_residual_fixed_le_center hnlarge hF r m hr B P hP
  have hVfix : d.V ≤ centralizer (c.L : Set G) := by
    intro v hv
    have hvm : v ∈ (blockU c.L).map c.L.subtype ⊔
        (d.componentSpan c.L ⊓ centralizer (c.L : Set G)) :=
      hsplit ▸ le_conjugateSpanBy d.V c.L hv
    have hprod : v ∈ ((blockU c.L).map c.L.subtype : Set G) *
        ((d.componentSpan c.L ⊓ centralizer (c.L : Set G) : Subgroup G) : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left]
      · exact hvm
      · exact (inf_le_right.trans (centralizer_le (map_subtype_le (blockU c.L)))).trans
          (Subgroup.centralizer_le_normalizer _)
    obtain ⟨u,⟨l,hl,he⟩,z,hz,hvz⟩ := hprod
    subst u
    have hzN : z ∈ centralizer (N.map c.L.subtype : Set G) :=
      centralizer_le (map_subtype_le N) hz.2
    have hvN : v ∈ centralizer (N.map c.L.subtype : Set G) :=
      le_centralizer_iff.mp hNV hv
    have hlN : l ∈ centralizer (N : Set c.L) := by
      have hh := (centralizer (N.map c.L.subtype : Set G)).mul_mem hvN
        ((centralizer _).inv_mem hzN)
      rw [←hvz,mul_inv_cancel_right] at hh
      intro x hx
      exact Subtype.ext (hh x (mem_map_of_mem c.L.subtype hx))
    have hlc : l ∈ center c.L := hfixed ⟨hl,hlN⟩
    have hlC : (l : G) ∈ centralizer (c.L : Set G) := by
      intro x hx
      exact congrArg Subtype.val (mem_center_iff.mp hlc ⟨x,hx⟩)
    exact hvz ▸ (centralizer (c.L : Set G)).mul_mem hlC hz.2
  exact c.outside ((le_centralizer_iff.mp hVfix).trans hC)
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

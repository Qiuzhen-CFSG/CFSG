module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticActor
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.PrimeResidual
public import Theory.Representation.BinaryOffender.FaithfulInvariantSection

/-!
# The extra cubic actor in the order-fifteen marked residual

If the faithful two-residual of the original prime-five marked centralizer
has order fifteen, its prime-to-three residual has order three. It fixes
the first support. On the second support it centralizes the original
dihedral factor: the cubic and that factor are disjoint normal subgroups
of the same marked centralizer. Thus it centralizes the whole original
factor product and preserves the Thompson fixed subgroup.

Transport through the literal C_M(Z₁)/C_M(V) map constructs
A = O^{3′}(C_M(Z₁)). Original 15.1.14 places A in M ∩ Mc. Its image has
order three, and irreducibility of the original quintic actor makes
[V,A] the original moving support of order sixteen. The actual
eight-dimensional consumer retains both supports and the same marking.

This is a consequence of the order-fifteen alternative, not its ambient
exclusion. In particular, no centralization theorem for all of M ∩ Mc
is inferred from the residual theorems for individual HStar members.
The prime-five marker and same-component final assembly still require
that exclusion and the independently owned catalogue exhaustion.

Source: Aschbacher--Smith 15.1.14(2), 15.1.16(a)--18 and 15.1.23,
printed pp.1091--1093,1100. All residual conventions and quotient maps
are the original ones.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition

private theorem cubic_residual_of_cyclic_fifteen
    {K : Type*} [Group K] [Finite K] (hc : IsCyclic (pResidual 2 K))
    (hcard : Nat.card (pResidual 2 K) = 15) :
    primeToResidual 3 K = pCore 3 K ∧ Nat.card (primeToResidual 3 K) = 3 ∧
      primeToResidual 3 K ≤ pResidual 2 K := by
  let R := pResidual 2 K
  let : IsCyclic R := hc
  have hcop : Nat.Coprime 3 R.index := by
    rw [index_eq_card]
    obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := K) 2).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have he : primeToResidual 3 K = pCore 3 K :=
    primeToResidual_eq_pCore_of_nilpotent_normal R inferInstance hcop
  have hle : primeToResidual 3 K ≤ R := primeToResidual_le R hcop
  let P : Sylow 3 R := Classical.arbitrary _
  have hP : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity,hcard]
    decide +kernel
  have hl : 3 ∣ Nat.card (pCore 3 K) := by
    have hh := card_dvd_of_le (P.map_le_pCore inferInstance inferInstance 3)
    rw [card_map_of_injective R.subtype_injective,hP] at hh
    exact hh
  have hd : Nat.card (pCore 3 K) ∣ 15 :=
    hcard ▸ card_dvd_of_le (he ▸ hle)
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := K)).exists_card_eq
  have hfive : Nat.Coprime 5 (Nat.card (pCore 3 K)) :=
    hn ▸ (by decide : Nat.Coprime 5 3).pow_right n
  have hthree : Nat.card (pCore 3 K) ∣ 3 :=
    hfive.symm.dvd_of_dvd_mul_left hd
  exact ⟨he,he ▸ Nat.dvd_antisymm hthree hl,hle⟩

variable {G : Type*} [Group G] [Finite G]

/-- A fifteen-element faithful residual has a canonical cubic image
centralizing the entire original product of dihedral factors. -/
theorem ThompsonPair.full_image_cubic_residual_of_fifteen
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (hfive : s.prime = 5) :
    let ρ := imageRepresentation M V hn
    let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)
    let K := subspaceKernel ρ W ⊤
    Nat.card (pResidual 2 K) = 15 →
      Nat.card (primeToResidual 3 K) = 3 ∧
      (primeToResidual 3 K).map K.subtype ≤ centralizer (Jhat ρ : Set _) := by
  intro ρ W K h15
  let D := internalActionImage M V hn
  let F := c.ambientFactor d s.first
  let B := c.ambientFactor d s.second
  let A := (primeToResidual 3 K).map K.subtype
  obtain ⟨he,hcard,hle⟩ := cubic_residual_of_cyclic_fifteen
    (s.full_image_residual_of_prime_five hTM hn c d π hp hs hJ hfive).1 h15
  have hfix : F.space ≤ fixedSpace ρ A := by
    intro w hw a
    exact s.full_residual_fixes_first hTM hn c d π hp hs hJ hw
      ⟨a,(map_mono hle) a.property⟩
  have hAF : A ≤ subspaceStabilizer ρ F.space := by
    apply le_subspaceStabilizer
    intro a ha w hw
    have hh : ρ a w = w := hfix hw ⟨a,ha⟩
    rwa [hh]
  have hFN : F.actor ≤ subspaceStabilizer ρ F.space := by
    apply le_subspaceStabilizer
    rintro g ⟨b,rfl⟩ w ⟨v,rfl⟩
    exact ⟨F.action b v,F.embedding.equivariant b v⟩
  have hfaith : ∀ g ∈ F.actor, (∀ w ∈ F.space, ρ g w = w) → g = 1 := by
    rintro g ⟨b,rfl⟩ hb
    have hh : F.action b = 1 := by
      ext v
      apply F.embedding.space_injective
      exact (F.embedding.equivariant b v).trans (hb _ ⟨v,rfl⟩)
    rw [F.faithful (hh.trans F.action.map_one.symm),map_one]
  have hACF : A ≤ centralizer (F.actor : Set D) := by
    intro a ha
    exact centralizes_of_fixes_faithful_section ρ F.actor F.space hFN hfaith
      (c.support_stabilizer_normalizes_actor d π hp hs s.first (hAF ha))
      (fun w hw => hfix hw ⟨a,ha⟩)
  let P := (s.marking s.second).kernel.map B.embedding.groupMap
  have hKP : K ≤ normalizer (P : Set D) :=
    (s.full_image_residual hTM hn c d hJ).2.1
  have hKB : K ≤ subspaceStabilizer ρ B.space := by
    rw [←s.kernel_moved s.second]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hKP
  have hBK : B.actor ≤ K := by
    intro b hb
    exact ⟨mem_top _,fun w hw => c.ambient_cross d s.distinct hw.1 ⟨b,hb⟩⟩
  let Bk := B.actor.subgroupOf K
  let : Bk.Normal := normal_subgroupOf_of_le_normalizer
    (hKB.trans (c.support_stabilizer_normalizes_actor d π hp hs s.second))
  have hBcard : Nat.card Bk = 10 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv]
    change Nat.card B.embedding.groupMap.range = 10
    rw [←Nat.card_congr (MonoidHom.ofInjective B.embedding.group_injective).toEquiv]
    have hd := (s.dihedral s.second).dihedral.some
    change Nat.card (d.factor s.second).Carrier = 10
    rw [Nat.card_congr hd.toEquiv,DihedralGroup.nat_card,hfive]
  have hdis : Disjoint (primeToResidual 3 K) Bk :=
    disjoint_of_coprime_natCard (by rw [hcard,hBcard]; decide)
  have hACB : A ≤ centralizer (B.actor : Set D) := by
    rintro a ⟨a,ha,rfl⟩ b hb
    exact congrArg Subtype.val
      (commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hdis)
        ha ⟨b,hBK hb⟩ hb)
  refine ⟨hcard,?_⟩
  apply le_centralizer_iff.mpr
  rw [←c.ambient_actors_generate d]
  apply iSup_le
  intro k
  rcases s.covers k with rfl | rfl
  · exact le_centralizer_iff.mp hACF
  · exact le_centralizer_iff.mp hACB

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker

namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_action_image
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (W : Submodule (ZMod 2) (Additive V)) :
    let K := subspaceKernel (imageRepresentation M V hn) W ⊤
    let C := M ⊓ centralizer (plane V W : Set G)
    let A := (primeToResidual 3 C).map C.subtype
    (A.subgroupOf M).map (actionHom M V hn).rangeRestrict =
      (primeToResidual 3 K).map K.subtype := by
  intro K C A
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let hAM : A ≤ M := (map_subtype_le _).trans inf_le_left
  let a := f.comp (inclusion hAM)
  obtain ⟨q,hq,_,hcoord⟩ := ExtraspecialMarker.stabilizer_projection M V hn W
  have he := map_primeToResidual_of_surjective 3 q hq
  change (A.subgroupOf M).map f = _
  rw [←inclusion_range hAM,←MonoidHom.range_comp]
  change a.range = _
  rw [←he,map_map]
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    obtain ⟨z,hz,hzy⟩ := y.property
    refine ⟨z,hz,?_⟩
    change (q z : internalActionImage M V hn) = f (inclusion hAM y)
    exact (hcoord z).trans (congrArg f (Subtype.ext hzy))
  · rintro ⟨z,hz,rfl⟩
    exact ⟨⟨z,mem_map_of_mem C.subtype hz⟩,(hcoord z).symm⟩

/-- The canonical cubic preimage lies in the partner by original 15.1.14,
and its displacement is the same original sixteen-element moving support. -/
theorem ThompsonPair.cubic_actor_in_partner_of_quotient_fifteen
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJambient : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V h.normalized) (Jhat (imageRepresentation M V h.normalized)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) h.normalized c d)
    (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict ⊓
        Jhat (imageRepresentation M V h.normalized))
    (hfive : s.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    let Z := thompsonPlane T V (c.ambientFactor d s.first).space
    let C := M ⊓ centralizer (Z : Set G)
    let A := (primeToResidual 3 C).map C.subtype
    letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
    Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 15 →
      A ≤ M ⊓ Mc ∧ A ≤ (pResidual 2 C).map C.subtype ∧
      Nat.card ((A.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict) = 3 ∧
      ¬ A ≤ centralizer (V : Set G) ∧
      ⁅V,A⁆ = plane V (c.ambientFactor d s.second).space := by
  intro Z C A h15
  let ρ := imageRepresentation M V h.normalized
  let f : M →* internalActionImage M V h.normalized :=
    (actionHom M V h.normalized).rangeRestrict
  let J := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ J
  let K := subspaceKernel ρ W ⊤
  have hW : plane V W = Z := plane_thompson_intersection hM.1.2 h.normalized _
  have hi : (A.subgroupOf M).map f = (primeToResidual 3 K).map K.subtype := by
    have hh := cubic_action_image M V h.normalized W
    rwa [hW] at hh
  have hK15 : Nat.card (pResidual 2 K) = 15 := by
    let qcard (Z' : Subgroup G) : ℕ :=
      let C' := M ⊓ centralizer (Z' : Set G)
      letI := caseI_module_centralizer_normal (Z1 := Z') h.normalized
      Nat.card (pResidual 2 (C' ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C'))
    have hh : qcard (plane V W) = Nat.card (pResidual 2 K) :=
      ExtraspecialMarker.residual_card M V h.normalized W
    rw [hW] at hh
    exact hh.symm.trans h15
  obtain ⟨hcard,hcentral⟩ := s.full_image_cubic_residual_of_fifteen
    hM.1.2 h.normalized c d π hp hs hJ hfive hK15
  have hAM : A ≤ M := (map_subtype_le _).trans inf_le_left
  have hAJ : (A.subgroupOf M).map f ≤ centralizer (J : Set _) := by
    rw [hi]
    have hJJ : J ≤ Jhat ρ := by
      change ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V h.normalized).rangeRestrict ≤ Jhat ρ
      rw [hJ]
      exact inf_le_right
    exact hcentral.trans (centralizer_le hJJ)
  have hnorm : (A.subgroupOf M).map f ≤ subspaceStabilizer ρ (fixedSpace ρ J) :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ _ J
      (commutator_eq_bot_iff_le_centralizer.mpr hAJ)
  have hAVE : A ≤ normalizer (thompsonFixed T V : Set G) := by
    rw [←plane_thompson_image hM.1.2 h.normalized]
    apply le_normalizer_iff.mpr
    rintro a ha y ⟨v,hv,rfl⟩
    let aM : M := ⟨a,hAM ha⟩
    refine ⟨(actionHom M V h.normalized aM) v,?_,rfl⟩
    exact (hnorm (mem_map_of_mem f (show aM ∈ A.subgroupOf M from ha))
      (Additive.ofMul v)).mpr hv
  have hAR : A ≤ (pResidual 2 C).map C.subtype := by
    apply map_mono
    apply primeToResidual_le
    rw [index_eq_card]
    obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := C) 2).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have himcard : Nat.card ((A.subgroupOf M).map f) = 3 := by
    rw [hi,card_map_of_injective K.subtype_injective,hcard]
  have hnoncentral : ¬ A ≤ centralizer (V : Set G) := by
    intro hAC
    have hb : (A.subgroupOf M).map f = ⊥ := by
      apply bot_unique
      rintro _ ⟨a,ha,rfl⟩
      apply mem_bot.mpr
      apply Subtype.ext
      change a ∈ (actionHom M V h.normalized).ker
      rw [actionHom_ker]
      exact hAC ha
    rw [hb,card_bot] at himcard
    omega
  refine ⟨le_inf hAM (hAVE.trans
    (h.thompsonFixed_normalizers hG T hM hJambient hu hres).2.1),hAR,himcard,hnoncentral,?_⟩
  let Y := (primeToResidual 5 C).map C.subtype
  have hYC : Y ≤ C := map_subtype_le _
  have hCA : C ≤ normalizer (A : Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 C))
  have hYN : Y ≤ normalizer ((⁅V,A⁆ : Subgroup G) : Set G) := by
    intro y hy
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (h.normalized (hYC hy).1),
      mem_normalizer_iff_map_conj_eq.mp (hCA (hYC hy))]
  have hgeo := s.full_residual_geometry hM.1.2 h.normalized c d π hp hs hJ
  have hmovele : ⁅V,A⁆ ≤ plane V (c.ambientFactor d s.second).space :=
    (commutator_mono le_rfl hAR).trans hgeo.2.1.le
  rcases s.quintic_actor_irreducible hM.1.2 h.normalized c d π hp hs hJ hfive
      ⁅V,A⁆ hmovele hYN with hzero | hfull
  · exact (hnoncentral (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hzero))).elim
  · exact hfull

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The original eight-dimensional source produces the canonical cubic actor
if the faithful marked residual has order fifteen. Its nontrivial image and
placement in the partner retain the same marking and both original supports. -/
theorem PreparedChosenModule.decomposable_fifteen_cubicActor_of_dimension_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 8)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    letI := h.elementary
    ∃ (U : Submodule (ZMod 2) (Additive V))
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d),
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π ∧
      cubicRatio (imageRepresentation M V h.normalized) = 2 ∧
      let Z := DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space
      let C := M ⊓ centralizer (Z : Set G)
      let R := (pResidual 2 C).map C.subtype
      letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
      let Q := pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)
      IsCyclic Q ∧
      (Nat.card Q = s.prime ∨ (s.prime = 5 ∧ Nat.card Q = 15)) ∧
      V ⊓ centralizer (R : Set G) =
        DecomposableMarker.plane V (c.ambientFactor d s.first).space ∧
      ⁅V,R⁆ = DecomposableMarker.plane V (c.ambientFactor d s.second).space ∧
      Nat.card (V ⊓ centralizer (R : Set G) : Subgroup G) = 16 ∧
      Nat.card (⁅V,R⁆ : Subgroup G) = 16 ∧
      (Nat.card Q = 15 →
        let A := (primeToResidual 3 C).map C.subtype
        A ≤ M ⊓ Mc ∧ A ≤ R ∧
        Nat.card ((A.subgroupOf M).map (actionHom M V h.normalized).rangeRestrict) = 3 ∧
        ¬ A ≤ centralizer (V : Set G) ∧
        ⁅V,A⁆ = DecomposableMarker.plane V (c.ambientFactor d s.second).space) := by
  subst V
  let := h.elementary
  obtain ⟨U,c,d,π,hd,_,_,hperm,hcases⟩ := ha
  rcases hcases with h9 | hex | ⟨hdec,hq⟩
  · obtain ⟨l,_,hfour,_⟩ := h9
    omega
  · obtain ⟨l,_,_,_,_,_,hsix,_⟩ := hex
    omega
  · have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π
      (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2)
      (Or.inr (Or.inr (Or.inl hdec)))
    have hstar := (h.thompson_actors T hM.1.2 hq
      (fun E hE => hE.rank_le_of_primeRank_le hr)).1
    have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
    have he := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
      hm hstar c d π (fun g k => (hperm g k).2.1) hdec).1
    obtain ⟨s⟩ := DecomposableMarker.thompsonPair_of_image hM.1.2 h.normalized c d π
      (fun g k => (hperm g k).2.2) hdec hq he
    refine ⟨U,c,d,π,s,hdec,hq,?_⟩
    have hgeo := s.full_residual_geometry hM.1.2 h.normalized c d π
      (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he
    rcases s.prime_cases with hthree | hfive
    · have hc := s.full_quotient_residual_card_of_prime_three hG T hM h.normalized c d π
        (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hthree
      refine ⟨isCyclic_of_prime_card (hc.trans hthree),Or.inl hc,
        hgeo.1,hgeo.2.1,hgeo.2.2.1,hgeo.2.2.2,?_⟩
      intro h15
      rw [hc,hthree] at h15
      norm_num at h15
    · obtain ⟨hcyc,hcard⟩ := s.full_quotient_residual_of_prime_five hM.1.2 h.normalized c d π
        (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hfive
      refine ⟨hcyc,hcard.elim (fun hc => Or.inl (hc.trans hfive.symm))
        (fun hc => Or.inr ⟨hfive,hc⟩),hgeo.1,hgeo.2.1,hgeo.2.2.1,hgeo.2.2.2,?_⟩
      exact s.cubic_actor_in_partner_of_quotient_fifteen hG T hM hJ hu h c d π
        (fun g k => (hperm g k).2.1) (fun g k => (hperm g k).2.2) he hfive hres


end CFSG.Quasithin.Chapter15.Section01

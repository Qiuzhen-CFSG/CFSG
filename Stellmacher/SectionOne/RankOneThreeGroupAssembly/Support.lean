module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaNormalization
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaCounting

/-!
# Support of Sylow involutions on omega factors

An involution's support records its nontrivial factor characters. Local coordinates add exactly one support factor, and full factor commutators identify the global cyclic commutator with the join of the supported factors.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

@[expose] public noncomputable def omegaSupport
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S : Subgroup G)
    (hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      S ≤ Subgroup.normalizer F)
    (s : S) : Finset (Subgroup G) := by
  classical
  exact (oneOmegaFinset (G := G) (V := V)).filter fun F =>
    ∃ hF : oneOmega (G := G) (V := V) F,
      omegaFactorCharacter S F (hnorm F hF) s ≠ 1

/-- Choose the order-two `oneAmax` subgroup in the source so that the number
of omega coordinates it moves is minimal.  We select its unique nonidentity
element, avoiding a separate choice of generators for order-two subgroups. -/
public theorem exists_minimal_oneAmax_omegaSupport
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : IsElementaryAbelian 2 (S : Subgroup G))
    (hScard : 4 ≤ Nat.card (S : Subgroup G))
    (hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      (S : Subgroup G) ≤ Subgroup.normalizer F) :
    ∃ a : S,
      a ≠ 1 ∧
      oneAmax (G := G) (V := V) (S : Subgroup G)
        (Subgroup.zpowers (a : G)) ∧
      Nat.card (Subgroup.zpowers (a : G)) = 2 ∧
      ∀ x : S, x ≠ 1 →
        oneAmax (G := G) (V := V) (S : Subgroup G)
          (Subgroup.zpowers (x : G)) →
        (omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm a).card ≤
          (omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm x).card := by
  classical
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hScard
    norm_num at hScard
  obtain ⟨A, hAmax, hAcard⟩ :=
    lemma_one_five_exists_oneAmax_card_two_relative
      h S (S : Subgroup G) le_rfl hS hSne
  obtain ⟨aA, haAne, _haAuniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hAcard
  let a : S := ⟨(aA : G), hAmax.1 aA.property⟩
  have hane : a ≠ 1 := by
    intro ha
    apply haAne
    apply Subtype.ext
    exact congrArg (fun z : S => (z : G)) ha
  have hAeq : A = Subgroup.zpowers (a : G) :=
    subgroup_card_two_eq_zpowers_of_mem_ne_one A hAcard aA.property
      (fun ha => haAne (Subtype.ext ha))
  let _ : Fintype S := Fintype.ofFinite S
  let C : Finset S := Finset.univ.filter fun x : S =>
    x ≠ 1 ∧ oneAmax (G := G) (V := V) (S : Subgroup G)
      (Subgroup.zpowers (x : G))
  have haC : a ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hane, hAeq ▸ hAmax⟩
  obtain ⟨b, hbC, hbmin⟩ := Finset.exists_min_image C
    (fun x : S =>
      (omegaSupport (G := G) (V := V) (S : Subgroup G) hnorm x).card)
    ⟨a, haC⟩
  have hb := (Finset.mem_filter.mp hbC).2
  have hbcard : Nat.card (Subgroup.zpowers (b : G)) = 2 := by
    have hbpow : (b : G) ^ 2 = 1 := by
      exact congrArg Subtype.val
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (S : Subgroup G)) b)
    rw [Nat.card_zpowers, orderOf_eq_prime hbpow]
    exact fun hb1 => hb.1 (Subtype.ext hb1)
  refine ⟨b, hb.1, hb.2, hbcard, ?_⟩
  intro x hxne hxmax
  exact hbmin x
    (Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨hxne, hxmax⟩⟩)

public theorem omegaSupport_subset_oneOmegaFinset
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S : Subgroup G)
    (hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      S ≤ Subgroup.normalizer F)
    (s : S) :
    omegaSupport (G := G) (V := V) S hnorm s ⊆
      oneOmegaFinset (G := G) (V := V) := by
  classical
  change (oneOmegaFinset (G := G) (V := V)).filter _ ⊆
    oneOmegaFinset (G := G) (V := V)
  exact Finset.filter_subset _ _

public theorem mem_omegaSupport_iff
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S : Subgroup G)
    (hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      S ≤ Subgroup.normalizer F)
    (s : S) (F : Subgroup G)
    (hF : oneOmega (G := G) (V := V) F) :
    F ∈ omegaSupport (G := G) (V := V) S hnorm s ↔
      omegaFactorCharacter S F (hnorm F hF) s ≠ 1 := by
  classical
  rw [omegaSupport, Finset.mem_filter,
    mem_oneOmegaFinset_iff (G := G) (V := V) F]
  constructor
  · rintro ⟨_, hF', hs⟩
    have heq : hF' = hF := Subsingleton.elim _ _
    simpa only [heq] using hs
  · intro hs
    exact ⟨hF, hF, hs⟩

public theorem omegaFactorCharacter_eq_one_iff_mem_centralizer
    {G : Type u} [Group G] (S F : Subgroup G)
    (hSF : S ≤ Subgroup.normalizer F) (s : S) :
    omegaFactorCharacter S F hSF s = 1 ↔
      (s : G) ∈ Subgroup.centralizer (F : Set G) := by
  change F.normalizerMonoidHom (Subgroup.inclusion hSF s) = 1 ↔ _
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
  rfl

public theorem mem_omegaSupport_iff_not_mem_centralizer
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S : Subgroup G)
    (hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      S ≤ Subgroup.normalizer F)
    (s : S) (F : Subgroup G)
    (hF : oneOmega (G := G) (V := V) F) :
    F ∈ omegaSupport (G := G) (V := V) S hnorm s ↔
      (s : G) ∉ Subgroup.centralizer (F : Set G) := by
  rw [mem_omegaSupport_iff S hnorm s F hF, ne_eq,
    omegaFactorCharacter_eq_one_iff_mem_centralizer]

/-- For an omega factor normalized by `S`, its commutator with the cyclic
subgroup generated by `s` is the whole factor exactly when `s` belongs to
the support. -/
public theorem commutator_oneOmega_zpowers_eq_self_of_mem_support
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S : Subgroup G)
    (hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      S ≤ Subgroup.normalizer F)
    (s : S) (F : Subgroup G)
    (hF : oneOmega (G := G) (V := V) F)
    (hmem : F ∈ omegaSupport (G := G) (V := V) S hnorm s) :
    ⁅F, Subgroup.zpowers (s : G)⁆ = F := by
  have hsNorm : Subgroup.zpowers (s : G) ≤ Subgroup.normalizer F := by
    rw [Subgroup.zpowers_le]
    exact hnorm F hF s.property
  have hcommLe : ⁅F, Subgroup.zpowers (s : G)⁆ ≤ F :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hsNorm)
  have hcommNe : ⁅F, Subgroup.zpowers (s : G)⁆ ≠ ⊥ := by
    intro hbot
    have hcent : Subgroup.zpowers (s : G) ≤
        Subgroup.centralizer (F : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
        Subgroup.commutator_comm]
      exact hbot
    exact (mem_omegaSupport_iff_not_mem_centralizer S hnorm s F hF).mp hmem
      (Subgroup.zpowers_le.mp hcent)
  let I : Subgroup F :=
    (⁅F, Subgroup.zpowers (s : G)⁆).subgroupOf F
  let hprime : Fact (Nat.card F).Prime := ⟨hF.2.1 ▸ Nat.prime_three⟩
  let _ : Fact (Nat.card F).Prime := hprime
  rcases I.eq_bot_or_eq_top_of_prime_card with hI | hI
  · exfalso
    apply hcommNe
    calc
      ⁅F, Subgroup.zpowers (s : G)⁆ = I.map F.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hcommLe).symm
      _ = ⊥ := by rw [hI, Subgroup.map_bot]
  · calc
      ⁅F, Subgroup.zpowers (s : G)⁆ = I.map F.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hcommLe).symm
      _ = F := by
        rw [hI, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

public theorem commutator_oneOmega_zpowers_eq_bot_of_not_mem_support
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S : Subgroup G)
    (hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      S ≤ Subgroup.normalizer F)
    (s : S) (F : Subgroup G)
    (hF : oneOmega (G := G) (V := V) F)
    (hmem : F ∉ omegaSupport (G := G) (V := V) S hnorm s) :
    ⁅F, Subgroup.zpowers (s : G)⁆ = ⊥ := by
  have hsCent : (s : G) ∈ Subgroup.centralizer (F : Set G) := by
    by_contra hs
    exact hmem ((mem_omegaSupport_iff_not_mem_centralizer
      S hnorm s F hF).mpr hs)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
  exact hsCent

/-- A coordinate outside the support of `s` lies in the local commutator
`[C_W(⟨s⟩),S]`.  The reverse inclusion needed here is precisely where
the global hypothesis `W=[W,S]` enters: it forces every prime-order direct
coordinate to have full commutator with `S`. -/
public theorem oneOmega_le_local_commutator_of_not_mem_support
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G)
    (hnorm : ∀ K : Subgroup G, oneOmega (G := G) (V := V) K →
      S ≤ Subgroup.normalizer K)
    (hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V))
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (hW : oddCore G = ⁅oddCore G, S⁆)
    (s : S) (F : Subgroup G)
    (hF : oneOmega (G := G) (V := V) F)
    (hnot : F ∉ omegaSupport (G := G) (V := V) S hnorm s) :
    F ≤ ⁅oddCore G ⊓
      Subgroup.centralizer (Subgroup.zpowers (s : G) : Set G), S⁆ := by
  have hcommBot : ⁅F, Subgroup.zpowers (s : G)⁆ = ⊥ :=
    commutator_oneOmega_zpowers_eq_bot_of_not_mem_support
      S hnorm s F hF hnot
  have hFcent : F ≤
      Subgroup.centralizer (Subgroup.zpowers (s : G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
  have hFle : F ≤ oddCore G ⊓
      Subgroup.centralizer (Subgroup.zpowers (s : G) : Set G) :=
    le_inf hF.1 hFcent
  rw [← commutator_oneOmega_sylow_eq_self
    S hnorm hcoreEq hdecomp hW F hF]
  exact Subgroup.commutator_mono hFle le_rfl

public theorem oneOmega_not_mem_support_of_le_local_commutator
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnorm : ∀ K : Subgroup G, oneOmega (G := G) (V := V) K →
      S ≤ Subgroup.normalizer K)
    (a : S) (F : Subgroup G)
    (hF : oneOmega (G := G) (V := V) F)
    (hFle : F ≤ ⁅oddCore G ⊓
      Subgroup.centralizer (Subgroup.zpowers (a : G) : Set G), S⁆) :
    F ∉ omegaSupport (G := G) (V := V) S hnorm a := by
  have hFcent : F ≤
      Subgroup.centralizer (Subgroup.zpowers (a : G) : Set G) :=
    hFle.trans (local_commutator_le_centralizer
      S (Subgroup.zpowers (a : G)) hS
      ((Subgroup.zpowers_le).mpr a.property))
  have hbot : ⁅F, Subgroup.zpowers (a : G)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hFcent
  intro hmem
  have hfull := commutator_oneOmega_zpowers_eq_self_of_mem_support
    S hnorm a F hF hmem
  have hFbot : F = ⊥ := hfull.symm.trans hbot
  have := hF.2.1
  rw [hFbot] at this
  norm_num at this

/-- If a local order-four coordinate changes one omega character `F` and no
other character outside the old support, then the new support differs from
the old one by exactly that coordinate.  The containment is obtained from
the source equality `[W_A,A_i]=F_i`. -/
public theorem support_sdiff_eq_singleton_of_local_coordinate
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    [DecidableEq (Subgroup G)]
    (S : Subgroup G)
    (hnorm : ∀ K : Subgroup G, oneOmega (G := G) (V := V) K →
      S ≤ Subgroup.normalizer K)
    (hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V))
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (hW : oddCore G = ⁅oddCore G, S⁆)
    (a x : S) (Aᵢ F : Subgroup G)
    (hxAᵢ : (x : G) ∈ Aᵢ)
    (hF : oneOmega (G := G) (V := V) F)
    (hFnotA : F ∉ omegaSupport (G := G) (V := V) S hnorm a)
    (hFx : ⁅F, Subgroup.zpowers (x : G)⁆ = F)
    (hcoordinate :
      ⁅⁅oddCore G ⊓
          Subgroup.centralizer (Subgroup.zpowers (a : G) : Set G), S⁆,
        Aᵢ⁆ = F) :
    (omegaSupport (G := G) (V := V) S hnorm x \
        omegaSupport (G := G) (V := V) S hnorm a) = {F} := by
  classical
  have hFmemX : F ∈ omegaSupport (G := G) (V := V) S hnorm x := by
    by_contra hnot
    have hbot := commutator_oneOmega_zpowers_eq_bot_of_not_mem_support
      S hnorm x F hF hnot
    have hFne : F ≠ ⊥ := by
      intro hbotF
      have := hF.2.1
      rw [hbotF] at this
      norm_num at this
    exact hFne (hFx.symm.trans hbot)
  ext K
  simp only [Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨hKx, hKnotA⟩
    have hKomega : oneOmega (G := G) (V := V) K :=
      (mem_oneOmegaFinset_iff (G := G) (V := V) K).mp
        (omegaSupport_subset_oneOmegaFinset S hnorm x hKx)
    have hKleLocal := oneOmega_le_local_commutator_of_not_mem_support
      S hnorm hcoreEq hdecomp hW a K hKomega hKnotA
    have hKcomm := commutator_oneOmega_zpowers_eq_self_of_mem_support
      S hnorm x K hKomega hKx
    have hKleF : K ≤ F := by
      rw [← hKcomm]
      exact (Subgroup.commutator_mono hKleLocal
        ((Subgroup.zpowers_le).mpr hxAᵢ)).trans
        hcoordinate.le
    exact Subgroup.eq_of_le_of_card_ge hKleF (by
      rw [hF.2.1, hKomega.2.1])
  · rintro rfl
    exact ⟨hFmemX, hFnotA⟩

/-- The commutator of the odd core with a cyclic subgroup of `S` is exactly
the join of the omega factors in the element's support. -/
public theorem commutator_oddCore_zpowers_eq_iSup_support
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S : Subgroup G)
    (hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      S ≤ Subgroup.normalizer F)
    (hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V))
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (s : S) :
    ⁅oddCore G, Subgroup.zpowers (s : G)⁆ =
      ⨆ F : {F : Subgroup G //
        F ∈ omegaSupport (G := G) (V := V) S hnorm s},
        (F : Subgroup G) := by
  classical
  let W : Subgroup G := oddCore G
  let B : Subgroup G := Subgroup.zpowers (s : G)
  let H : Subgroup G := W ⊔ B
  let Ω := {F : Subgroup G //
    F ∈ oneOmegaFinset (G := G) (V := V)}
  let SuppIndex := {F : Subgroup G //
    F ∈ omegaSupport (G := G) (V := V) S hnorm s}
  let KH : Ω → Subgroup H := fun F => (F : Subgroup G).subgroupOf H
  let FH : SuppIndex → Subgroup H := fun F => (F : Subgroup G).subgroupOf H
  let N : Subgroup H := ⨆ F : SuppIndex, FH F
  have hWcomm : IsMulCommutative W := by
    change IsMulCommutative (oddCore G)
    rw [hcoreEq]
    exact oneOmegaGenerated_isMulCommutative hdecomp
  have hFomega (F : Ω) : oneOmega (G := G) (V := V) (F : Subgroup G) :=
    (mem_oneOmegaFinset_iff (G := G) (V := V) (F : Subgroup G)).mp F.property
  have hFleW (F : Ω) : (F : Subgroup G) ≤ W := by
    change (F : Subgroup G) ≤ oddCore G
    exact (hFomega F).1
  have hBleS : B ≤ S := by
    change Subgroup.zpowers (s : G) ≤ S
    rw [Subgroup.zpowers_le]
    exact s.property
  have hFleH (F : Ω) : (F : Subgroup G) ≤ H :=
    (hFleW F).trans le_sup_left
  have hFsOmega (F : SuppIndex) : oneOmega (G := G) (V := V) (F : Subgroup G) := by
    exact (mem_oneOmegaFinset_iff (G := G) (V := V) (F : Subgroup G)).mp
      (omegaSupport_subset_oneOmegaFinset S hnorm s F.property)
  have hFsleW (F : SuppIndex) : (F : Subgroup G) ≤ W := by
    change (F : Subgroup G) ≤ oddCore G
    exact (hFsOmega F).1
  have hFsleH (F : SuppIndex) : (F : Subgroup G) ≤ H :=
    (hFsleW F).trans le_sup_left
  have hFHnormal (F : SuppIndex) : (FH F).Normal := by
    have hWnorm : W ≤ Subgroup.normalizer (F : Subgroup G) := by
      exact ((Subgroup.le_centralizer_iff).mpr
        ((hFsleW F).trans
          (Subgroup.le_centralizer_iff_isMulCommutative.mpr hWcomm))).trans
        (Subgroup.centralizer_le_normalizer ((F : Subgroup G) : Set G))
    have hBnorm : B ≤ Subgroup.normalizer (F : Subgroup G) :=
      hBleS.trans (hnorm (F : Subgroup G) (hFsOmega F))
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hFsleH F)).2
      (sup_le hWnorm hBnorm)
  have hNnormal : N.Normal := by
    dsimp only [N]
    simpa using Subgroup.biSup_normal Set.univ FH (fun F _ => hFHnormal F)
  let _ : N.Normal := hNnormal
  have hgenW : W = ⨆ F : Ω, (F : Subgroup G) := by
    calc
      W = oneOmegaGenerated (G := G) (V := V) := hcoreEq
      _ = ⨆ F : Ω, (F : Subgroup G) := hdecomp.part_a.1
  have hgenKH : W.subgroupOf H = ⨆ F : Ω, KH F := by
    apply Subgroup.map_injective H.subtype_injective
    calc
      (W.subgroupOf H).map H.subtype = W :=
        Subgroup.map_subgroupOf_eq_of_le le_sup_left
      _ = ⨆ F : Ω, (F : Subgroup G) := hgenW
      _ = ⨆ F : Ω, (KH F).map H.subtype := by
        congr 1
        funext F
        exact (Subgroup.map_subgroupOf_eq_of_le (hFleH F)).symm
      _ = (⨆ F : Ω, KH F).map H.subtype := by rw [Subgroup.map_iSup]
  have hlocalComm (F : Ω) : ⁅KH F, B.subgroupOf H⁆ ≤ N := by
    by_cases hFsupp : (F : Subgroup G) ∈
        omegaSupport (G := G) (V := V) S hnorm s
    · let Fs : SuppIndex := ⟨(F : Subgroup G), hFsupp⟩
      intro x hx
      have hxmap : ((x : H) : G) ∈
          (⁅KH F, B.subgroupOf H⁆).map H.subtype := ⟨x, hx, rfl⟩
      rw [commutator_subgroupOf_map_eq (S := H) (H := B)
        (R := (F : Subgroup G)) le_sup_right (hFleH F),
        commutator_oneOmega_zpowers_eq_self_of_mem_support
          S hnorm s (F : Subgroup G) (hFomega F) hFsupp] at hxmap
      exact le_iSup FH Fs hxmap
    · have hbot : ⁅(F : Subgroup G), B⁆ = ⊥ :=
        commutator_oneOmega_zpowers_eq_bot_of_not_mem_support
          S hnorm s (F : Subgroup G) (hFomega F) hFsupp
      have hsubbot : ⁅KH F, B.subgroupOf H⁆ = ⊥ := by
        apply Subgroup.map_injective H.subtype_injective
        rw [commutator_subgroupOf_map_eq (S := H) (H := B)
          (R := (F : Subgroup G)) le_sup_right (hFleH F), hbot,
          Subgroup.map_bot]
      rw [hsubbot]
      exact bot_le
  have hcommSub : ⁅W.subgroupOf H, B.subgroupOf H⁆ ≤ N :=
    commutator_le_normal_of_eq_iSup
      (W.subgroupOf H) (B.subgroupOf H) N KH hgenKH hlocalComm
  apply le_antisymm
  · have hmapLe :
        (⁅W.subgroupOf H, B.subgroupOf H⁆).map H.subtype ≤
          N.map H.subtype :=
      Subgroup.map_mono hcommSub
    have hNmap : N.map H.subtype =
        ⨆ F : SuppIndex, (F : Subgroup G) := by
      calc
        N.map H.subtype = ⨆ F : SuppIndex, (FH F).map H.subtype := by
          dsimp only [N]
          rw [Subgroup.map_iSup]
        _ = ⨆ F : SuppIndex, (F : Subgroup G) := by
          congr 1
          funext F
          exact Subgroup.map_subgroupOf_eq_of_le (hFsleH F)
    rw [commutator_subgroupOf_map_eq (S := H) (H := B) (R := W)
      le_sup_right le_sup_left, hNmap] at hmapLe
    exact hmapLe
  · refine iSup_le ?_
    intro F
    have hterm := commutator_oneOmega_zpowers_eq_self_of_mem_support
      S hnorm s (F : Subgroup G) (hFsOmega F) F.property
    rw [← hterm]
    exact Subgroup.commutator_mono (hFsleW F) le_rfl

end Stellmacher.SectionOne.RankOneThreeGroupAssembly

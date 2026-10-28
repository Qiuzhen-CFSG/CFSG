module

public import Stellmacher.SectionFiveToSeven.Defs

/-!
# The minimal bad subgroup in Stellmacher (5.2)

Starting from a 2-local overgroup in which `K` is not subnormal, this
module constructs the subgroup `M` satisfying assertions (4)--(6) in the
proof of Stellmacher (5.2).  First choose a maximal bad 2-local overgroup
`L`.  Its nontrivial 2-core normalizer is another bad 2-local overgroup,
so maximality gives `L=N_H(O₂(L))`.  The assumed internal
characteristic-2 property of `L` therefore yields the ambient inequality
`C_H(O₂(L))≤O₂(L)`.

Next choose a minimal bad subgroup `M≤L` containing `B K O₂(L)`.
Normality gives `O₂(L)≤O₂(M)`, so ambient self-centralization descends to
`O₂(M)`; solvability descends from `L`, and minimality is exactly the
proper-overgroup assertion (6).  The returned structure records only the
facts used by the remaining quotient argument.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), proof of (5.2), pp. 28--29, assertions (4)--(6).
-/

namespace Stellmacher.SectionsFiveToSeven

universe u

/-- The properties (4)--(6) retained from the minimal bad subgroup. -/
public structure FiveTwoMinimalBadData
    {G : Type u} [Group G] (B K M : Subgroup G) : Prop where
  sup_le : B ⊔ K ≤ M
  not_subnormal : ¬ SubnormalIn K M
  solvable : Group.IsSolvable M
  core_ne : twoCoreIn M ≠ ⊥
  centralizer_core_le :
    Subgroup.centralizer (twoCoreIn M : Set G) ≤ twoCoreIn M
  proper_subnormal : ∀ X : Subgroup G,
    (B ⊔ K) ⊔ twoCoreIn M ≤ X → X < M → SubnormalIn K X

private theorem twoCoreIn_le_52bad
    {G : Type u} [Group G] (P : Subgroup G) : twoCoreIn P ≤ P :=
  Subgroup.map_subtype_le _

private theorem twoCoreIn_isPGroup_52bad
    {G : Type u} [Group G] (P : Subgroup G) : IsPGroup 2 (twoCoreIn P) :=
  (pCore_isPGroup (p := 2) (G := P)).map P.subtype

private theorem twoCoreIn_normal_52bad
    {G : Type u} [Group G] (P : Subgroup G) :
    ((twoCoreIn P).subgroupOf P).Normal := by
  change (Subgroup.comap P.subtype ((pCore 2 P).map P.subtype)).Normal
  rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  infer_instance

private theorem le_normalizer_twoCoreIn_52bad
    {G : Type u} [Group G] (P : Subgroup G) :
    P ≤ Subgroup.normalizer (twoCoreIn P : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (twoCoreIn_le_52bad P)).mp
    (twoCoreIn_normal_52bad P)

private theorem normal_twoSubgroup_le_twoCoreIn_52bad
    {G : Type u} [Group G] (Q P : Subgroup G)
    (hQP : Q ≤ P) (hQp : IsPGroup 2 Q)
    (hQnormal : (Q.subgroupOf P).Normal) : Q ≤ twoCoreIn P := by
  have hQpP : IsPGroup 2 (Q.subgroupOf P) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have hle : Q.subgroupOf P ≤ pCore 2 P := le_sSup ⟨hQnormal, hQpP⟩
  calc
    Q = (Q.subgroupOf P).map P.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQP).symm
    _ ≤ (pCore 2 P).map P.subtype := Subgroup.map_mono hle
    _ = twoCoreIn P := rfl

private theorem subnormalIn_restrict_52bad
    {G : Type u} [Group G] {A B C : Subgroup G}
    (hAB : A ≤ B) (hBC : B ≤ C) (hsub : SubnormalIn A C) :
    SubnormalIn A B := by
  let BC : Subgroup C := B.subgroupOf C
  let e : BC ≃* B := Subgroup.subgroupOfEquivOfLe hBC
  have hsubBC :
      ((A.subgroupOf C).subgroupOf BC).IsSubnormal := hsub.2.subgroupOf
  have hmapped := Subgroup.IsSubnormal.map
    (f := e.toMonoidHom) e.surjective hsubBC
  have hmap : ((A.subgroupOf C).subgroupOf BC).map e.toMonoidHom =
      A.subgroupOf B := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro ha
      let xC : C := ⟨a, hBC (hAB ha)⟩
      let xBC : BC := ⟨xC, hAB ha⟩
      exact ⟨xBC, ha, rfl⟩
  rw [hmap] at hmapped
  exact ⟨hAB, hmapped⟩

/-- Every bad 2-local overgroup contains a solvable minimal bad subgroup
with nontrivial ambient self-centralizing 2-core. -/
public theorem exists_five_two_minimal_bad
    {G : Type u} [Group G] [Finite G]
    (B K U : Subgroup G)
    (hUlocal : IsTwoLocal U) (hBKU : B ⊔ K ≤ U)
    (hbadU : ¬ SubnormalIn K U)
    (hlocal : ∀ L : Subgroup G, IsTwoLocal L → B ≤ L →
      Group.IsSolvable L ∧ Stellmacher.IsCharacteristicTwoType L) :
    ∃ M : Subgroup G, FiveTwoMinimalBadData B K M := by
  classical
  let Bad : Set (Subgroup G) :=
    {L | U ≤ L ∧ IsTwoLocal L ∧ ¬ SubnormalIn K L}
  have hBadU : U ∈ Bad := ⟨le_rfl, hUlocal, hbadU⟩
  obtain ⟨L, hLmax⟩ := (Set.toFinite Bad).exists_maximal ⟨U, hBadU⟩
  have hUL : U ≤ L := hLmax.1.1
  have hLlocal : IsTwoLocal L := hLmax.1.2.1
  have hbadL : ¬ SubnormalIn K L := hLmax.1.2.2
  have hBL : B ≤ L := le_sup_left.trans (hBKU.trans hUL)
  have hKL : K ≤ L := le_sup_right.trans (hBKU.trans hUL)
  obtain ⟨hLsolv, hLchar⟩ := hlocal L hLlocal hBL
  let OL : Subgroup G := twoCoreIn L
  have hOLne : OL ≠ ⊥ := by
    rcases hLlocal with ⟨Q, hQne, hQp, hLeq⟩
    have hQL : Q ≤ L := by rw [hLeq]; exact Q.le_normalizer
    have hQnormalL : (Q.subgroupOf L).Normal := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQL).mpr
      rw [hLeq]
    have hQOL : Q ≤ OL := normal_twoSubgroup_le_twoCoreIn_52bad
      Q L hQL hQp hQnormalL
    intro hbot
    exact hQne (le_bot_iff.mp (hQOL.trans (le_of_eq hbot)))
  let NL : Subgroup G := Subgroup.normalizer (OL : Set G)
  have hLNL : L ≤ NL := le_normalizer_twoCoreIn_52bad L
  have hNLlocal : IsTwoLocal NL :=
    ⟨OL, hOLne, twoCoreIn_isPGroup_52bad L, rfl⟩
  have hUNL : U ≤ NL := hUL.trans hLNL
  have hbadNL : ¬ SubnormalIn K NL := by
    intro hsub
    exact hbadL (subnormalIn_restrict_52bad hKL hLNL hsub)
  have hNLBad : NL ∈ Bad := ⟨hUNL, hNLlocal, hbadNL⟩
  have hNLL : NL ≤ L := hLmax.2 hNLBad hLNL
  have hLeqNL : L = NL := le_antisymm hLNL hNLL
  have hCLcore : Subgroup.centralizer (OL : Set G) ≤ OL := by
    intro x hx
    have hxL : x ∈ L := by
      rw [hLeqNL]
      exact Subgroup.centralizer_le_normalizer (OL : Set G) hx
    let xL : L := ⟨x, hxL⟩
    have hxcent : xL ∈ Subgroup.centralizer (pCore 2 L : Set L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyOL : (y : G) ∈ OL :=
        Subgroup.mem_map_of_mem L.subtype hy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx (y : G) hyOL)
    exact Subgroup.mem_map_of_mem L.subtype (hLchar hxcent)
  let SmallBad : Set (Subgroup G) :=
    {X | X ≤ L ∧ (B ⊔ K) ⊔ OL ≤ X ∧ ¬ SubnormalIn K X}
  have hLSmall : L ∈ SmallBad := by
    exact ⟨le_rfl, sup_le (sup_le hBL hKL) (twoCoreIn_le_52bad L), hbadL⟩
  obtain ⟨M, hMmin⟩ := (Set.toFinite SmallBad).exists_minimal ⟨L, hLSmall⟩
  have hML : M ≤ L := hMmin.1.1
  have hBKOLM : (B ⊔ K) ⊔ OL ≤ M := hMmin.1.2.1
  have hbadM : ¬ SubnormalIn K M := hMmin.1.2.2
  have hBKM : B ⊔ K ≤ M := le_sup_left.trans hBKOLM
  have hOLM : OL ≤ M := le_sup_right.trans hBKOLM
  have hOLnormalM : (OL.subgroupOf M).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hOLM).mpr
    exact hML.trans (le_normalizer_twoCoreIn_52bad L)
  have hOLOM : OL ≤ twoCoreIn M :=
    normal_twoSubgroup_le_twoCoreIn_52bad OL M hOLM
      (twoCoreIn_isPGroup_52bad L) hOLnormalM
  have hOMne : twoCoreIn M ≠ ⊥ := by
    intro hbot
    exact hOLne (le_bot_iff.mp (hOLOM.trans (le_of_eq hbot)))
  have hCMcore : Subgroup.centralizer (twoCoreIn M : Set G) ≤ twoCoreIn M :=
    (Subgroup.centralizer_le hOLOM).trans (hCLcore.trans hOLOM)
  have hMsolv : Group.IsSolvable M :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hML) (Subgroup.inclusion_injective hML)
  refine ⟨M, hBKM, hbadM, hMsolv, hOMne, hCMcore, ?_⟩
  intro X hBKOMX hXM
  by_contra hbadX
  have hXL : X ≤ L := hXM.le.trans hML
  have hBKOLX : (B ⊔ K) ⊔ OL ≤ X := by
    exact sup_le (le_sup_left.trans hBKOMX)
      (hOLOM.trans (le_sup_right.trans hBKOMX))
  have hXSmall : X ∈ SmallBad := ⟨hXL, hBKOLX, hbadX⟩
  have hMX : M ≤ X := hMmin.2 hXSmall hXM.le
  exact hXM.ne (le_antisymm hXM.le hMX)

end Stellmacher.SectionsFiveToSeven

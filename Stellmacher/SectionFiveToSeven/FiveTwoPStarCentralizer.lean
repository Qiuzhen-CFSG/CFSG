module

public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.OmegaOneCenterMap

/-!
# The P-star residual inside the omega centralizer

Let `S` be a Sylow 2-subgroup and put `C = C_G(Ω₁(Z(S)))`. If `P`
belongs to `PStarFamily C S`, then its two-residual is subnormal in `C`.
This is the initial P-star reduction in Stellmacher (5.2), before the
maximal-counterexample argument.

The definition supplies a maximal local-family member `L` in which the
two-residual of `P` is subnormal. The proof shows that `C` itself is a local
member: its 2-core contains the nontrivial omega center. If that core were
all of `S`, then `S` would be normal in `P`, contrary to the proper-core
clause in the local-family definition. Maximality therefore gives `L=C`.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), proof of Lemma (5.2), pp. 28--29; see
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

private theorem twoCoreIn_le_of_isSylowTwoIn_52
    {G : Type u} [Group G]
    {S P : Subgroup G} (hS : IsSylowTwoIn S P) :
    twoCoreIn P ≤ S := by
  obtain ⟨_hSP, T, rfl⟩ := hS
  exact Subgroup.map_mono
    ((pCore_isPGroup (G := P) (p := 2)).le_sylow_of_normal T)

private theorem omegaOneCenter_isPGroup_52
    {G : Type u} [Group G] (S : Subgroup G) :
    IsPGroup 2 (omegaOneCenter S) := by
  rw [show omegaOneCenter S = omegaOneCenterAmbient S by rfl]
  let _ : IsElementaryAbelian 2 (omegaOneCenterAmbient S) :=
    omegaOneCenterAmbient_elementaryAbelian S
  exact IsElementaryAbelian.isPGroup 2 (omegaOneCenterAmbient S)

private theorem omegaOneCenter_le_self_52
    {G : Type u} [Group G] (S : Subgroup G) :
    omegaOneCenter S ≤ S := by
  unfold omegaOneCenter
  exact (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans
    (Subgroup.map_subtype_le _)

private theorem omegaOneCenter_le_centerAmbient_52
    {G : Type u} [Group G] (S : Subgroup G) :
    omegaOneCenter S ≤ (Subgroup.center S).map S.subtype := by
  unfold omegaOneCenter
  exact Subgroup.map_mono (Subgroup.map_subtype_le _)

private theorem omegaOneCenter_ne_bot_of_isPGroup_52
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (hS : IsPGroup 2 S) (hSne : S ≠ ⊥) :
    omegaOneCenter S ≠ ⊥ := by
  let _ : Nontrivial S :=
    (Subgroup.nontrivial_iff_ne_bot S).2 hSne
  let _ : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  have hcenterP : IsPGroup 2 (Subgroup.center S) :=
    hS.to_subgroup (Subgroup.center S)
  obtain ⟨n, hn, hcard⟩ := hcenterP.nontrivial_iff_card.mp inferInstance
  have htwo : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hinner := omega₁_map_subtype_ne_bot
    (G := S) (Subgroup.center S) 2 htwo
  intro hbot
  apply hinner
  apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
  simpa [omegaOneCenter] using hbot

private theorem omegaOneCenter_normal_in_centralizer_52
    {G : Type u} [Group G]
    (S : Subgroup G) :
    ((omegaOneCenter S).subgroupOf
      (Subgroup.centralizer (omegaOneCenter S : Set G))).Normal := by
  have hle : omegaOneCenter S ≤
      Subgroup.centralizer (omegaOneCenter S : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨zc, hzc, rfl⟩ := omegaOneCenter_le_centerAmbient_52 S hz
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzc ⟨w, omegaOneCenter_le_self_52 S hw⟩)
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro z c hz hc
  have hcz : c * z = z * c :=
    (Subgroup.mem_centralizer_iff.mp hc z hz).symm
  simpa [hcz]

private theorem omegaOneCenter_le_twoCoreIn_centralizer_52
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) :
    omegaOneCenter S ≤
      twoCoreIn (Subgroup.centralizer (omegaOneCenter S : Set G)) := by
  let C := Subgroup.centralizer (omegaOneCenter S : Set G)
  have hZC : omegaOneCenter S ≤ C := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨zc, hzc, rfl⟩ := omegaOneCenter_le_centerAmbient_52 S hz
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzc ⟨w, omegaOneCenter_le_self_52 S hw⟩)
  let ZC : Subgroup C := (omegaOneCenter S).subgroupOf C
  have hZCnormal : ZC.Normal := omegaOneCenter_normal_in_centralizer_52 S
  have hZCp : IsPGroup 2 ZC :=
    (omegaOneCenter_isPGroup_52 S).of_equiv
      (Subgroup.subgroupOfEquivOfLe hZC).symm
  have hZCcore : ZC ≤ pCore 2 C := le_sSup ⟨hZCnormal, hZCp⟩
  simpa [C, ZC, twoCoreIn, Subgroup.map_subgroupOf_eq_of_le hZC] using
    (Subgroup.map_mono (f := C.subtype) hZCcore)

private theorem centralizer_isLMember_52
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (P : Subgroup G)
    (hP : P ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G))
      (S : Subgroup G)) :
    IsLMember
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G))
      (S : Subgroup G)
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G)) := by
  let C := Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G)
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨zc, hzc, rfl⟩ :=
      omegaOneCenter_le_centerAmbient_52 (S : Subgroup G) hz
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzc ⟨s, hs⟩).symm
  have hSylowC : IsSylowTwoIn (S : Subgroup G) C := by
    refine ⟨hSC, S.subtype hSC, ?_⟩
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSC]
  have hcoreP_le_S : twoCoreIn P ≤ (S : Subgroup G) :=
    twoCoreIn_le_of_isSylowTwoIn_52 hP.1.1.2.1
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro hbot
    apply hP.1.1.2.2.1
    exact le_bot_iff.mp (hcoreP_le_S.trans (le_of_eq hbot))
  have hZne : omegaOneCenter (S : Subgroup G) ≠ ⊥ :=
    omegaOneCenter_ne_bot_of_isPGroup_52
      (S : Subgroup G) S.isPGroup' hSne
  have hcoreCne : twoCoreIn C ≠ ⊥ := by
    intro hbot
    apply hZne
    exact le_bot_iff.mp
      ((omegaOneCenter_le_twoCoreIn_centralizer_52
        (S : Subgroup G)).trans (le_of_eq hbot))
  have hcoreCneS : (S : Subgroup G) ≠ twoCoreIn C := by
    intro heq
    have hcoreCnormal : ((twoCoreIn C).subgroupOf C).Normal := by
      rw [← Subgroup.comap_subtype, twoCoreIn,
        Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      exact (inferInstance : (pCore 2 C).Normal)
    have hCnormS : C ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
      rw [heq]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.map_subtype_le (pCore 2 C))).mp hcoreCnormal
    have hPnormS : P ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
      hP.1.1.1.trans hCnormS
    have hSP : (S : Subgroup G) ≤ P := hP.1.1.2.1.1
    have hSnormP : ((S : Subgroup G).subgroupOf P).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSP).mpr hPnormS
    have hScore : (S : Subgroup G) ≤ twoCoreIn P := by
      let SP : Subgroup P := (S : Subgroup G).subgroupOf P
      have hSPp : IsPGroup 2 SP :=
        S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSP).symm
      have hSPcore : SP ≤ pCore 2 P := le_sSup ⟨hSnormP, hSPp⟩
      simpa [SP, twoCoreIn, Subgroup.map_subgroupOf_eq_of_le hSP] using
        (Subgroup.map_mono (f := P.subtype) hSPcore)
    exact hP.1.1.2.2.2 (le_antisymm hScore hcoreP_le_S)
  exact ⟨le_rfl, hSylowC, hcoreCne, hcoreCneS⟩

/-- A P-star member's two-residual is subnormal in the full centralizer of
the omega-one center of the global Sylow 2-subgroup. -/
public theorem pstar_residual_subnormal_in_omegaCentralizer
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (P : Subgroup G)
    (hP : P ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G))
      (S : Subgroup G)) :
    SubnormalIn (twoResidualIn P)
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G)) := by
  let C := Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G)
  rcases hP.2 with ⟨L, hLmax, hsub⟩
  have hCmember : IsLMember C (S : Subgroup G) C :=
    centralizer_isLMember_52 S P hP
  have hCL : C = L := hLmax.2 C hCmember hLmax.1.1
  change SubnormalIn (twoResidualIn P) C
  rwa [hCL]

end Stellmacher.SectionsFiveToSeven

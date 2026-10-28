module
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.AmbientFusion.Fusion
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.Core
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.Pair
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Center
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Axes
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.TCentralizer
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.GroupTheory.IndexTwoInvolutionCentralizer

/-!
# The original marked pair for the centralizer argument

The unique central involution and the index-two centralizer calculation are
transported through the original Sylow marking. Nonfusion then promotes the
dihedral base to a Sylow subgroup of C_G(t), producing every field of PairData.
The source 13.9.7 consumer consequently has no extra local-geometry premise.

Source: Aschbacher–Smith 13.9.2(6) and 13.9.7, printed pp.969–971.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath CentralizerStructure
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

theorem t_order : orderOf m.t = 2 :=
  orderOf_eq_prime (by simpa only [pow_two] using m.t_sq) m.t_ne_one

theorem z_order : orderOf m.z = 2 := by
  rw [z,orderOf_injective m.embedding m.embedding_injective,SymmetricFourWreath.z_order]

theorem sylow_center_image :
    (center d.T).map (d.T : Subgroup G).subtype = zpowers m.z := by
  rw [← m.image_standardSylow]
  change (center ((standardSylow : Subgroup W).map m.embedding)).map
    ((standardSylow : Subgroup W).map m.embedding).subtype = _
  rw [← map_embeddedCenter _ _ m.embedding_injective,center_standardSylow,MonoidHom.map_zpowers]
  rfl

include m in
theorem sylow_center_omega_card : Nat.card (omega₁ (center d.T) (p := 2)) = 2 := by
  have hc : Nat.card (center d.T) = 2 := by
    rw [← card_map_of_injective (d.T : Subgroup G).subtype_injective,
      m.sylow_center_image,Nat.card_zpowers,m.z_order]
  have hzC : (⟨m.z,m.z_mem_sylow⟩ : d.T) ∈ center d.T := by
    apply mem_center_iff.mpr
    intro a
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (m.z_central_sylow a.property))
  let zz : omega₁ (center d.T) (p := 2) :=
    ⟨⟨⟨m.z,m.z_mem_sylow⟩,hzC⟩,subset_closure (by
      apply Subtype.ext
      apply Subtype.ext
      change m.z ^ (2^1) = 1
      simpa only [pow_one,m.z_order] using pow_orderOf_eq_one m.z)⟩
  have hzord : orderOf zz = 2 := by
    rw [← orderOf_coe zz,← orderOf_coe (zz : center d.T),
      ← orderOf_coe ((zz : center d.T) : d.T)]
    exact m.z_order
  apply Nat.dvd_antisymm
  · simpa only [hc] using (omega₁ (center d.T) (p := 2)).card_subgroup_dvd_card
  · simpa only [hzord] using orderOf_dvd_natCard zz

theorem sylow_centralizer_t :
    (d.T : Subgroup G) ⊓ centralizer ({m.t} : Set G) =
      Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) := by
  rw [m.elementary_thompson,← m.image_standardSylow]
  have he : m.image (standardSylow : Subgroup W) ⊓ centralizer ({m.t} : Set G) =
      m.image ((standardSylow : Subgroup W) ⊓ centralizer ({SymmetricFourWreath.t} : Set W)) := by
    ext x
    constructor
    · rintro ⟨⟨w,hw,rfl⟩,hc⟩
      refine ⟨w,⟨hw,?_⟩,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply m.embedding_injective
      simpa only [Marking.t,map_mul] using mem_centralizer_singleton_iff.mp hc
    · rintro ⟨w,⟨hw,hc⟩,rfl⟩
      refine ⟨mem_map_of_mem m.embedding hw,mem_centralizer_singleton_iff.mpr ?_⟩
      simpa only [Marking.t,map_mul] using congrArg m.embedding (mem_centralizer_singleton_iff.mp hc)
  rw [he,centralizer_t_in_standardSylow]
  rfl

variable [Finite G]

theorem thompson_sylow_t :
    ∃ S : Sylow 2 (centralizer ({m.t} : Set G)),
      (S : Subgroup (centralizer ({m.t} : Set G))).map
        (centralizer ({m.t} : Set G)).subtype =
          Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) := by
  let tt : d.T := ⟨m.t,m.t_mem_sylow⟩
  let zz : d.T := ⟨m.z,m.z_mem_sylow⟩
  have hzC : zz ∈ center d.T := by
    apply mem_center_iff.mpr
    intro a
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (m.z_central_sylow a.property))
  have hcard : Nat.card (centralizer ({tt} : Set d.T)) = 64 := by
    rw [← card_map_of_injective (d.T : Subgroup G).subtype_injective,
      map_subtype_centralizer_singleton]
    change Nat.card ((d.T : Subgroup G) ⊓ centralizer ({m.t} : Set G) : Subgroup G) = 64
    rw [m.sylow_centralizer_t,m.elementary_thompson,Marking.dihedralBase,m.card_image,card_J]
  have hidx : (centralizer ({tt} : Set d.T)).index = 2 := by
    have h := (centralizer ({tt} : Set d.T)).card_mul_index
    rw [hcard,d.card_sylow] at h
    omega
  obtain ⟨S,hS⟩ := d.T.exists_sylow_centralizer_eq_of_index_two_of_not_isConj
    m.sylow_center_omega_card zz hzC ((orderOf_coe zz).symm.trans m.z_order)
    tt ((orderOf_coe tt).symm.trans m.t_order) m.not_isConj_t_z hidx
  refine ⟨S,?_⟩
  rw [hS,subgroupOf_map_subtype]
  exact m.sylow_centralizer_t

/-- Every marked field of the original 13.9.7 configuration. -/
def pairData : PairData d where
  t := m.t
  z := m.z
  t_order := m.t_order
  z_order := m.z_order
  t_mem := m.t_mem_sylow
  z_mem := m.z_mem_sylow
  z_central := m.z_central_sylow
  thompson_normalizer := m.thompson_normalizer
  thompson_sylow := m.thompson_sylow_t
  thompson_derived := by
    rw [thompson,m.elementary_thompson]
    change ⁅SymmetricFourWreath.J.map m.embedding,SymmetricFourWreath.J.map m.embedding⁆ ≤ _
    rw [← map_commutator]
    have h := map_mono (f := m.embedding) derived_J_le
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,Marking.t,Marking.z] using h

theorem marked_common_centralizer (hE : IsEvenCharacteristicAt d.T) :
    centralizer ({m.z} : Set G) ⊓ centralizer ({m.t} : Set G) =
      Stellmacher.elementaryAbelianMaxJ (d.T : Subgroup G) :=
  m.pairData.source13_9_7 hE

end CFSG.Quasithin.Chapter13.Section09.Marking

module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCoreJoin
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Ambient

/-!
# The original binary-three projection descends through the point kernel

The full Sylow of the point centralizer maps to the original S. Its
two-core is therefore contained in O₂(LS), so the actual source projection
LS → SL₃(2) factors through the literal image of LS in C/O₂(C). This
factorization retains the original projection on every representative,
and its kernel is precisely the two-core of that image.

The actual opposite core maps to the same original self-centralizing
four-group under this descended projection. No containment of Lᵍ in C,
survival of the original Q, or finite carrier exclusion is inferred.
Source: Aschbacher--Smith15.3.23, pp.1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The descended map preserves the literal original core projection,
including its exact two-core kernel, at the actual full-Sylow point. -/
theorem binary_three_point_original_projection
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (z : G) (hLS : L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let A := (L ⊔ d.S).subgroupOf C
    let r := (q.subgroupMap A).comp (subgroupOfEquivOfLe hLS).symm.toMonoidHom
    ∃ π : A.map q →* Matrix.PSL3Two.SL,
      Function.Surjective π ∧ π.comp r = b.coreProjection ∧
      π.ker = pCore 2 (A.map q) := by
  let C := centralizer ({z} : Set G)
  let J := L ⊔ d.S
  let A := J.subgroupOf C
  let q := QuotientGroup.mk' (pCore 2 C)
  let r := (q.subgroupMap A).comp (subgroupOfEquivOfLe hLS).symm.toMonoidHom
  have hNS : C.pCoreIn 2 ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hcore : C.pCoreIn 2 ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 C) (hNS.trans le_sup_right)
      (hLS.trans (C.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image C (pCore 2 C))))
  have hr : Function.Surjective r :=
    (q.subgroupMap_surjective A).comp (subgroupOfEquivOfLe hLS).symm.surjective
  have hk : r.ker ≤ b.coreProjection.ker := by
    intro x hx
    rw [b.coreProjection_kernel]
    have hxq : q (inclusion hLS x) = 1 := congrArg Subtype.val hx
    have hxC : inclusion hLS x ∈ pCore 2 C := (QuotientGroup.eq_one_iff _).mp hxq
    obtain ⟨y,hy,he⟩ := hcore (mem_map_of_mem C.subtype hxC)
    exact (Subtype.ext he : y = x) ▸ hy
  have hbk : IsPGroup 2 b.coreProjection.ker := by
    rw [b.coreProjection_kernel]
    exact pCore_isPGroup
  have hzero : pCore 2 Matrix.PSL3Two.SL = ⊥ := by
    apply map_injective (f := Matrix.PSL3Two.equiv.toMonoidHom) Matrix.PSL3Two.equiv.injective
    rw [pCore_map_iso,Matrix.PSL3Two.pCore_two_PSL_eq_bot,Subgroup.map_bot]
  exact binary_three_factor_projection r b.coreProjection hr b.coreProjection_surjective hk hbk hzero

omit [Finite G] in
private theorem point_image_subgroup
    (J C Q : Subgroup G) (hJC : J ≤ C) (hQJ : Q ≤ J)
    (q : C →* (C ⧸ pCore 2 C)) :
    (Q.subgroupOf J).map
        ((q.subgroupMap (J.subgroupOf C)).comp (subgroupOfEquivOfLe hJC).symm.toMonoidHom) =
      ((Q.subgroupOf C).map q).subgroupOf ((J.subgroupOf C).map q) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact mem_map_of_mem q (show inclusion hJC y ∈ Q.subgroupOf C from hy)
  · rintro ⟨y,hy,he⟩
    refine ⟨⟨y,hQJ hy⟩,hy,?_⟩
    exact Subtype.ext he

/-- At the same actual point and exchanger, the descended original map
retains the opposite core's original elementary four and self-centralizer. -/
theorem binary_three_source_point_opposite_projection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let A := (c.L ⊔ d.S).subgroupOf C
    let r := (q.subgroupMap A).comp (subgroupOfEquivOfLe hLS).symm.toMonoidHom
    let D := ((((LinearThree.commutatorCore c.L).conjBy g).subgroupOf C).map q).subgroupOf (A.map q)
    ∃ π : A.map q →* Matrix.PSL3Two.SL,
      Function.Surjective π ∧ π.comp r = b.coreProjection ∧
      π.ker = pCore 2 (A.map q) ∧
      IsElementaryAbelian 2 (D.map π) ∧ Nat.card (D.map π) = 4 ∧
      centralizer (D.map π : Set Matrix.PSL3Two.SL) ≤ D.map π := by
  obtain ⟨π,hπ,hcomp,hker⟩ := binary_three_point_original_projection d c.L b z hLS P hP
  refine ⟨π,hπ,hcomp,hker,?_⟩
  obtain ⟨hQS,_,_⟩ := binary_three_source_conjugate_core_nonvanishing
    hG d hempty hM hu hmany hI htwo hf c e g hgT hgS
  have he := point_image_subgroup (c.L ⊔ d.S) (centralizer ({z} : Set G))
    ((LinearThree.commutatorCore c.L).conjBy g) hLS (hQS.trans le_sup_right)
    (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))
  rw [←he,map_map,hcomp]
  exact binary_three_source_conjugate_core_four
    hG d hempty hM hu hmany hI htwo hf c e b g hgT hgS

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

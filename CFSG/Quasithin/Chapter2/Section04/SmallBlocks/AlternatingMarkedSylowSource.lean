module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingExtensionInputs
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSylowGeometrySource
public import Theory.Representation.BinaryAlternatingFiveExtension.MarkedSylow
/-!
# The marked Sylow geometry from the original single A5 source

The actual moved elementary subgroup supplies an odd involution for the
same natural quotient action. Together with the elementary block centralizer,
this identifies the selected Sylow subgroup with the dihedral wreath product
times that literal centralizer. The Borel residual core then has its center
central in T, and its product with the centralizer is normalized by T.

All extension and marking premises are discharged from MinimalBlockSetup.
Source: Aschbacher–Smith 2.4.29, printed pp.544–545.
-/
public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_marked_sylow_model
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let D := centralizer (d.block : Set d.H)
    ∃ eS : d.S ≃* SymmetricFourWreath.P × D,
      ((MonoidHom.fst SymmetricFourWreath.P D).comp eS.toMonoidHom).ker =
        D.subgroupOf (d.S : Subgroup d.H) := by
  let U := (blockU d.block).map d.block.subtype
  let D := centralizer (d.block : Set d.H)
  let : d.block.Normal := hsingle ▸ d.L0_normal
  obtain ⟨q,e,hq,hker,hC,he⟩ := d.single_alternating_marked_action hsingle hA
  obtain ⟨hLq,hkL⟩ := d.single_alternating_residual_action hsingle q hq hker
  rw [d.single_block_core_intrinsic_source hG T hST hsingle] at hkL
  have hki : q.ker ⊓ d.block = U := by
    have hh := congrArg (map d.block.subtype) hkL
    change (q.ker.subgroupOf d.block).map d.block.subtype = U at hh
    rwa [subgroupOf_map_subtype] at hh
  obtain ⟨hd,hDz,hDe,hcore,hDS⟩ :=
    d.single_alternating_centralizer_factor hG T hM hTM hu hST hsingle hA
  let : IsElementaryAbelian 2 D := hDe
  obtain ⟨t,_,ht,ho⟩ := d.single_alternating_odd_involution hsingle hA q e hker hC he
  apply BinaryPermutation.AlternatingFiveExtension.marked_sylow_equiv
    q U d.block D (map_subtype_le _) hLq hki rfl hDz
    (hker.trans hcore) hd e he t _ ho (IsElementaryAbelian.isPGroup 2 D) d.S
  rw [←ht]
  exact pow_orderOf_eq_one t

theorem MinimalBlockSetup.single_alternating_marked_ambient_sylow_model
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let D := centralizer (d.block : Set d.H)
    let R := (d.S : Subgroup d.H).map d.H.subtype
    ∃ eR : R ≃* SymmetricFourWreath.P × D,
      ((MonoidHom.fst SymmetricFourWreath.P D).comp eR.toMonoidHom).ker =
        (D.map d.H.subtype).subgroupOf R := by
  let D := centralizer (d.block : Set d.H)
  let R := (d.S : Subgroup d.H).map d.H.subtype
  obtain ⟨eS,heS⟩ := d.single_alternating_marked_sylow_model hG T hM hTM hu hST hsingle hA
  let j := (d.S : Subgroup d.H).equivMapOfInjective d.H.subtype d.H.subtype_injective
  refine ⟨j.symm.trans eS,?_⟩
  ext x
  change (eS (j.symm x)).1 = 1 ↔ x.val ∈ D.map d.H.subtype
  have hh := Subgroup.ext_iff.mp heS (j.symm x)
  change (eS (j.symm x)).1 = 1 ↔ (j.symm x).val ∈ D at hh
  rw [hh]
  have hx : ((j.symm x).val : G) = x.val := congrArg Subtype.val (j.apply_symm_apply x)
  constructor
  · intro h
    exact hx ▸ mem_map_of_mem d.H.subtype h
  · rintro ⟨y,hy,hyx⟩
    have heq : y = (j.symm x).val := Subtype.ext (hyx.trans hx.symm)
    exact heq ▸ hy

/-- The original centralizer factor agrees with the ambient Sylow centralizer. -/
theorem MinimalBlockSetup.single_alternating_centralizer_factor_map
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    (centralizer (d.block : Set d.H)).map d.H.subtype =
      (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) := by
  let D := centralizer (d.block : Set d.H)
  have hDS := (d.single_alternating_centralizer_factor hG T hM hTM hu hST hsingle hA).2.2.2.2
  apply le_antisymm
  · exact le_inf ((map_mono hDS).trans hST.le)
      (map_centralizer_le_centralizer_image (d.block : Set d.H) d.H.subtype)
  · intro z hz
    have hzR := (d.single_block_sylow_centralizer T hST.le hsingle).le hz
    have hzH := (map_subtype_le _) hzR.1
    refine mem_map.mpr ⟨⟨z,hzH⟩,?_,rfl⟩
    intro l hl
    exact Subtype.ext (hz.2 (l : G) (mem_map_of_mem d.H.subtype hl))

/-- The center and characteristic-product conclusions of 2.4.29, with every
model premise discharged from the original single-block hypotheses. -/
theorem MinimalBlockSetup.single_alternating_sylow_geometry
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
    (center P).map P.subtype = (frattini R ⊓ center R).map R.subtype ∧
      (center P).map P.subtype ≤ (center (T : Subgroup G)).map (T : Subgroup G).subtype ∧
      (T : Subgroup G) ≤ normalizer ((P ⊔ D : Subgroup G) : Set G) := by
  let D := centralizer (d.block : Set d.H)
  obtain ⟨_,_,hDe,_,hDS⟩ :=
    d.single_alternating_centralizer_factor hG T hM hTM hu hST hsingle hA
  let : IsElementaryAbelian 2 D := hDe
  obtain ⟨e,he⟩ := d.single_alternating_marked_ambient_sylow_model hG T hM hTM hu hST hsingle hA
  refine ⟨d.single_alternating_core_frattini_center_of_sylow_model hG T hST hsingle hA e,
    d.single_alternating_core_center_in_T_of_sylow_model hG T hM hTM hu hST hsingle hA e,?_⟩
  have hh := d.single_alternating_core_factor_normalized_of_sylow_model
    hG T hM hTM hu hST hsingle hA e (D.map d.H.subtype) (map_mono hDS) he
  rwa [d.single_alternating_centralizer_factor_map hG T hM hTM hu hST hsingle hA] at hh

end CFSG.Quasithin.Chapter2

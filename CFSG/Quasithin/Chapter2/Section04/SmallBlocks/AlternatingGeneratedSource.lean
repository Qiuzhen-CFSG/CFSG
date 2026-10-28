module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingCentralFactorSource
public import Theory.GroupAction.PResidualCentralProduct

/-!
# The generated group in the single alternating-five block case

The Borel two-residual K and the ambient Sylow subgroup T normalize P D, where
P=O₂(K) is the quaternion central product and D=C_T(L). Their joined group has
two-residual centralizing Z(P D). The original unique maximal two-local overgroup
also contains C_G(Z(P)). All inputs are the original marked block setup.

Source: Aschbacher--Smith, 2.4.29, printed pp.544--545.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_generated_setup
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
    let E := P ⊔ D
    let F := K ⊔ (T : Subgroup G)
    E ≤ F ∧ F ≤ normalizer (E : Set G) ∧
      (pResidual 2 F).map F.subtype ≤ centralizer ((center E).map E.subtype : Set G) := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
  let E := P ⊔ D
  let Z := (center P).map P.subtype
  have hKL : K ≤ d.block.map d.H.subtype := (map_subtype_le _).trans inf_le_right
  have hKP : K ≤ normalizer (P : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hDK : D ≤ centralizer (K : Set G) := inf_le_right.trans (centralizer_le hKL)
  have hKD : K ≤ centralizer (D : Set G) := le_centralizer_iff.mp hDK
  have hKn : K ≤ normalizer (E : Set G) :=
    (le_inf hKP (hKD.trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hTn := (d.single_alternating_sylow_geometry hG T hM hTM hu hST hsingle hA).2.2
  have hZK : Z ≤ K := (map_subtype_le _).trans (pCoreIn_le 2 K)
  have hKZ : K ≤ normalizer (Z : Set G) :=
    hKP.trans (normalizer_le_normalizer_characteristic_image P (center P))
  let : (Z.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hZK).mpr hKZ
  obtain ⟨hp⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  have hc : Nat.card (Z.subgroupOf K) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZK).toEquiv,
      card_map_of_injective P.subtype_injective,hp.center_card]
  have hz := central_of_normal_card_two (Z.subgroupOf K) hc
  have hZc : Z ≤ centralizer (K : Set G) := by
    intro z hz'
    have hzc : (⟨z,hZK hz'⟩ : K) ∈ center K := hz hz'
    exact fun k hk => congrArg Subtype.val (mem_center_iff.mp hzc ⟨k,hk⟩)
  have hDR : D ≤ (d.S : Subgroup d.H).map d.H.subtype := by
    rw [show D = _ from d.single_block_sylow_centralizer T hST.le hsingle]
    exact inf_le_left
  have hDc := (d.single_alternating_centralizer_source hG T hM hTM hu hST hsingle hA).1
  have hec : (center E).map E.subtype = Z ⊔ D :=
    center_sup_of_central_factor P D
      (hDK.trans (centralizer_le (pCoreIn_le 2 K)))
      (hDc.trans (centralizer_le (hDR.trans (map_subtype_le _))))
  have hKc : K ≤ centralizer ((center E).map E.subtype : Set G) := by
    rw [hec]
    exact le_centralizer_iff.mpr (sup_le hZc hDK)
  refine ⟨sup_le ((pCoreIn_le 2 K).trans le_sup_left) (inf_le_left.trans le_sup_right),
    sup_le hKn hTn,?_⟩
  exact pResidual_join_le_centralizer 2 K (T : Subgroup G) _ hKc
    (hTn.trans (normalizer_le_normalizer_characteristic_image E (center E))) T.isPGroup'

theorem MinimalBlockSetup.single_alternating_core_center_centralizer_le
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    centralizer ((center P).map P.subtype : Set G) ≤ M := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let Z := (center P).map P.subtype
  obtain ⟨hp⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G:=center P) 2 (hp.center_card ▸ dvd_rfl)
  let f := P.subtype.comp (center P).subtype
  have hf : Function.Injective f := P.subtype_injective.comp (center P).subtype_injective
  have hzG : orderOf (f z) = 2 := (orderOf_injective f hf z).trans hz
  have hzZ : f z ∈ Z := mem_map_of_mem P.subtype z.property
  have hZ := (d.single_alternating_sylow_geometry hG T hM hTM hu hST hsingle hA).2.1
  obtain ⟨w,hw,hwz⟩ := hZ hzZ
  have hc := centralizer_le_of_M_central_involution T hTM hu hzG (T.subtype hTM) (by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]
    intro a ha
    rw [←hwz]
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨a,ha⟩))
  exact (centralizer_le (Set.singleton_subset_iff.mpr hzZ)).trans hc

end CFSG.Quasithin.Chapter2

module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryBenderBorel
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryBenderLinear
public import Theory.SpecificGroups.SU3.OrdinaryBorelTransport
public import Theory.SpecificGroups.SU3.OrdinaryComponentRank
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal

/-!
# The actual original ordinary binary unitary exclusion

Odd-prime rank forces the same unitary component to be normal in the
original centralizer. Its native fixed-field torus supplies a two-perfect
subgroup of the actual Borel, with Thompson normalization and the requisite
centralizer comparison. Original local controls identify that Borel with
the marked intersection and original residual control contradicts movement.
The internal Linear import shares only the private raw Thompson contradiction;
no private name enters this module's public statement.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]

private theorem raw_bender_unitary_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G)) (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSU L 3 (2^n)) :
    (L.subgroupOf (centralizer (Z1 : Set G))).Normal := by
  let := h.elementary
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  obtain ⟨r,hr,ho,hR⟩ := HermitianForm.OrdinaryBorel.exists_odd_rank_two J hn hF hconj
  let : Fact r.Prime := ⟨hr⟩
  have hsq := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  let ek := subgroupOfEquivOfLe hLG
  have hZtwo : IsPGroup 2 (center L) := hcenter ▸ pCore_isPGroup
  have hZ' := hZtwo.of_equiv (centerCongr ek.symm)
  obtain ⟨k,hk⟩ := hZ'.exists_card_eq
  have hc : Nat.Coprime r (Nat.card (center (L.subgroupOf (centralizer (Z1 : Set G))))) := by
    rw [hk]
    exact (Nat.coprime_two_right.mpr ho).pow_right k
  have hR' : 2 ≤ primeRank r (L.subgroupOf (centralizer (Z1 : Set G))) := by
    rw [primeRank_equiv r ek,primeRank_equiv r e]
    exact hR
  exact hL.normal_of_coprime_center_primeRank r hc (by
    have hh := hsq.stronglyQuasithin r hr ho
    omega)

/-- Original marked Borel and residual controls exclude every nondegenerate
binary unitary ordinary component, without assuming its normality. -/
theorem PreparedChosenModule.raw_ordinary_not_binary_unitary
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G)) (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hcontrol : ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
      (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤ Mc)
    (hI : (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype)
    (hmove : ⁅L,⁅V,(pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (Z1 : Set G)).subtype⁆⁆ ≠ ⊥)
    (hout : ¬ L ≤ centralizer (Z1 : Set G) ⊓ Mc)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSU L 3 (2^n)) : False := by
  let H := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ H
  let B0 := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
  have hBMZ : B0 ≤ H ⊓ Mc := by
    have he := h.raw_ordinary_bender_borel hG T hu hZ hZne hLG hL
      hSylG hSylL hcontrol hbound hout (.unitary n hn hm)
    change (H ⊓ Mc) ⊓ L = B0 at he
    rw [←he]
    exact inf_le_left
  have hnL := raw_bender_unitary_normal hG T h hZ hZne hLG hL hcenter hn hm
  have hSL : S ≤ normalizer (L : Set G) := (show S ≤ H from inf_le_right).trans
    ((normal_subgroupOf_iff_le_normalizer hLG).mp hnL)
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  obtain ⟨P,hP⟩ := hSylL
  have hSP : S.subgroupOf L = (P : Subgroup L) := by
    apply map_injective L.subtype_injective
    rw [hP,subgroupOf_map_subtype]
  have hP' : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  obtain ⟨B,hBB,hBtwo,hBJ,hfix⟩ :=
    HermitianForm.OrdinaryBorel.exists_thompson_borel_subgroup J hn hF hconj L S hSL e P hSP
  have hBB0 : B ≤ B0 := by
    change B ≤ (normalizer ((P : Subgroup L) : Set L)).map L.subtype at hBB
    rwa [hP'] at hBB
  exact raw_bender_thompson_contradiction hG T hM hJ h hZ hI hmove
    (hBB0.trans hBMZ) hBJ hBtwo hfix

end CFSG.Quasithin.Chapter15.Section01

module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SylowControl
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.OddImage

/-!
# The central-involution hypotheses in the Case-I centralizer

The nontrivial elementary subgroup Z₁ is central in G₁=C_G(Z₁).
The actual Sylow subgroup of G₁ lies in T, so source1.1.6 supplies the
complete1.1.5 hypotheses for each nonidentity central involution of T.
The unique maximal local over C_G(Z) contains each such involution
centralizer. Its characteristic-two property also passes to C_Mc(Z₁).

Source: Aschbacher--Smith15.1.18(6), printed p.1093, using1.1.3 and1.1.6.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterB Chapter14.SourcePreliminaries Chapter12.Section08
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace CaseIMarkedSubgroup
variable {T : Sylow 2 G} {Mc Z1 : Subgroup G}

/-- Derive the whole earlier-source input required by original15.1.18(6). -/
theorem central_involution_hypotheses
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hZne : Z1 ≠ ⊥) (hZ : IsElementaryAbelian 2 Z1)
    (P : Sylow 2 (centralizer (Z1 : Set G)))
    (hPT : (P : Subgroup (centralizer (Z1 : Set G))).map
      (centralizer (Z1 : Set G)).subtype ≤ (T : Subgroup G))
    {z : G} (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1) :
    Chapter1.Lemma115Hypotheses (centralizer (Z1 : Set G)) P Mc z := by
  let := hZ
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hz' := (mem_omegaOneCenterAmbient_iff _ z).mp hz
  exact Chapter1.lemma_1_1_6 hZne (IsElementaryAbelian.isPGroup 2 Z1)
    (le_centralizer_iff_isMulCommutative.mpr inferInstance) le_rfl
    (Subgroup.centralizer_le_normalizer _) P T hPT
    (orderOf_eq_prime hz'.2.1 hzne) hz'.1
    (fun t ht => hz'.2.2 t ht) hMc.1
    (central_involution_centralizer_le_partner T hu hz hzne)
    (fun N hN hTN => Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T N hN hTN))

/-- The literal M_Z inherits characteristic two from M_c. -/
theorem partner_centralizer_characteristic_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hZ : IsPGroup 2 Z1) (hZT : Z1 ≤ (T : Subgroup G)) :
    centralizer (Z1 : Set G) ⊓ Mc ∈ Chapter1.He G := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  rw [inf_comm]
  exact pCoreIn_selfCentralizing_centralizer
    (Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T Mc hMc.1 hTMc)) hZ (hZT.trans hTMc)

end CaseIMarkedSubgroup
end CFSG.Quasithin.Chapter15.Section01

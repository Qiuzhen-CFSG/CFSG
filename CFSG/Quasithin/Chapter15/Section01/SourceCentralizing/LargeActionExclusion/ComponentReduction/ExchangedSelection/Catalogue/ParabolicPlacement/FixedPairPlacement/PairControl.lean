module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.Definitions
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SylowControl
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Pair
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.PairTransport

/-!
# One characteristic pair on the original two Sylow subgroups

The pair is chosen on Baum(T), before the parabolic. The source equality
Baum(S)=Baum(T) transports this same pair to any Sylow realization of S.
Its first central restriction contains the original nontrivial central seed;
its second ambient image is unchanged. Consequently their centralizer and
normalizer lie in the original Mc and M, respectively.

This is the transfer step in 15.1.22(*), not the missing minimal-parabolic
or residual-product argument. Source: Aschbacher--Smith, C.1.19 and
15.1.17, 15.1.22, printed pp.127,1092,1098--1099.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB ChapterC.GlaubermanNiles ChapterC.RankOne.ChiProduct
open Section03 Section03.InitialSource ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The source C₁(S), using the pair originally selected on Baum(T). -/
@[expose] noncomputable def pairSeed (d : CaseIComponentData T M Mc V)
    (D : CharacteristicPair (baumann (T : Subgroup G))) : Subgroup G :=
  omegaOneCenterAmbient d.S ⊓ D.first.map (baumann (T : Subgroup G)).subtype

/-- The original seed grows on passing from T to S; the pair is unchanged. -/
theorem firstSeed_le_pairSeed (d : CaseIComponentData T M Mc V)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (hB : baumann d.S = baumann (T : Subgroup G)) :
    FixedPair.firstSeed T D ≤ d.pairSeed D := by
  intro x hx
  obtain ⟨hxT,hx2,hxc⟩ := (mem_omegaOneCenterAmbient_iff _ x).mp hx.1
  have hxB : x ∈ baumann (T : Subgroup G) := (map_subtype_le D.first) hx.2
  have hxS : x ∈ d.S := (show baumann d.S ≤ d.S from inf_le_left) (hB.symm ▸ hxB)
  exact ⟨(mem_omegaOneCenterAmbient_iff _ x).mpr
    ⟨hxS,hx2,fun s hs => hxc s (d.S_le_T hs)⟩,hx.2⟩

/-- The full ambient centralizer, not only its intersection with G₁, is controlled. -/
theorem pairSeed_centralizer_le_partner (d : CaseIComponentData T M Mc V)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (hB : baumann d.S = baumann (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    centralizer (d.pairSeed D : Set G) ≤ Mc :=
  (centralizer_le (d.firstSeed_le_pairSeed D hB)).trans
    (UniformControl.firstSeed_centralizer_le_partner T D hu)

/-- Original 15.1.17 controls the second member of every such pair. -/
theorem pair_second_normalizer_le (d : CaseIComponentData T M Mc V)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) :
    normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G) ≤ M := by
  let := D.second_characteristic
  have hc := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).2.2.1
  have hB := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).2.1
  rw [hB] at hc
  exact (normalizer_le_characteristicNormalizerClosure _ D.second D.second_ne_bot).trans hc

/-- The literal Baumann marking for an arbitrary realization of S in H. -/
@[expose] noncomputable def pairBaumannEquiv (d : CaseIComponentData T M Mc V)
    (H : Subgroup G) (R : Sylow 2 H) (hR : (R : Subgroup H).map H.subtype = d.S)
    (hB : baumann d.S = baumann (T : Subgroup G)) :
    baumann (R : Subgroup H) ≃* baumann (T : Subgroup G) :=
  ((baumann (R : Subgroup H)).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      unfold baumann thompsonAlpha at hB ⊢
      rw [baumann_map_injective H.subtype H.subtype_injective,hR]
      exact hB))

theorem pairBaumannEquiv_symm_coe (d : CaseIComponentData T M Mc V)
    (H : Subgroup G) (R : Sylow 2 H) (hR : (R : Subgroup H).map H.subtype = d.S)
    (hB : baumann d.S = baumann (T : Subgroup G))
    (b : baumann (T : Subgroup G)) :
    (((d.pairBaumannEquiv H R hR hB).symm b : baumann (R : Subgroup H)) : H) = (b : G) := by
  exact congrArg (baumann (T : Subgroup G)).subtype
    ((d.pairBaumannEquiv H R hR hB).apply_symm_apply b)

/-- No new universal pair is selected in the local parabolic. -/
@[expose] noncomputable def localPair (d : CaseIComponentData T M Mc V)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (H : Subgroup G) (R : Sylow 2 H) (hR : (R : Subgroup H).map H.subtype = d.S)
    (hB : baumann d.S = baumann (T : Subgroup G)) :
    CharacteristicPair (baumann (R : Subgroup H)) :=
  D.map (d.pairBaumannEquiv H R hR hB).symm

theorem localPair_universal (d : CaseIComponentData T M Mc V)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u})
    (H : Subgroup G) (R : Sylow 2 H) (hR : (R : Subgroup H).map H.subtype = d.S)
    (hB : baumann d.S = baumann (T : Subgroup G)) :
    (d.localPair D H R hR hB).Universal.{u,u} := hD.map _

theorem pair_member_map (d : CaseIComponentData T M Mc V)
    (H : Subgroup G) (R : Sylow 2 H) (hR : (R : Subgroup H).map H.subtype = d.S)
    (hB : baumann d.S = baumann (T : Subgroup G))
    (A : Subgroup (baumann (T : Subgroup G))) :
    ((A.map (d.pairBaumannEquiv H R hR hB).symm.toMonoidHom).map
      (baumann (R : Subgroup H)).subtype).map H.subtype =
        A.map (baumann (T : Subgroup G)).subtype := by
  rw [map_map,map_map]
  congr 1
  ext b
  exact d.pairBaumannEquiv_symm_coe H R hR hB b

theorem localPair_firstSeed_map (d : CaseIComponentData T M Mc V)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (H : Subgroup G) (R : Sylow 2 H) (hR : (R : Subgroup H).map H.subtype = d.S)
    (hB : baumann d.S = baumann (T : Subgroup G)) :
    (FixedPair.firstSeed R (d.localPair D H R hR hB)).map H.subtype = d.pairSeed D := by
  rw [FixedPair.firstSeed,Subgroup.map_inf _ _ _ H.subtype_injective,
    ←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,hR]
  exact congrArg (fun A => omegaOneCenterAmbient d.S ⊓ A)
    (d.pair_member_map H R hR hB D.first)

/-- Transfer the two genuine local alternatives to the original M and Mc. -/
theorem placement_of_localPair_alternative (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (H P : Subgroup G) (hPH : P ≤ H) (hPL : P ≤ d.L)
    (R : Sylow 2 H) (hR : (R : Subgroup H).map H.subtype = d.S)
    (hB : baumann d.S = baumann (T : Subgroup G))
    (halt : FixedPair.firstSeed R (d.localPair D H R hR hB) ≤ center H ∨
      ((d.localPair D H R hR hB).second.map (baumann (R : Subgroup H)).subtype).Normal) :
    P ≤ M ⊓ d.L ∨ P ≤ d.ML := by
  rcases halt with hc | hn
  · right
    apply le_inf (le_inf (hPL.trans d.L_component.1) ?_) hPL
    apply le_trans hPH
    apply le_trans _ (d.pairSeed_centralizer_le_partner D hB hu)
    intro x hx z hz
    rw [←d.localPair_firstSeed_map D H R hR hB] at hz
    obtain ⟨a,ha,rfl⟩ := hz
    exact (congrArg H.subtype ((mem_center_iff.mp (hc ha)) ⟨x,hx⟩)).symm
  · left
    apply le_inf _ hPL
    apply le_trans hPH
    apply le_trans _ (d.pair_second_normalizer_le D hG hM hJ h)
    let := hn
    have hnmap := ((d.localPair D H R hR hB).second.map
      (baumann (R : Subgroup H)).subtype).le_normalizer_map H.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hnmap
    change H ≤ normalizer (((D.second.map
      (d.pairBaumannEquiv H R hR hB).symm.toMonoidHom).map
        (baumann (R : Subgroup H)).subtype).map H.subtype : Set G) at hnmap
    rwa [d.pair_member_map] at hnmap

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

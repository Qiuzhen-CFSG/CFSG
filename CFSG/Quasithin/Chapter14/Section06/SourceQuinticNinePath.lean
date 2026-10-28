module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticNinePathOdd
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiCriticalPlacement

/-!
# Source oddness of every normalized quintic nine-path

The actual small-Suzuki three-path action places the original critical
pair on each required segment. The original critical intersection's nonzero
commutator is transported to the path by the common-Sylow action. Thus the
nine-path oddness theorem has only the original quintic source prefix and
the normalized nonbacktracking path as inputs.
-/

public noncomputable section
open Subgroup SimpleGraph Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
open Reduction CommutingNontrivial CommutingThreeProfile CommutingThreeProfile.ReducedLayer
variable {G : Type*} [Group G] [Finite G]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual normalized quintic nine-path has odd pointwise stabilizer,
with all critical placements and nonzero commutators produced internally. -/
theorem source_quintic_nine_path_odd
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let L : Fin 2 → Subgroup G := ![H,X]
    let F := reducedFamily L (T : Subgroup G)
    ∀ {v₀ : Vertex F} (p : BasedWalk (graph F) 9 v₀), p.Nonbacktracking →
      (p.2.1 : Vertex F) = base F true →
      (p.2.2.1 : Vertex F) = base F false →
      Odd (Nat.card (pathStabilizer F p)) ∧
        Odd (Nat.card ((pathStabilizer F p).map (G₀ L (T : Subgroup G)).subtype)) := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := G₀ L (T : Subgroup G)
  let F := reducedFamily L (T : Subgroup G)
  dsimp only
  intro v₀ p hp hm hy
  obtain ⟨hF,_,hred,_,hP,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  change HypothesisF11 L (T : Subgroup G) at hF
  change SuzukiContainment.reducedSylow L (T : Subgroup G) = T at hred
  change ∀ j, Reduction.P₀ L (T : Subgroup G) j = L j at hP
  have hstar' (r : Fin 2) : starredParabolic L (T : Subgroup G) r =
      Reduction.P₀ L (T : Subgroup G) r := by
    have hpar : parabolic L (T : Subgroup G) r = Reduction.P₀ L (T : Subgroup G) r := by
      rw [Reduction.P₀_eq_source hF,hred]
    exact le_antisymm ((starredParabolic_le r).trans_eq hpar)
      ((hP r).le.trans (local_le_starredParabolic r))
  have hstar (j : Bool) : star L (T : Subgroup G) j = F j := by
    cases j
    · change (starredParabolic L (T : Subgroup G) 0).subgroupOf J =
        (Reduction.P₀ L (T : Subgroup G) 0).subgroupOf J
      exact congrArg (fun K : Subgroup G => K.subgroupOf J) (hstar' 0)
    · change (starredParabolic L (T : Subgroup G) 1).subgroupOf J =
        (Reduction.P₀ L (T : Subgroup G) 1).subgroupOf J
      exact congrArg (fun K : Subgroup G => K.subgroupOf J) (hstar' 1)
  have hcommon (j : Bool) : ∃ R : Sylow 2 (star L (T : Subgroup G) j),
      (R : Subgroup (star L (T : Subgroup G) j)).map
        (star L (T : Subgroup G) j).subtype = Q F (base F (!j)) ⊔ Q F (base F j) := by
    obtain ⟨R,hR⟩ :=
      (source_quintic_dgs_common_sylow hG T hempty hM hu hmany hcard e H hH hi).2.2 j
    rw [hstar j]
    refine ⟨R,?_⟩
    cases j
    · exact hR.1.trans (sup_comm _ _)
    · exact hR.1
  obtain ⟨Tlin,hTlin⟩ := hcommon true
  obtain ⟨Ry,hRy⟩ := hcommon false
  obtain ⟨_,⟨eSuz⟩⟩ := source_quintic_suzuki_zero_quotient hG T hempty hM hu hmany hcard e H hH hi
  obtain ⟨_,⟨eX⟩⟩ := Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  let eLin : (X ⧸ pCore 2 X) ≃* SL(2,ZMod 2) :=
    eX.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
  have hfield : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hb : 2 < b F := by
    have hh := (source_quintic_dgs_critical_three hG T hempty hM hu hmany hcard e H hH hi).1
    change b F = 3 at hh
    omega
  let y := base F false
  let m := base F true
  let z : Vertex F := p.2.2.2.1
  let w : Vertex F := p.2.2.2.2.1
  obtain ⟨a₀,x₀,ha₀,_,_,hx₀m,hx₀ne,_,hc₀,_,_,hbranch₀⟩ :=
    source_quintic_dgs_critical_path hG T hempty hM hu hmany hcard e H hH hi
  have hb3 : b F = 3 :=
    (source_quintic_dgs_critical_three hG T hempty hM hu hmany hcard e H hH hi).1
  have hcrit {a b c d : Vertex F} (hab : (graph F).Adj a b)
      (hbc : (graph F).Adj b c) (hcd : (graph F).Adj c d)
      (hca : c ≠ a) (hdb : d ≠ b) (hat : a.type = true) : IsCriticalPair F a d := by
    let q : BasedWalk (graph F) 3 a := ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,⟨⟨d,hcd⟩,PUnit.unit⟩⟩⟩
    have hq : q.Nonbacktracking := ⟨hca,hdb,True.intro⟩
    exact small_suzuki_critical_pair_on_three_path hF true eLin eSuz Tlin hTlin Ry hRy
      hc₀ hb3 q hq (hat.trans ha₀.symm)
  have htwo {a b c : Vertex F} (hab : (graph F).Adj a b) (hbc : (graph F).Adj b c) :
      a.type = c.type := by
    have ha := Bool.eq_not_iff.mpr hab.1
    have hb := Bool.eq_not_iff.mpr hbc.1
    rw [ha,hb,Bool.not_not]
  have ht2 : (p.2.1 : Vertex F).type = true := congrArg Subgroup.CosetGeometry.Vertex.type hm
  have ht0 : v₀.type = true := (htwo p.1.property p.2.1.property).trans ht2
  have ht4 : (p.2.2.2.1 : Vertex F).type = true :=
    (htwo p.2.2.2.1.property.symm p.2.2.1.property.symm).trans ht2
  have ht6 : (p.2.2.2.2.2.1 : Vertex F).type = true :=
    (htwo p.2.2.2.2.2.1.property.symm p.2.2.2.2.1.property.symm).trans ht4
  have ht8 : (p.2.2.2.2.2.2.2.1 : Vertex F).type = true :=
    (htwo p.2.2.2.2.2.2.2.1.property.symm p.2.2.2.2.2.2.1.property.symm).trans ht6
  have hc : IsCriticalPair F v₀ y := by
    have hh := hcrit p.1.property p.2.1.property p.2.2.1.property hp.1 hp.2.1 ht0
    simpa only [hy] using hh
  have hc6 : IsCriticalPair F (p.2.2.2.2.2.1 : Vertex F) y := by
    have hh := hcrit p.2.2.2.2.2.1.property.symm p.2.2.2.2.1.property.symm
      p.2.2.2.1.property.symm hp.2.2.2.2.1.symm hp.2.2.2.1.symm ht6
    simpa only [hy] using hh
  have hc2 : IsCriticalPair F (p.2.1 : Vertex F) w :=
    hcrit p.2.2.1.property p.2.2.2.1.property p.2.2.2.2.1.property
      hp.2.2.1 hp.2.2.2.1 ht2
  have hc8 : IsCriticalPair F (p.2.2.2.2.2.2.2.1 : Vertex F) w :=
    hcrit p.2.2.2.2.2.2.2.1.property.symm p.2.2.2.2.2.2.1.property.symm
      p.2.2.2.2.2.1.property.symm hp.2.2.2.2.2.2.1.symm hp.2.2.2.2.2.1.symm ht8
  have hbranch : ⁅V F w 1 ⊓ Q F y,V F y 1⁆ ≠ ⊥ := by
    have hym : (graph F).Adj y m :=
      ⟨by change (false : Bool) ≠ true; decide,Subgroup.CosetGeometry.incident_base F false true⟩
    have hyz : (graph F).Adj y z := by
      have hh : (graph F).Adj (p.2.2.1 : Vertex F) z := p.2.2.2.1.property
      simpa only [hy] using hh
    have hzw : (graph F).Adj z w := p.2.2.2.2.1.property
    have hwy : w ≠ y := by simpa only [hy] using hp.2.2.2.1
    obtain ⟨g,hg,hgz⟩ := star_locally_transitive hF false hyz hym
    have hgy : g • y = y := star_le_stabilizer false hg
    have hmgw : (graph F).Adj m (g • w) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hzw
      change (graph F).Adj (g • z) (g • w) at hh
      rwa [hgz] at hh
    have hgwne : g • w ≠ y := fun he => hwy ((MulAction.injective g) (he.trans hgy.symm))
    obtain ⟨u,hu,hux⟩ := linear_common_sylow_transitive hF true eLin Tlin hTlin
      hx₀m.symm hmgw hx₀ne hgwne
    have huy : u • y = y :=
      (sup_le (Q_le_stabilizer F y)
        (((source_Z_Q_U (reduced_triple hF) m).2.trans (ballKernel_one_le_edge F hym.symm)).trans inf_le_right)) hu
    have hsy : (g⁻¹*u) • y = y := by rw [mul_smul,huy,inv_smul_eq_iff]; exact hgy.symm
    have hsx : (g⁻¹*u) • x₀ = w := by rw [mul_smul,hux,inv_smul_smul]
    have hh := (map_eq_bot_iff_of_injective
      (⁅V F x₀ 1 ⊓ Q F y,V F y 1⁆ : Subgroup J)
      (f := (MulAut.conj (g⁻¹*u)).toMonoidHom) (MulAut.conj (g⁻¹*u)).injective).not.mpr hbranch₀
    rwa [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj (g⁻¹*u)).injective,
      ←V_translate F,←Q_translate F,←V_translate F,hsy,hsx] at hh
  exact source_quintic_normalized_nine_path_odd hG T hempty hM hu hmany hcard e H hH hi
    p hp hm hy hc hc6 hc2 hc8 hbranch

end CFSG.Quasithin.Chapter14.Section06

module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticTrappedEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiUntrappedExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiIncomingIndex
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiNinePathOdd

/-!
# Odd stabilizer of the original normalized quintic nine-path

The actual quintic trapped escape and the parameter-zero untrapped
exclusion kill every element of a two-subgroup fixing the same nine-path.
The final orbit-normalizer argument uses the original full cores. Applied
to the literal Sylow two-subgroup of the path stabilizer, this proves its
order is odd, including under the original completion inclusion.
-/

public noncomputable section
open Subgroup SimpleGraph Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
open Reduction CommutingNontrivial CommutingThreeProfile CommutingThreeProfile.ReducedLayer
set_option backward.isDefEq.respectTransparency false in
private theorem small_suzuki_nine_path_element_from_trapped_geometry
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (hF : HypothesisF11 L S) (hb : 2 < b (reducedFamily L S))
    (eSuz : (L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0)
    (eLin : (L 1 ⧸ pCore 2 (L 1)) ≃* SL(2,k))
    (Ry : Sylow 2 (star L S false))
    (hRy : (Ry : Subgroup (star L S false)).map (star L S false).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) true) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) false))
    (hfield : Nat.card k = 2)
    (Tlin : Sylow 2 (star L S true))
    (hTlin : (Tlin : Subgroup (star L S true)).map (star L S true).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) false) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) true))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) true)
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) false)
    (hc2 : IsCriticalPair (reducedFamily L S)
      (p.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hc8 : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hc6 : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (base (reducedFamily L S) false))
    (htrapped : ∀ t : G₀ L S, t ∈ Q (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) →
      let F := reducedFamily L S
      let A := V F (p.1 : Vertex F) 1 ⊓ centralizer ({t} : Set (G₀ L S))
      A ≤ Q F (base F false) → A = V F (p.1 : Vertex F) 1 ⊓ Q F (base F false) ∧
        ¬ A ⊓ Q F (p.2.2.2.2.1 : Vertex F) ≤ Q F (p.2.2.2.2.2.1 : Vertex F))
    (U : Subgroup (G₀ L S)) (hU : IsPGroup 2 U)
    (hfix : U ≤ pathStabilizer (reducedFamily L S) p)
    (t : G₀ L S) (ht : t ∈ U)
    (hbranchw : ⁅V (reducedFamily L S) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) 1 ⊓
      Q (reducedFamily L S) (base (reducedFamily L S) false),
      V (reducedFamily L S) (base (reducedFamily L S) false) 1⁆ ≠ ⊥) : t = 1 := by
  let J := G₀ L S
  let F := reducedFamily L S
  let m := base F true
  let y := base F false
  let x : Vertex F := p.1
  let z : Vertex F := p.2.2.2.1
  let w : Vertex F := p.2.2.2.2.1
  let c : Vertex F := p.2.2.2.2.2.1
  let C := centralizer ({t} : Set J)
  let A := V F x 1 ⊓ C
  let D := A ⊓ Q F w
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple hF)
  have hcore := source_mixed_path_two_subgroup_core hF true eLin eSuz p hp U hU hfix
  have htype : w.type = false := by
    have h3 : (p.2.2.1 : Vertex F).type = false := congrArg Subgroup.CosetGeometry.Vertex.type hy
    have h4 : false ≠ z.type := h3 ▸ p.2.2.2.1.property.1
    exact (Bool.eq_not_iff.mpr p.2.2.2.2.1.property.1.symm).trans (Bool.not_eq_iff.mpr h4.symm)
  have hzt : z.type = true := by
    have hh := Bool.eq_not_iff.mpr (htype ▸ p.2.2.2.2.1.property.1)
    simpa only [Bool.not_false] using hh
  have hzyEdge : (graph F).Adj z y := by
    have hh : (graph F).Adj z (p.2.2.1 : Vertex F) := p.2.2.2.1.property.symm
    simpa only [hy] using hh
  have hzw : (graph F).Adj z w := p.2.2.2.2.1.property
  have hwc : (graph F).Adj w c := p.2.2.2.2.2.1.property
  have hwy : w ≠ y := by simpa only [hy] using hp.2.2.2.1
  have hzn : z ≠ m := by simpa only [hm] using hp.2.2.1
  have hxm : (graph F).Adj x m := by
    have hh : (graph F).Adj x (p.2.1 : Vertex F) := p.2.1.property
    simpa only [hm] using hh
  have hxne : x ≠ y := by
    have hh := hp.2.1
    simpa only [hy] using hh.symm
  have htx : t ∈ Q F x := hcore x (by exact List.mem_cons_self) ht
  have htz : t ∈ Q F z := hcore z (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))) ht
  have htw : t ∈ Q F w := hcore w (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))) ht
  have hbranchx : ⁅V F x 1 ⊓ Q F y,V F y 1⁆ ≠ ⊥ := by
    have hym : (graph F).Adj y m :=
      ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base F false true⟩
    obtain ⟨g,hg,hgz⟩ := star_locally_transitive hF false hzyEdge.symm hym
    have hgy : g • y = y := star_le_stabilizer false hg
    have hmgw : (graph F).Adj m (g • w) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hzw
      change (graph F).Adj (g • z) (g • w) at hh
      rwa [hgz] at hh
    have hgwne : g • w ≠ y := fun he => hwy ((MulAction.injective g) (he.trans hgy.symm))
    obtain ⟨u,hu,huw⟩ := linear_common_sylow_transitive hF true eLin Tlin hTlin
      hmgw hxm.symm hgwne hxne
    have huy : u • y = y :=
      (sup_le (Q_le_stabilizer F y)
        (((source_Z_Q_U (reduced_triple hF) m).2.trans (ballKernel_one_le_edge F hym.symm)).trans inf_le_right)) hu
    have hty : (u*g) • y = y := by rw [mul_smul,hgy,huy]
    have htw : (u*g) • w = x := by rw [mul_smul,huw]
    have hh := (map_eq_bot_iff_of_injective
      (⁅V F w 1 ⊓ Q F y,V F y 1⁆ : Subgroup J)
      (f := (MulAut.conj (u*g)).toMonoidHom) (MulAut.conj (u*g)).injective).not.mpr hbranchw
    rwa [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj (u*g)).injective,
      ←V_translate F,←Q_translate F,←V_translate F,hty,htw] at hh
  by_cases htrap : A ≤ Q F y
  · obtain ⟨hA,hescape⟩ := htrapped t htx htrap
    have hiA : (Q F z).relIndex A = Nat.card k := by
      rw [show A = V F x 1 ⊓ Q F y from hA]
      exact source_small_suzuki_incoming_second_index hF false hb eSuz eLin hfield
        Ry hRy hxm hzyEdge.symm hzn hbranchx
    have hlocal := (source_small_suzuki_path_center_transitivity hF false hb eSuz Ry hRy
      p.2.2.1.property p.2.2.2.1.property p.2.2.2.2.1.property
      p.2.2.2.2.2.1.property p.2.2.2.2.2.2.1.property p.2.2.2.2.2.2.2.1.property
      hp.2.2.2.2.1 htype hc2 hc8 U
      (hcore _ (by exact List.mem_cons_of_mem _ (List.mem_cons_self)))
      (hcore _ (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
      (hcore _ (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
      (hcore _ (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))).1
    have hlocalC : ∀ v, (graph F).Adj w v → ∃ a ∈ stabilizer F w ⊓ C, a • z = v := by
      intro v hv
      obtain ⟨a,ha,he⟩ := hlocal v hv
      exact ⟨a,⟨ha.1,mem_centralizer_singleton_iff.mpr (ha.2 t ht).symm⟩,he⟩
    obtain ⟨a,ha,hac⟩ := hlocalC c hwc
    let g := a⁻¹
    let f := (MulAut.conj g).toMonoidHom
    let E := D.map f
    have hgw : g • w = w := (stabilizer F w).inv_mem ha.1
    have hgc : g • c = z := inv_smul_eq_iff.mpr hac.symm
    have hEQ : E ≤ Q F w := by
      have hh := map_mono (f := f) (show D ≤ Q F w from inf_le_right)
      change E ≤ (Q F w).map (MulAut.conj g).toMonoidHom at hh
      rwa [←Q_translate F,hgw] at hh
    have hEesc : ¬ E ≤ Q F z := by
      intro hE
      apply hescape
      intro d hd
      have hh := hE (mem_map_of_mem f hd)
      rw [←hgc,Q_translate F] at hh
      obtain ⟨u,hu,he⟩ := hh
      exact (MulAut.conj g).injective he ▸ hu
    have hEp : IsPGroup 2 E :=
      ((isPGroup_pCoreIn 2 (stabilizer F w)).to_le (show D ≤ Q F w from inf_le_right)).map f
    have hEC : E ≤ C := by
      have hh := map_mono (f := f) (show D ≤ C from inf_le_left.trans inf_le_right)
      have he : C.map (MulAut.conj g).toMonoidHom = C :=
        mem_normalizer_iff_map_conj_eq.mp (C.le_normalizer (C.inv_mem ha.2))
      exact hh.trans he.le
    have hlinear := linear_full_index_escape_transitive_at hF true eLin eSuz Tlin hTlin hzt
      hzyEdge hzw hwy.symm A E htrap hiA hEQ hEp hEesc
    have hCN : C ≤ normalizer (zpowers t : Set J) := by
      rw [zpowers_eq_closure]
      exact (show C ≤ centralizer (closure ({t} : Set J) : Set J) by
        rw [centralizer_closure]).trans (Subgroup.centralizer_le_normalizer _)
    have hlinearC : ∀ v, (graph F).Adj z v → ∃ g ∈ C, g • w = v := by
      obtain ⟨b,hb,hby⟩ := hlinear w hzw
      intro v hv
      obtain ⟨d,hd,hdy⟩ := hlinear v hv
      have hAC : A ⊔ E ≤ C := sup_le inf_le_right hEC
      refine ⟨d*b⁻¹,C.mul_mem (hAC hd) (C.inv_mem (hAC hb)),?_⟩
      rw [mul_smul,inv_smul_eq_iff.mpr hby.symm,hdy]
    have hbot := source_normalized_edge_eq_bot (reduced_triple hF) hzw (zpowers t)
      (zpowers_le.mpr ⟨Q_le_stabilizer F z htz,Q_le_stabilizer F w htw⟩)
      (fun v hv => by obtain ⟨g,hg,he⟩ := hlinearC v hv; exact ⟨g,hCN hg,he⟩)
      (fun v hv => by obtain ⟨g,hg,he⟩ := hlocalC v hv; exact ⟨g,hCN hg.2,he⟩)
    exact mem_bot.mp (hbot ▸ mem_zpowers t)
  · exact source_small_suzuki_nine_path_untrapped_eq_one hF false hb eSuz eLin
      Ry hRy hfield Tlin hTlin p hp hm hy hc2 hc8 hc6 U hU hfix t ht htrap hbranchw

variable {G : Type*} [Group G] [Finite G]

set_option backward.isDefEq.respectTransparency false in
/-- The literal normalized source nine-path has odd stabilizer. Its actual
critical placements and nonzero intersection branch are retained; no
positive parameter, local-action or path-oddness premise is present. -/
theorem source_quintic_normalized_nine_path_odd
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
      IsCriticalPair F v₀ (base F false) →
      IsCriticalPair F (p.2.2.2.2.2.1 : Vertex F) (base F false) →
      IsCriticalPair F (p.2.1 : Vertex F) (p.2.2.2.2.1 : Vertex F) →
      IsCriticalPair F (p.2.2.2.2.2.2.2.1 : Vertex F) (p.2.2.2.2.1 : Vertex F) →
      ⁅V F (p.2.2.2.2.1 : Vertex F) 1 ⊓ Q F (base F false),V F (base F false) 1⁆ ≠ ⊥ →
      Odd (Nat.card (pathStabilizer F p)) ∧
        Odd (Nat.card ((pathStabilizer F p).map (G₀ L (T : Subgroup G)).subtype)) := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := G₀ L (T : Subgroup G)
  let F := reducedFamily L (T : Subgroup G)
  dsimp only
  intro v₀ p hp hm hy hc hc6 hc2 hc8 hbranchw
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
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple hF)
  have helem (U : Subgroup J) (hU : IsPGroup 2 U)
      (hfix : U ≤ pathStabilizer F p) (t : J) (ht : t ∈ U) : t = 1 := by
    apply small_suzuki_nine_path_element_from_trapped_geometry hF hb eSuz eLin Ry hRy
      hfield Tlin hTlin p hp hm hy hc2 hc8 hc6 ?_ U hU hfix t ht hbranchw
    intro u hux
    dsimp only
    intro htrap
    exact source_quintic_trapped_centralizer_escape hG T hempty hM hu hmany hcard e H hH hi
      p.1.property.symm
      (by
        have hh : (graph F).Adj (p.1 : Vertex F) (p.2.1 : Vertex F) := p.2.1.property
        simpa only [hm] using hh)
      (by simpa only [hy] using hp.2.1.symm)
      (by
        have hh : (graph F).Adj (p.2.2.1 : Vertex F) (p.2.2.2.1 : Vertex F) := p.2.2.2.1.property
        simpa only [hy] using hh)
      p.2.2.2.2.1.property.symm p.2.2.2.2.2.1.property
      (by simpa only [hm] using hp.2.2.1)
      hc hc6 u hux htrap
  let P := pathStabilizer F p
  let S₂ : Sylow 2 P := Classical.choice inferInstance
  let U := (S₂ : Subgroup P).map P.subtype
  have hU : U = ⊥ := by
    apply eq_bot_iff.mpr
    intro t ht
    exact mem_bot.mpr (helem U (S₂.isPGroup'.map P.subtype) (map_subtype_le _) t ht)
  have hS₂ : (S₂ : Subgroup P) = ⊥ :=
    (map_eq_bot_iff_of_injective (S₂ : Subgroup P) P.subtype_injective).mp hU
  have hindex : (S₂ : Subgroup P).index = Nat.card P := by rw [hS₂,index_bot]
  have hodd : Odd (Nat.card P) := by
    rw [←Nat.not_even_iff_odd,even_iff_two_dvd,←hindex]
    exact S₂.not_dvd_index
  refine ⟨hodd,?_⟩
  rw [card_map_of_injective J.subtype_injective]
  exact hodd

end CFSG.Quasithin.Chapter14.Section06

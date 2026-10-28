module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCriticalNoncentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearCoreOrbit

/-!
# Large span intersections at every original cubic neighbor

The original critical intersection contains the marked four-plane and moves
the full cubic core. Since that core fixes the four-plane, the intersection
has more than four elements. The actual common Sylow fixes the original
quintic neighbor and is transitive on the other neighbors. Transport along
this Sylow preserves the literal intersection and gives the bound at every
neighbor, including the zero-parameter Suzuki case.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
open CommutingNontrivial CommutingThreeProfile CommutingThreeProfile.ReducedLayer
variable {G : Type*} [Group G] [Finite G]

/-- Every distinct neighbor of the actual cubic endpoint has a large
intersection with the original quintic span. -/
theorem source_quintic_dgs_neighbor_intersection_large
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
    let F := Reduction.reducedFamily L (T : Subgroup G)
    ∀ x, (graph F).Adj (base F true) x → x ≠ base F false →
      4 < Nat.card (V F (base F false) 1 ⊓ V F x 1 : Subgroup (Reduction.G₀ L (T : Subgroup G))) := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := Reduction.G₀ L (T : Subgroup G)
  let F := Reduction.reducedFamily L (T : Subgroup G)
  let y := base F false
  let m := base F true
  let U := conjugateSpanBy (localModule T M) H
  obtain ⟨g,hg,hDQ,hescape,hVI,_,hnoncentral⟩ :=
    source_quintic_critical_intersection_noncentral hG T hempty hM hu hmany hcard e H hH hi
  let Ustar := U.map (MulAut.conj g).toMonoidHom
  let I := U ⊓ Ustar
  have hIcard : 4 < Nat.card I := by
    by_contra hn
    have he : I = localModule T M :=
      (eq_of_le_of_card_ge hVI ((Nat.le_of_not_gt hn).trans_eq hcard.symm)).symm
    apply hnoncentral
    change I ≤ centralizer (X.pCoreIn 2 : Set G)
    rw [he]
    exact le_centralizer_iff.mp
      ((Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e).1.le.trans
        inf_le_right)
  obtain ⟨hF,_,hred,_,hP,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  change HypothesisF11 L (T : Subgroup G) at hF
  change SuzukiContainment.reducedSylow L (T : Subgroup G) = T at hred
  have hXmap : (F true).map J.subtype = X := (hmaps true).1
  have hQymap : (Q F y).map J.subtype = H.pCoreIn 2 := (hmaps false).2
  obtain ⟨g₀,hg₀,hg₀eq⟩ := (show g ∈ (F true).map J.subtype from hXmap.symm ▸ hg)
  change (g₀ : G) = g at hg₀eq
  let x₀ := g₀ • y
  have hgm : g₀ ∈ stabilizer F m := by
    change g₀ ∈ stabilizer F (base F true)
    rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base]
    exact hg₀
  have hadj : (graph F).Adj m y :=
    ⟨by change (true : Bool) ≠ false; decide,Subgroup.CosetGeometry.incident_base F true false⟩
  have hx₀ : (graph F).Adj m x₀ := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g₀).map_adj_iff.mpr hadj
    change (graph F).Adj (g₀ • m) x₀ at hh
    rwa [show g₀ • m = m from hgm] at hh
  obtain ⟨_,hUmap,_⟩ :=
    source_quintic_dgs_span_and_full_kernel hG T hempty hM hu hmany hcard e H hH hi
  change (V F y 1).map J.subtype = U at hUmap
  have hUx₀ : (V F x₀ 1).map J.subtype = Ustar := by
    rw [show x₀ = g₀ • y from rfl,V_translate,Subgroup.map_map]
    rw [show J.subtype.comp (MulAut.conj g₀).toMonoidHom =
      (MulAut.conj (g₀ : G)).toMonoidHom.comp J.subtype from rfl,
      ←Subgroup.map_map,hUmap,hg₀eq]
  let : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple hF)
  have hZ := fun v => (source_Z_Q_U (Reduction.reduced_triple hF) v).1
  have hb : 2 < b F := by
    have hh := (source_quintic_dgs_critical_three hG T hempty hM hu hmany hcard e H hH hi).1
    change b F = 3 at hh
    omega
  have hne₀ : x₀ ≠ y := by
    intro he
    apply hescape
    change Ustar ≤ H.pCoreIn 2
    rw [←hUx₀,he,←hQymap]
    exact map_mono (V_le_Q F (Reduction.reduced_triple hF).generate hZ
      (Reduction.reduced_kernel_sylow hF) hb y)
  have hI₀ : 4 < Nat.card (V F y 1 ⊓ V F x₀ 1 : Subgroup J) := by
    have he : (V F y 1 ⊓ V F x₀ 1).map J.subtype = I := by
      rw [map_inf _ _ _ J.subtype_injective,hUmap,hUx₀]
    have hc := card_map_of_injective (K := V F y 1 ⊓ V F x₀ 1) J.subtype_injective
    rw [he] at hc
    exact hc ▸ hIcard
  have hpar : parabolic L (T : Subgroup G) 1 = Reduction.P₀ L (T : Subgroup G) 1 := by
    rw [Reduction.P₀_eq_source hF,hred]
  have hstar : star L (T : Subgroup G) true = F true := by
    change (starredParabolic L (T : Subgroup G) 1).subgroupOf J =
      (Reduction.P₀ L (T : Subgroup G) 1).subgroupOf J
    apply congrArg (fun K : Subgroup G => K.subgroupOf J)
    apply le_antisymm
    · exact (starredParabolic_le 1).trans_eq hpar
    · rw [hP]
      exact local_le_starredParabolic 1
  obtain ⟨S,hS⟩ :=
    (source_quintic_dgs_common_sylow hG T hempty hM hu hmany hcard e H hH hi).2.2 true
  have hsyl : ∃ S₀ : Sylow 2 (star L (T : Subgroup G) true),
      (S₀ : Subgroup (star L (T : Subgroup G) true)).map (star L (T : Subgroup G) true).subtype =
        Q F y ⊔ Q F m := by
    rw [hstar]
    exact ⟨S,hS.1⟩
  obtain ⟨S₀,hS₀⟩ := hsyl
  obtain ⟨_,⟨eX⟩⟩ := Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  let eLin : (X ⧸ pCore 2 X) ≃* SL(2,ZMod 2) :=
    eX.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
  change ∀ x, (graph F).Adj m x → x ≠ y →
    4 < Nat.card (V F y 1 ⊓ V F x 1 : Subgroup J)
  intro x hx hne
  obtain ⟨t,ht,htx⟩ := linear_common_sylow_transitive hF true eLin S₀ hS₀ hx₀ hx hne₀ hne
  have hty : t • y = y :=
    (sup_le (Q_le_stabilizer F y)
      (((source_Z_Q_U (Reduction.reduced_triple hF) m).2).trans
        ((ballKernel_one_le_edge F hadj).trans inf_le_right))) ht
  have he : (V F y 1 ⊓ V F x₀ 1).map (MulAut.conj t).toMonoidHom =
      V F y 1 ⊓ V F x 1 := by
    rw [map_inf _ _ _ (MulAut.conj t).injective,←V_translate F,←V_translate F,hty,htx]
  have hc := card_map_of_injective (K := V F y 1 ⊓ V F x₀ 1)
    (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
  rw [he] at hc
  exact hc.symm ▸ hI₀

end CFSG.Quasithin.Chapter14.Section06

module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticReciprocalCommutator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SecondKernelSpan
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSpanFixedIndex

/-!
# The elementary second-kernel span in the original quintic source

The actual middle-core-product conjugator determines the other neighbor in
the same reduced graph. The full original core and span markings transport
the reciprocal commutator to the general linear second-kernel construction.
A linear neighbor swap places both reciprocal intersections in that same
span. The original inclusion returns an elementary X-span in both full cores,
with its exact intersection with either original neighboring span retained.

The intentional internal import reuses only the generic linear neighbor swap,
as in the existing internal second-kernel-span proof split. No positive Suzuki
parameter or supplied graph configuration is assumed.
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

omit [Finite G] in
private theorem map_conjugate_inclusion (J : Subgroup G) (W : Subgroup J) (g : J) :
    (W.map (MulAut.conj g).toMonoidHom).map J.subtype =
      (W.map J.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
  rw [map_map,map_map]
  rfl

private theorem second_span_of_original_conjugator
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (g : G) (hg : g ∈ sourceResidual M Mc ⊔ (T : Subgroup G))
    (hescape : ¬ (conjugateSpanBy (localModule T M) H).map
      (MulAut.conj g).toMonoidHom ≤ H.pCoreIn 2) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let UH := conjugateSpanBy (localModule T M) H
    let Ustar := UH.map (MulAut.conj g).toMonoidHom
    let Qstar := (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom
    let R := UH ⊓ Qstar
    let Rstar := Ustar ⊓ H.pCoreIn 2
    let W := conjugateSpanBy R X
    IsElementaryAbelian 2 W ∧ W ≤ H.pCoreIn 2 ⊓ X.pCoreIn 2 ∧
      W ⊓ UH = R ∧ Rstar ≤ W ∧ W ⊓ Ustar = Rstar ∧ ⁅Rstar,UH⁆ ≠ ⊥ := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := Reduction.G₀ L (T : Subgroup G)
  let F := Reduction.reducedFamily L (T : Subgroup G)
  let y := base F false
  let m := base F true
  let UH := conjugateSpanBy (localModule T M) H
  let Ustar := UH.map (MulAut.conj g).toMonoidHom
  let Qstar := (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom
  let R := UH ⊓ Qstar
  let Rstar := Ustar ⊓ H.pCoreIn 2
  let W := conjugateSpanBy R X
  obtain ⟨hF,_,hred,_,hP,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  change HypothesisF11 L (T : Subgroup G) at hF
  change SuzukiContainment.reducedSylow L (T : Subgroup G) = T at hred
  have hXmap : (F true).map J.subtype = X := (hmaps true).1
  have hQymap : (Q F y).map J.subtype = H.pCoreIn 2 := (hmaps false).2
  have hQmmap : (Q F m).map J.subtype = X.pCoreIn 2 := (hmaps true).2
  obtain ⟨g₀,hg₀,hg₀eq⟩ := (show g ∈ (F true).map J.subtype from hXmap.symm ▸ hg)
  change (g₀ : G)=g at hg₀eq
  let x := g₀ • y
  have hgm : g₀ ∈ stabilizer F m := by
    change g₀ ∈ stabilizer F (base F true)
    rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base]
    exact hg₀
  have hadj : (graph F).Adj m y :=
    ⟨by change (true : Bool) ≠ false; decide,Subgroup.CosetGeometry.incident_base F true false⟩
  have hxadj : (graph F).Adj m x := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g₀).map_adj_iff.mpr hadj
    change (graph F).Adj (g₀ • m) x at hh
    rwa [show g₀ • m=m from hgm] at hh
  obtain ⟨hfirst,hUmap,_⟩ :=
    source_quintic_dgs_span_and_full_kernel hG T hempty hM hu hmany hcard e H hH hi
  change (V F y 1).map J.subtype = UH at hUmap
  have hUx : (V F x 1).map J.subtype = Ustar := by
    rw [show x=g₀ • y from rfl,V_translate,map_conjugate_inclusion,hUmap,hg₀eq]
  have hQx : (Q F x).map J.subtype = Qstar := by
    rw [show x=g₀ • y from rfl,Q_translate,map_conjugate_inclusion,hQymap,hg₀eq]
  let : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple hF)
  have hZ := fun v => (source_Z_Q_U (Reduction.reduced_triple hF) v).1
  have hb : 2 < b F := by
    have hh := (source_quintic_dgs_critical_three hG T hempty hM hu hmany hcard e H hH hi).1
    change b F = 3 at hh
    omega
  have hne : x ≠ y := by
    intro he
    apply hescape
    change Ustar ≤ H.pCoreIn 2
    rw [←hUx,he,←hQymap]
    exact map_mono (V_le_Q F (Reduction.reduced_triple hF).generate hZ
      (Reduction.reduced_kernel_sylow hF) hb y)
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
  obtain ⟨hZymap,_⟩ := source_quintic_dgs_center_markings hG T hempty hM hu hmany hcard e H hH hi
  have hcomm : ⁅V F y 1,Q F y⁆ ≤ Z F y := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_commutator,hUmap,hQymap,hZymap]
    exact (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2.le
  have hcross : ⁅V F y 1 ⊓ Q F x,V F x 1 ⊓ Q F y⁆ = ⊥ := by
    apply map_injective J.subtype_injective
    rw [map_commutator,map_inf _ _ _ J.subtype_injective,map_inf _ _ _ J.subtype_injective,
      hUmap,hQx,hUx,hQymap,Subgroup.map_bot]
    exact (source_quintic_reciprocal_core_geometry hG T hempty hM hu hmany hcard e H hH hi
      g hg hescape).2.2
  let W₀ := conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)
  obtain ⟨hWel,hW2,_,hnW,hWY,_,hWz,_,_⟩ :=
    source_linear_second_kernel_span hF true hb hxadj hne S₀ hS₀ eLin hcomm hcross
  change IsElementaryAbelian 2 W₀ at hWel
  change W₀ ⊓ V F y 1=V F y 1 ⊓ Q F x at hWY
  have hRmap : (V F y 1 ⊓ Q F x).map J.subtype = R := by
    rw [map_inf _ _ _ J.subtype_injective,hUmap,hQx]
  have hRstarmap : (V F x 1 ⊓ Q F y).map J.subtype = Rstar := by
    rw [map_inf _ _ _ J.subtype_injective,hUx,hQymap]
  have hWmap : W₀.map J.subtype = W := by
    rw [map_conjugateSpanBy,hRmap]
    rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base,hXmap]
  have hWQm : W₀ ≤ Q F m := by
    have hh := (hfirst true).1
    change ballKernel F m 1=Q F m at hh
    exact (hW2.trans (ballKernel_antitone F m (by decide : 1≤2))).trans_eq hh
  have hWcores : W ≤ H.pCoreIn 2 ⊓ X.pCoreIn 2 := by
    apply le_inf
    · rw [←hWmap,←hQymap]
      exact map_mono (hWz y hadj)
    · rw [←hWmap,←hQmmap]
      exact map_mono hWQm
  have hWI : W ⊓ UH = R := by
    rw [←hWmap,←hUmap,←map_inf _ _ _ J.subtype_injective,hWY,hRmap]
  obtain ⟨u,hum,hux,huy⟩ := linear_neighbor_swap hF true eLin hxadj hadj hne
  have hswap : (V F y 1 ⊓ Q F x).map (MulAut.conj u).toMonoidHom = V F x 1 ⊓ Q F y := by
    rw [map_inf _ _ _ (MulAut.conj u).injective,←V_translate F,←Q_translate F,huy,hux]
  have hRstarW : V F x 1 ⊓ Q F y ≤ W₀ := by
    have hh := map_mono (f := (MulAut.conj u).toMonoidHom)
      (le_conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m))
    rw [hswap] at hh
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp (hnW hum))
  have hRW : Rstar ≤ W := by
    rw [←hRstarmap,←hWmap]
    exact map_mono hRstarW
  have hWIstar : W ⊓ Ustar = Rstar := le_antisymm
    (le_inf inf_le_right (inf_le_left.trans (hWcores.trans inf_le_left)))
    (le_inf hRW inf_le_left)
  have hnonzero : ⁅V F x 1 ⊓ Q F y,V F y 1⁆ ≠ ⊥ := by
    obtain ⟨a₀,x₀,_,_,_,hx₀,hn₀,_,_,_,_,hdisp⟩ :=
      source_quintic_dgs_critical_path hG T hempty hM hu hmany hcard e H hH hi
    change (graph F).Adj x₀ m at hx₀
    change x₀ ≠ y at hn₀
    change ⁅V F x₀ 1 ⊓ Q F y,V F y 1⁆ ≠ ⊥ at hdisp
    obtain ⟨t,ht,htx⟩ := linear_common_sylow_transitive hF true eLin S₀ hS₀ hx₀.symm hxadj hn₀ hne
    have hty : t • y=y :=
      (sup_le (Q_le_stabilizer F y)
        (((source_Z_Q_U (Reduction.reduced_triple hF) m).2).trans
          ((ballKernel_one_le_edge F hadj).trans inf_le_right))) ht
    have hmap : (⁅V F x₀ 1 ⊓ Q F y,V F y 1⁆).map (MulAut.conj t).toMonoidHom=
        ⁅V F x 1 ⊓ Q F y,V F y 1⁆ := by
      rw [map_commutator,map_inf _ _ _ (MulAut.conj t).injective,
        ←V_translate F,←Q_translate F,←V_translate F,htx,hty]
    intro hz
    apply hdisp
    apply map_injective (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
    rw [hmap,hz,Subgroup.map_bot]
  have hnonzeroG : ⁅Rstar,UH⁆ ≠ ⊥ := by
    intro hz
    apply hnonzero
    apply map_injective J.subtype_injective
    rw [map_commutator,hRstarmap,hUmap,Subgroup.map_bot]
    exact hz
  let : IsElementaryAbelian 2 W₀ := hWel
  have hel : IsElementaryAbelian 2 (W₀.map J.subtype) := IsElementaryAbelian.map J.subtype
  rw [hWmap] at hel
  exact ⟨hel,hWcores,hWI,hRW,hWIstar,hnonzeroG⟩


/-- The actual critical conjugator gives an elementary normal span in both
full original cores. Both reciprocal intersections and the nonzero critical
commutator are retained together with the original middle-core product. -/
theorem source_quintic_second_kernel_span
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
    let UH := conjugateSpanBy (localModule T M) H
    ∃ g ∈ X,
      let Ustar := UH.map (MulAut.conj g).toMonoidHom
      let Qstar := (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom
      let I := UH ⊓ Ustar
      let R := UH ⊓ Qstar
      let Rstar := Ustar ⊓ H.pCoreIn 2
      let W := conjugateSpanBy R X
      Ustar ≤ X.pCoreIn 2 ∧ ¬ Ustar ≤ H.pCoreIn 2 ∧
        localModule T M ≤ I ∧ (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        (H.pCoreIn 2 ⊓ X.pCoreIn 2) ⊔ (Qstar ⊓ X.pCoreIn 2) = X.pCoreIn 2 ∧
        ⁅I,X.pCoreIn 2⁆ = localModule T M ∧ UH = ⁅UH,H⁆ ∧
        IsElementaryAbelian 2 W ∧ W ≤ H.pCoreIn 2 ⊓ X.pCoreIn 2 ∧
        X ≤ normalizer (W : Set G) ∧ W ⊓ UH = R ∧ Rstar ≤ W ∧
        W ⊓ Ustar = Rstar ∧ ⁅Rstar,UH⁆ ≠ ⊥ := by
  obtain ⟨g,hg,hDQ,hescape,hVI,hTI,hprod,hIQ,hUH⟩ :=
    source_quintic_middle_core_product hG T hempty hM hu hmany hcard e H hH hi
  obtain ⟨hWel,hWcore,hWI,hRW,hWIstar,hNZ⟩ :=
    second_span_of_original_conjugator hG T hempty hM hu hmany hcard e H hH hi g hg hescape
  exact ⟨g,hg,hDQ,hescape,hVI,hTI,hprod,hIQ,hUH,hWel,hWcore,
    le_normalizer_conjugateSpanBy _ _,hWI,hRW,hWIstar,hNZ⟩

end CFSG.Quasithin.Chapter14.Section06

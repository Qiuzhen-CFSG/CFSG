module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticReciprocalFrattiniKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearComplementTransitivity

/-!
# The full original Frattini subgroup in the cubic third kernel

The reciprocal containment for one escaping neighbor propagates across all
other neighbors through the actual common Sylow. Covering the third ball
by neighboring second balls retains the full embedded Frattini subgroup.
No third-kernel upper bound or positive Suzuki parameter is assumed.
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

/-- The full Frattini image lies in the original cubic third ball kernel. -/
theorem source_quintic_full_kernel_frattini_third_kernel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let J := Reduction.G₀ ![H,X] (T : Subgroup G)
    let F := Reduction.reducedFamily ![H,X] (T : Subgroup G)
    let U := conjugateSpanBy (localModule T M) H
    let C := H ⊓ centralizer (U : Set G)
    (frattini C).map C.subtype ≤ (ballKernel F (base F true) 3).map J.subtype := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := Reduction.G₀ L (T : Subgroup G)
  let F := Reduction.reducedFamily L (T : Subgroup G)
  let y := base F false
  let m := base F true
  let U := conjugateSpanBy (localModule T M) H
  let C := H ⊓ centralizer (U : Set G)
  let P := (frattini C).map C.subtype
  obtain ⟨g,hg,hDQ,hescape,hVI,hTI,hprod,hIQ,hUH,hWel,hWQ,hXW,
      hWU,hWUstar,hRW,hmove,hRcard,hRstarcard,hWcard,hWcomm,hUC,
      hindex,hkernelcard,hWCeq,hWQcomm,hPq,hPc⟩ :=
    source_quintic_same_conjugator_frattini_kernel
      hG T hempty hM hu hmany hcard e H hH hi
  let Ustar := U.map (MulAut.conj g).toMonoidHom
  have hPmap : P ≤ C.map (MulAut.conj g).toMonoidHom := by
    rw [←map_inf_centralizer_of_injective _ (MulAut.conj g).injective]
    exact hPc
  obtain ⟨hF,_,hred,_,hP,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  change HypothesisF11 L (T : Subgroup G) at hF
  change SuzukiContainment.reducedSylow L (T : Subgroup G) = T at hred
  have hXmap : (F true).map J.subtype = X := (hmaps true).1
  have hHmap : (F false).map J.subtype = H := (hmaps false).1
  have hQymap : (Q F y).map J.subtype = H.pCoreIn 2 := (hmaps false).2
  have hHJ : H ≤ J := hHmap ▸ map_subtype_le _
  have hPJ : P ≤ J := (map_subtype_le _).trans (inf_le_left.trans hHJ)
  let P₀ := P.subgroupOf J
  have hP₀map : P₀.map J.subtype = P := map_subgroupOf_eq_of_le hPJ
  have hHC : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_centralizer U))).trans inf_normalizer_le_normalizer_inf
  have hHP : H ≤ normalizer (P : Set G) := hHC.trans
    (normalizer_le_normalizer_characteristic_image C (frattini C))
  have hnP₀ : stabilizer F y ≤ normalizer (P₀ : Set J) := by
    intro t ht
    have htH : (t : G) ∈ H := by
      rw [←hHmap]
      have ht' : t ∈ F false := by
        change t ∈ stabilizer F (base F false) at ht
        simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using ht
      exact mem_map_of_mem J.subtype ht'
    apply mem_normalizer_iff.mpr
    intro z
    exact mem_normalizer_iff.mp (hHP htH) (z : G)
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
  obtain ⟨hfirst,hUmap,hCmap⟩ :=
    source_quintic_dgs_span_and_full_kernel hG T hempty hM hu hmany hcard e H hH hi
  change (V F y 1).map J.subtype = U at hUmap
  change (ballKernel F y 2).map J.subtype = C at hCmap
  have hUx : (V F x 1).map J.subtype = Ustar := by
    rw [show x=g₀ • y from rfl,V_translate,map_conjugate_inclusion,hUmap,hg₀eq]
  have hCx : (ballKernel F x 2).map J.subtype = C.map (MulAut.conj g).toMonoidHom := by
    rw [show x=g₀ • y from rfl,ballKernel_translate,map_conjugate_inclusion,hCmap,hg₀eq]
  have hP₀y : P₀ ≤ ballKernel F y 2 := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [hP₀map,hCmap]
    exact map_subtype_le _
  have hP₀x : P₀ ≤ ballKernel F x 2 := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [hP₀map,hCx]
    exact hPmap
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
  have hPkernels (z : Vertex F) (hz : (graph F).Adj m z) : P₀ ≤ ballKernel F z 2 := by
    by_cases hzy : z = y
    · simpa only [hzy] using hP₀y
    obtain ⟨t,ht,htx⟩ := linear_common_sylow_transitive hF true eLin S₀ hS₀ hxadj hz hne hzy
    have hty : t ∈ stabilizer F y :=
      (sup_le (Q_le_stabilizer F y)
        (((source_Z_Q_U (Reduction.reduced_triple hF) m).2).trans
          ((ballKernel_one_le_edge F hadj).trans inf_le_right))) ht
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hP₀x
    have hPt : P₀.map (MulAut.conj t).toMonoidHom = P₀ :=
      mem_normalizer_iff_map_conj_eq.mp (hnP₀ hty)
    rwa [hPt,←ballKernel_translate F,htx] at hh
  have hP₀N : P₀ ≤ ballKernel F m 3 := by
    intro t ht z hz
    have hdist : (graph F).edist m z ≠ ⊤ := ne_top_of_le_ne_top
      (by simp : ((3 : ℕ) : ℕ∞) ≠ ⊤) hz
    obtain ⟨p,hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hdist
    have hlen : p.length ≤ 3 := ENat.natCast_le_natCast.mp (hp ▸ hz)
    cases p with
    | nil => exact ((ballKernel_succ_le F hadj.symm 1).trans
        (ballKernel_le_stabilizer F m 1)) (hP₀y ht)
    | @cons _ u _ hu p =>
      exact hPkernels u hu ht z (p.edist_le.trans
        (ENat.natCast_le_natCast.mpr (by have hh : p.length + 1 ≤ 3 := hlen; omega)))
  change P ≤ (ballKernel F m 3).map J.subtype
  rw [←hP₀map]
  exact map_mono hP₀N

end CFSG.Quasithin.Chapter14.Section06

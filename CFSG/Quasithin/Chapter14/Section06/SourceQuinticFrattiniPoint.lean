module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFrattiniThirdKernel
public import Theory.GroupTheory.AmalgamGraph.NormalTwoDetection
public import Theory.ElementaryAbelian.Join
public import Theory.Frattini.Intersection

/-!
# The full original quintic Frattini bound

The cubic third kernel lies in the full quintic kernel, so its Frattini
image lies in the original Phi(C). Its intersection with the cubic center
plane lies in the original central line. Cubic normality and centerlessness
make that intersection trivial; Sylow-center detection makes the third
kernel elementary. It centralizes the actual middle span W. The elementary
bound on their join, together with |W| = 32, absorbs the third kernel into
W. The exact W-cap-C identity then puts the full Phi(C) in U and hence ZT.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normal_in_centerless_le_line_eq_bot
    (A D Z : Subgroup G) (hDA : D ≤ A) (hDZ : D ≤ Z)
    (hn : A ≤ normalizer (D : Set G)) (hA : center A = ⊥)
    (hZ : Nat.card Z = 2) : D = ⊥ := by
  let : (D.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hn
  have hc : Nat.card (D.subgroupOf A) = Nat.card D :=
    Nat.card_congr (subgroupOfEquivOfLe hDA).toEquiv
  have hd : Nat.card (D.subgroupOf A) ∣ 2 := by
    rw [hc,←hZ]
    exact card_dvd_of_le hDZ
  have hb : D.subgroupOf A = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact card_eq_one.mp h1
    · exact bot_unique ((central_of_normal_card_two _ h2).trans hA.le)
  have hh := congrArg (Subgroup.map A.subtype) hb
  simpa only [map_subgroupOf_eq_of_le hDA,Subgroup.map_bot] using hh

/-- The full embedded Frattini subgroup of the literal quintic kernel lies
in the original central line, without a bound on the kernel as a premise. -/
theorem source_quintic_full_kernel_frattini_le_point
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
    let U := conjugateSpanBy (localModule T M) H
    let C := H ⊓ centralizer (U : Set G)
    (frattini C).map C.subtype ≤ centralInvolutions T := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := Reduction.G₀ L (T : Subgroup G)
  let F := Reduction.reducedFamily L (T : Subgroup G)
  let V := localModule T M
  let U := conjugateSpanBy V H
  let C := H ⊓ centralizer (U : Set G)
  let P := (frattini C).map C.subtype
  let N₀ := ballKernel F (base F true) 3
  let N := N₀.map J.subtype
  let D := (frattini N).map N.subtype
  have hPN : P ≤ N := source_quintic_full_kernel_frattini_third_kernel
    hG T hempty hM hu hmany hcard e H hH hi
  obtain ⟨_,_,_,_,_,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  have hXmap : (F true).map J.subtype = X := (hmaps true).1
  have hadj : (graph F).Adj (base F true) (base F false) :=
    ⟨by change (true : Bool) ≠ false; decide,
      Subgroup.CosetGeometry.incident_base F true false⟩
  obtain ⟨hfirst,_,hCmap⟩ :=
    source_quintic_dgs_span_and_full_kernel hG T hempty hM hu hmany hcard e H hH hi
  change (ballKernel F (base F false) 2).map J.subtype = C at hCmap
  have hNC : N ≤ C := by
    rw [←hCmap]
    exact map_mono (ballKernel_succ_le F hadj 2)
  have hNQX : N ≤ X.pCoreIn 2 := by
    have hmap : (ballKernel F (base F true) 1).map J.subtype = X.pCoreIn 2 :=
      (hfirst true).2
    rw [←hmap]
    exact map_mono (ballKernel_antitone F (base F true) (by decide : 1 ≤ 3))
  have hXN : X ≤ normalizer (N : Set G) := by
    have hh := map_mono (f := J.subtype)
      (stabilizer_le_normalizer_ballKernel F (base F true) 3)
    rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base,hXmap] at hh
    exact hh.trans (N₀.le_normalizer_map J.subtype)
  have hCQ : C ≤ H.pCoreIn 2 := source_quintic_span_centralizer_le_core hG T hM H hH hi
  have hpC : IsPGroup 2 C := (isPGroup_pCoreIn 2 H).to_le hCQ
  have hpN : IsPGroup 2 N := hpC.to_le hNC
  have hDP : D ≤ P := frattini_image_le_of_le hNC hpC
  have hDX : D ≤ X := (map_subtype_le _).trans (hNQX.trans (pCoreIn_le 2 X))
  have hXD : X ≤ normalizer (D : Set G) := hXN.trans
    (normalizer_le_normalizer_characteristic_image N (frattini N))
  have hXV : X ≤ normalizer (V : Set G) := by
    rw [←InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
    exact sup_le (sourceResidual_le M Mc) hM.1.2
  have hDcap : D ⊓ V ≤ centralInvolutions T :=
    (inf_le_inf hDP (le_conjugateSpanBy V H)).trans
      (source_quintic_full_kernel_frattini_span_intersection
        hG T hempty hM hu hmany hcard e H hH hi)
  have hcapbot : D ⊓ V = ⊥ := normal_in_centerless_le_line_eq_bot X (D ⊓ V)
    (centralInvolutions T) (inf_le_left.trans hDX) hDcap
    ((le_inf hXD hXV).trans inf_normalizer_le_normalizer_inf)
    (source_quintic_cubic_natural_center hG T hempty hM hu hmany hcard e H hH hi).1
    (plane_centralInvolutions_card T M hM.1.2 hcard e)
  have hspan : sylowCenterSpan X = V := by
    have hh := (source_quintic_dgs_center_markings
      hG T hempty hM hu hmany hcard e H hH hi).2
    change (Z F (base F true)).map J.subtype = V at hh
    rw [Z,stabilizer,Subgroup.CosetGeometry.stabilizer_base,
      ←sylowCenterSpan_map_of_injective J.subtype J.subtype_injective,hXmap] at hh
    exact hh
  have hDbot : D = ⊥ := normal_two_eq_bot_of_disjoint_sylowCenterSpan X D hDX
    ((hpN.to_subgroup (frattini N)).map N.subtype) hXD
    (by rw [hspan]; exact disjoint_iff.mpr hcapbot)
  let : Fact (IsPGroup 2 N) := ⟨hpN⟩
  let : IsElementaryAbelian 2 N := frattini_eq_bot_iff_isElementaryAbelian.mp
    ((map_eq_bot_iff_of_injective (frattini N) N.subtype_injective).mp hDbot)
  obtain ⟨g,hg,hDQ,hescape,hVI,hTI,hprod,hIQ,hUH,hWel,hWQ,hXW,
      hWU,hWUstar,hRW,hmove,hRcard,hRstarcard,hWcard,hWcomm,hUC,
      hindex,hkernelcard,hWCeq,hWQcomm⟩ :=
    source_quintic_second_kernel_span_strong_full hG T hempty hM hu hmany hcard e H hH hi
  let R := U ⊓ (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom
  let W := conjugateSpanBy R X
  let : IsElementaryAbelian 2 W := hWel
  have hNW : N ≤ centralizer (W : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes N R X hXN
      ((hNC.trans inf_le_right).trans (centralizer_le inf_le_left))
  let : IsElementaryAbelian 2 (W ⊔ N : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hNW
  have hNcores : N ≤ H.pCoreIn 2 ⊓ X.pCoreIn 2 := le_inf (hNC.trans hCQ) hNQX
  have hXjoin : X ≤ normalizer ((W ⊔ N : Subgroup G) : Set G) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (hXW hx),
      mem_normalizer_iff_map_conj_eq.mp (hXN hx)]
  have hbound : Nat.card (W ⊔ N : Subgroup G) ≤ 32 :=
    source_quintic_elementary_normal_core_card hG T hempty hM hu hmany hcard e H hH hi
      (W ⊔ N) (sup_le hWQ hNcores) hXjoin
  have hjoin : W = W ⊔ N := eq_of_le_of_card_ge le_sup_left (by rwa [hWcard])
  have hNU : N ≤ U := by
    have hh : N ≤ W ⊓ C := le_inf (le_sup_right.trans hjoin.ge) hNC
    exact (hh.trans_eq hWCeq).trans inf_le_left
  exact (le_inf le_rfl (hPN.trans hNU)).trans
    (source_quintic_full_kernel_frattini_span_intersection
      hG T hempty hM hu hmany hcard e H hH hi)

end CFSG.Quasithin.Chapter14.Section06

module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.ConstructionOmega
public import Theory.GroupTheory.CyclicSL23AbelianConjugates

/-!
# The original point is outside the opposite centralizer's two-core

Inside the literal C₄*SL₂(3) residual centralizer, the source plane cannot
centralize its conjugate span. If z belonged to O₂(C_G(w)), its centrality
in the original T and the cubic actor would put the whole plane in the
center of that normal two-core. Normality under C_H(w) contradicts the
residual calculation. All groups and conjugations retain their source marks.

The same residual calculation makes the global two-core disjoint from
C_{O²(H)}(w), so it centralizes that subgroup. The extraspecial double
centralizer and the cyclic supplement then give N∩Q=⟨w⟩. The cubic orbit
excludes N∩R, and the core of LT excludes N∩I₂. Finally the original
abelian transfer quotient makes N central in C_H(w); it also centralizes
C_{I₂}(w). The existence theorem applies every bound to the constructed w.

These are the two-core bounds in Aschbacher--Smith 14.3.22, printed p.999.
The remaining small-normal-subgroup calculation proving N=⟨w⟩, the G₂(2)
quotient and RQ marking, and final core collapse remain with
qt-e-14322-core-collapse.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs


/-- The source plane does not centralize its span under the literal point
centralizer of w. This uses its C₄*SL₂(3) residual subgroup. -/
theorem source_opposite_plane_not_central
    {z w : G} (hlocal : LocalGeometry F (sourceResidual M Mc) z w) :
    ¬ rankTwoSeed T M ≤ centralizer
      (conjugateSpanBy (rankTwoSeed T M) (F.H ⊓ centralizer ({w}:Set G)) : Set G) := by
  intro hcentral
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hUK := U_le_embedded_twoResidual_of_full_orthogonal F dg hZ hne hr
  obtain ⟨E,B,⟨eE⟩,⟨eB⟩,hEB,hinter,hjoin⟩ := hlocal.residual_centralizer
  have hz : z∈E⊓B := hinter.symm ▸ (hlocal.point.symm ▸ mem_zpowers z)
  let : IsCyclic E := isCyclic_of_injective eE.toMonoidHom eE.injective
  have hz2 : orderOf z=2 := by
    rw [←Nat.card_zpowers,←hlocal.point]
    simpa using F.card 1 (by decide)
  have hBK : B≤localResidual F ⊓ centralizer ({w}:Set G) := hjoin ▸ le_sup_right
  have hBH : B≤F.H ⊓ centralizer ({w}:Set G) :=
    le_inf (hBK.trans inf_le_left |>.trans (map_subtype_le _)) (hBK.trans inf_le_right)
  have hVZ : rankTwoSeed T M≤zpowers z := by
    intro x hx
    apply cyclic_sl23_abelian_conjugates E B eB hEB z hz.1 hz.2 hz2 x
    · rw [hjoin]
      exact ⟨hUK (le_conjugateSpanBy _ _ hx),hlocal.plane_centralizes hx⟩
    · exact elemPow_eq_one_of_isElementaryAbelian x hx
    · intro c hcB
      have hm : c*x*c⁻¹∈conjugateSpanBy (rankTwoSeed T M)
          (F.H ⊓ centralizer ({w}:Set G)) := subset_closure ⟨c,hBH hcB,x,hx,rfl⟩
      exact (hcentral hx _ hm).symm
  have hcV : Nat.card (rankTwoSeed T M)=4 := by simpa [F.last] using F.card 2 (by decide)
  have hh := Nat.card_le_card_of_injective (inclusion hVZ) (inclusion_injective hVZ)
  rw [hcV,Nat.card_zpowers,hz2] at hh
  omega

include hc s
/-- If the original point belonged to O₂(C_G(w)), the cubic orbit would put
V in its center. Normality under C_H(w) contradicts the actual plane span. -/
theorem source_triple_point_not_mem_twoCore
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    z ∉ (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2 := by
  intro hzN
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let w := tripleProduct d a
  let C := centralizer ({w}:Set G)
  let N := C.pCoreIn 2
  let ZN := _root_.centerIn N
  have hlocal := source_triple_local_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨S,hS⟩ := source_triple_global_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hNT : N≤(T:Subgroup G) := ((pCoreIn_le_sylow C S).trans_eq hS).trans inf_le_left
  have hCN : C≤normalizer (N:Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hCZN : C≤normalizer (ZN:Set G) := normalizes_centerIn hCN
  have hzV : z∈rankTwoSeed T M := F.le_seed 1 (s.point.symm ▸ mem_zpowers z)
  have hz2 : orderOf z=2 := by
    rw [←Nat.card_zpowers,←s.point]
    simpa using F.card 1 (by decide)
  have hz1 : z≠1 := by intro hh; simp [hh] at hz2
  have hzt : (T:Subgroup G)≤centralizer ({z}:Set G) :=
    (F.invariant 1).trans_eq (F.H_eq_centralizer (by decide) z s.point)
  have hzZN : z∈ZN := ⟨hzN,fun x hx => mem_centralizer_singleton_iff.mp (hzt (hNT hx))⟩
  have heq : rankTwoSeed T M ⊓ ZN=rankTwoSeed T M := by
    apply invariant_four_eq_of_fixed_free (rankTwoSeed T M) (rankTwoSeed T M ⊓ ZN) a
      (by simpa [F.last] using F.card 2 (by decide)) inf_le_left
    · intro hh
      exact hz1 (mem_bot.mp (hh ▸ (show z∈rankTwoSeed T M ⊓ ZN from ⟨hzV,hzZN⟩)))
    · exact inf_normalizer_le_normalizer_inf
        ⟨h.L_normalizes_seed s.actor_mem,hCZN (s.actor_centralizes_product hc)⟩
    · apply bot_unique
      intro v hv
      exact s.actor_fixed ▸ (show v∈(F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓ centralizer ({a}:Set G)
        from ⟨s.seed_le_core hv.1,hv.2⟩)
  have hVZN : rankTwoSeed T M≤ZN := heq ▸ inf_le_right
  have hspan : conjugateSpanBy (rankTwoSeed T M) (F.H⊓C)≤ZN :=
    conjugateSpanBy_le hVZN (inf_le_right.trans hCZN)
  apply source_opposite_plane_not_central hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hlocal
  exact hVZN.trans (inf_le_right.trans (centralizer_le (hspan.trans inf_le_left)))


/-- The global two-core has trivial intersection with the actual residual
centralizer. The shared involution is essential to this conclusion. -/
theorem source_triple_twoCore_inf_residual_eq_bot
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2 ⊓
      (localResidual F ⊓ centralizer ({tripleProduct d a}:Set G))=⊥ := by
  let C := centralizer ({tripleProduct d a}:Set G)
  let N := C.pCoreIn 2
  let K := localResidual F ⊓ C
  have hlocal := source_triple_local_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨E,B,⟨eE⟩,⟨eB⟩,hEB,hinter,hjoin⟩ := hlocal.residual_centralizer
  let : IsCyclic E := isCyclic_of_injective eE.toMonoidHom eE.injective
  have hz : z∈E⊓B := hinter.symm ▸ (s.point.symm ▸ mem_zpowers z)
  have hz2 : orderOf z=2 := by
    rw [←Nat.card_zpowers,←s.point]
    simpa using F.card 1 (by decide)
  have hCN : C≤normalizer (N:Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hKN : K≤normalizer (N⊓K:Set G) :=
    (le_inf (inf_le_right.trans hCN) K.le_normalizer).trans inf_normalizer_le_normalizer_inf
  apply cyclic_sl23_normal_twoSubgroup_eq_bot E B (N⊓K) eB hEB
    (inf_le_right.trans hjoin.ge) (hjoin.symm ▸ hKN)
    ((isPGroup_pCoreIn 2 C).of_injective (inclusion (show N⊓K≤N from inf_le_left))
      (inclusion_injective _)) z hz.1 hz.2 hz2
  intro hzNK
  exact source_triple_point_not_mem_twoCore hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hzNK.1

/-- The original global two-core centralizes the entire C₄*SL₂(3)
residual centralizer, not just its Sylow subgroup. -/
theorem source_triple_twoCore_centralizes_residual
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2 ≤
      centralizer ((localResidual F ⊓ centralizer ({tripleProduct d a}:Set G) : Subgroup G) : Set G) := by
  let C := centralizer ({tripleProduct d a}:Set G)
  let N := C.pCoreIn 2
  let K := localResidual F ⊓ C
  obtain ⟨S,hS⟩ := source_triple_global_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hNH : N≤F.H := (((pCoreIn_le_sylow C S).trans_eq hS).trans inf_le_left).trans (F.invariant 1)
  have hNK : N≤normalizer (K:Set G) :=
    (le_inf (hNH.trans (le_normalizer_embedded_pResidual 2 F.H))
      ((pCoreIn_le 2 C).trans C.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hKN : K≤normalizer (N:Set G) := inf_le_right.trans (C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C)))
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  have hh : ⁅N,K⁆≤N⊓K := le_inf
    (le_normalizer_iff_commutator_le_left.mp hKN) (le_normalizer_iff_commutator_le_right.mp hNK)
  exact hh.trans_eq (source_triple_twoCore_inf_residual_eq_bot
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself)


/-- The double centralizer inside U of its opposite fixed subgroup is the
literal cyclic subgroup generated by dᵃdᵃ². -/
theorem source_triple_U_double_centralizer :
    let w := tripleProduct d a
    let t := (MulAut.conj a⁻¹) d * (MulAut.conj (a^2)⁻¹) d
    F.U ⊓ centralizer ((F.U ⊓ centralizer ({w}:Set G) : Subgroup G) : Set G)=zpowers t := by
  intro w t
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  let : IsExtraspecial 2 F.U := dU.extraspecial
  obtain ⟨htU,ht2,ht4,_⟩ := source_triple_pair_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  have hUK := U_le_embedded_twoResidual_of_full_orthogonal F dg hZ hne hr
  have hCC : F.U⊓centralizer ({w}:Set G)=F.U⊓centralizer ({t}:Set G) := by
    calc
      _ = F.U⊓(localResidual F⊓centralizer ({w}:Set G)) := by rw [←inf_assoc,inf_eq_left.mpr hUK]
      _ = F.U⊓(localResidual F⊓centralizer ({t}:Set G)) := congrArg (F.U⊓·)
        (source_triple_residual_centralizer_reduction hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s).2
      _ = _ := by rw [←inf_assoc,inf_eq_left.mpr hUK]
  let tt : F.U := ⟨t,htU⟩
  let C := centralizer ({tt}:Set F.U)
  have hmap : C.map F.U.subtype=F.U⊓centralizer ({w}:Set G) :=
    (map_subtype_centralizer_singleton F.U tt).trans hCC.symm
  have hCc : Nat.card C=16 := by
    rw [←card_map_of_injective F.U.subtype_injective,hmap]
    exact (source_triple_residual_centralizer_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s).1
  have hCi : C.index=2 := by
    have hh := C.card_mul_index
    rw [hCc,dU.card] at hh
    omega
  apply le_antisymm
  · intro x hx
    have hm : (⟨x,hx.1⟩:F.U)∈center F.U⊔zpowers tt := extraspecial_double_centralizer_le tt hCi
      (fun c hcC => Subtype.ext (hx.2 c (hmap ▸ mem_map_of_mem F.U.subtype hcC)))
    have hh := mem_map_of_mem F.U.subtype hm
    rw [Subgroup.map_sup,MonoidHom.map_zpowers] at hh
    change x∈F.ZU⊔zpowers t at hh
    rw [hZ,s.point,sup_eq_right.mpr (zpowers_le.mpr (show z∈zpowers t by
      rw [←ht2];exact (zpowers t).pow_mem (mem_zpowers t) 2))] at hh
    exact hh
  · apply zpowers_le.mpr
    refine ⟨htU,?_⟩
    intro x hx
    have hx' := hCC ▸ hx
    exact mem_centralizer_singleton_iff.mp hx'.2

/-- Intersecting the global two-core with the original Q gives exactly W.
This uses the literal pair and cyclic supplement, without identifying Q=U. -/
theorem source_triple_twoCore_inf_Q
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2 ⊓ F.H.pCoreIn 2 =
      zpowers (tripleProduct d a) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  let w := tripleProduct d a
  let t := (MulAut.conj a⁻¹) d * (MulAut.conj (a^2)⁻¹) d
  let D := supplement F
  let N := (centralizer ({w}:Set G)).pCoreIn 2
  let P := F.U⊓centralizer ({w}:Set G)
  let := hc.cyclic
  obtain ⟨htU,_,_,hwt⟩ := source_triple_pair_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  change w=d*t at hwt
  have hdD : d∈D := by
    change d∈supplement F
    rw [←s.generator]
    exact mem_zpowers d
  have hWN : zpowers w≤N := by
    have hw2 : w^2=1 := (s.product_mem_sylow_and_square hc).2
    let : IsElementaryAbelian 2 (zpowers w) := IsElementaryAbelian.zpowers_of_pow_eq_one hw2
    apply le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup (p:=2) (G:=zpowers w))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    have he : centralizer (zpowers w:Set G)=centralizer ({w}:Set G) := by
      rw [zpowers_eq_closure,centralizer_closure]
    exact he ▸ Subgroup.centralizer_le_normalizer _
  have hzD : z∈D := hc.strict.le (s.point.symm ▸ mem_zpowers z)
  have hz2 : orderOf z=2 := by
    rw [←Nat.card_zpowers,←s.point]
    simpa using F.card 1 (by decide)
  have hzN : z∉N := source_triple_point_not_mem_twoCore hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hND : N⊓D=⊥ := by
    have hbot : N.subgroupOf D=⊥ := by
      by_contra hneND
      have htwo : IsPGroup 2 D := (isPGroup_pCoreIn 2 F.H).to_le inf_le_left
      exact hzN (htwo.involution_mem_subgroup_of_ne_bot
        (x:=⟨z,hzD⟩) ((orderOf_coe (⟨z,hzD⟩:D)).symm.trans hz2) (N.subgroupOf D) hneND)
    apply bot_unique
    intro x hx
    have hm : (⟨x,hx.2⟩:D)∈N.subgroupOf D := hx.1
    rw [hbot,mem_bot] at hm
    exact mem_bot.mpr (congrArg Subtype.val hm)
  have hUK := U_le_embedded_twoResidual_of_full_orthogonal F dg hZ hne hr
  have hNC : N≤centralizer (P:Set G) :=
    (source_triple_twoCore_centralizes_residual hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).trans
      (centralizer_le (show P≤localResidual F⊓centralizer ({w}:Set G) from inf_le_inf_right _ hUK))
  have hDW : D≤centralizer ({w}:Set G) := by
    intro q hq
    have hqd : Commute q d := congrArg Subtype.val (mul_comm' (⟨q,hq⟩:D) ⟨d,hdD⟩)
    have hqt : Commute q t := (hq.2 t htU).symm
    exact mem_centralizer_singleton_iff.mpr (hwt.symm ▸ (hqd.mul_right hqt).eq)
  have hWD : zpowers w≤normalizer (D:Set G) :=
    (zpowers_le.mpr (show w∈centralizer (D:Set G) from fun q hq =>
      mem_centralizer_singleton_iff.mp (hDW hq))).trans (Subgroup.centralizer_le_normalizer _)
  have htDW : t∈D⊔zpowers w := by
    have hh := (D⊔zpowers w).mul_mem (mem_sup_left (D.inv_mem hdD)) (mem_sup_right (mem_zpowers w))
    simpa only [hwt,inv_mul_cancel_left] using hh
  apply le_antisymm
  · intro x hx
    have hxQ := hx.2
    rw [core_eq_U_sup_centralizer F dg hZ dU] at hxQ
    change x∈(↑(F.U⊔D):Set G) at hxQ
    rw [coe_mul_of_right_le_normalizer_left _ _
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))] at hxQ
    obtain ⟨u,huU,b,hb,hub⟩ := hxQ
    have huC : u∈centralizer (P:Set G) := by
      have hbC : b∈centralizer (P:Set G) := (centralizer_le (show P≤F.U from inf_le_left)) hb.2
      have hh := (centralizer (P:Set G)).mul_mem (hNC hx.1) ((centralizer (P:Set G)).inv_mem hbC)
      have hub' : u*b=x := hub
      simpa only [←hub',mul_inv_cancel_right] using hh
    have huT : u∈zpowers t := (source_triple_U_double_centralizer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s) ▸ ⟨huU,huC⟩
    have hxDW : x∈(↑(D⊔zpowers w):Set G) := hub ▸
      (D⊔zpowers w).mul_mem ((zpowers_le.mpr htDW) huT) (mem_sup_left hb)
    rw [coe_mul_of_right_le_normalizer_left D (zpowers w) hWD] at hxDW
    obtain ⟨q,hq,y,hy,hqy⟩ := hxDW
    have hqN : q∈N := by
      have hh := N.mul_mem hx.1 (N.inv_mem (hWN hy))
      have hqy' : q*y=x := hqy
      simpa only [←hqy',mul_inv_cancel_right] using hh
    have hq1 : q=1 := mem_bot.mp (hND ▸ (show q∈N⊓D from ⟨hqN,hq⟩))
    have hxy : x=y := by simpa only [hq1,one_mul] using hqy.symm
    exact hxy ▸ hy
  · refine le_inf hWN ?_
    apply zpowers_le.mpr
    rw [core_eq_U_sup_centralizer F dg hZ dU]
    have hh : w∈F.U⊔D := hwt.symm ▸ (F.U⊔D).mul_mem (mem_sup_right hdD) (mem_sup_left htU)
    exact hh


/-- The global two-core misses R. Any nontrivial intersection would have
an involution in V; the fixed-free cubic orbit then forces z into the core. -/
theorem source_triple_twoCore_inf_R
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2 ⊓
      (F.I₂ (sourceResidual M Mc)).pCoreIn 2=⊥ := by
  let C := centralizer ({tripleProduct d a}:Set G)
  let N := C.pCoreIn 2
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let V := rankTwoSeed T M
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hzN := source_triple_point_not_mem_twoCore hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hCN : C≤normalizer (N:Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hVN : V⊓N=⊥ := by
    by_contra hneVN
    have heq : V⊓N=V := invariant_four_eq_of_fixed_free V (V⊓N) a
      (by simpa [V,F.last] using F.card 2 (by decide)) inf_le_left hneVN
      (inf_normalizer_le_normalizer_inf
        ⟨h.L_normalizes_seed s.actor_mem,hCN (s.actor_centralizes_product hc)⟩) (by
          apply bot_unique
          intro v hv
          exact s.actor_fixed ▸ (show v∈R⊓centralizer ({a}:Set G) from ⟨s.seed_le_core hv.1,hv.2⟩))
    have hzV : z∈V := F.le_seed 1 (s.point.symm ▸ mem_zpowers z)
    exact hzN ((heq.symm ▸ hzV).2)
  have htwo : IsPGroup 2 (N⊓R:Subgroup G) := (isPGroup_pCoreIn 2 C).to_le inf_le_left
  rcases htwo.card_eq_or_dvd with hh|hh
  · exact Subgroup.card_eq_one.mp hh
  · obtain ⟨v,hv2⟩ := exists_prime_orderOf_dvd_card' (G:=(N⊓R:Subgroup G)) 2 hh
    have hvX : (v:G)∈span F⊓R :=
      (source_triple_core_centralizer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s).1 ▸
        (show (v:G)∈R⊓C from ⟨v.property.2,pCoreIn_le 2 C v.property.1⟩)
    have hvpow : (v:G)^2=1 := congrArg Subtype.val (hv2 ▸ pow_orderOf_eq_one v)
    have hvV : (v:G)∈V := by
      change (v:G)∈rankTwoSeed T M
      rw [←source_span_parabolic_core_omega hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s]
      exact (omegaOneAmbient_le_iff (span F⊓R) (omegaOneAmbient (span F⊓R))).mp le_rfl v hvX hvpow
    have hv1 : (v:G)=1 := mem_bot.mp (hVN ▸ (show (v:G)∈V⊓N from ⟨hvV,v.property.1⟩))
    have hv1' : v=1 := Subtype.ext hv1
    simp [hv1'] at hv2

/-- The two-core of C_G(w) is inside the original core of LT. -/
theorem source_triple_twoCore_le_parabolic_core
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2 ≤
      (sourceResidual M Mc⊔(T:Subgroup G)).pCoreIn 2 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hUK := U_le_embedded_twoResidual_of_full_orthogonal F dg hZ hne hr
  have hlocal := source_triple_local_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨S,hS⟩ := source_triple_global_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hNT := ((pCoreIn_le_sylow _ S).trans_eq hS).trans inf_le_left
  have hNV : (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2 ≤ centralizer (rankTwoSeed T M:Set G) :=
    (source_triple_twoCore_centralizes_residual hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).trans
      (centralizer_le (le_inf ((le_conjugateSpanBy _ _).trans hUK) hlocal.plane_centralizes))
  rw [←h.centralizer]
  exact le_inf (hNT.trans le_sup_right) hNV

/-- The two-core has trivial intersection with I₂ and centralizes its
literal opposite centralizer. -/
theorem source_triple_twoCore_parabolic_centralizer
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let C := centralizer ({tripleProduct d a}:Set G)
    C.pCoreIn 2⊓F.I₂ (sourceResidual M Mc)=⊥ ∧
      C.pCoreIn 2≤centralizer ((F.I₂ (sourceResidual M Mc)⊓C:Subgroup G):Set G) := by
  intro C
  let N := C.pCoreIn 2
  let I := F.I₂ (sourceResidual M Mc)
  let J := sourceResidual M Mc⊔(T:Subgroup G)
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hUI : F.U≤I := le_conjugateSpanBy _ _
  have hUT : F.U≤(T:Subgroup G) := normalized_pSubgroup_le_sylow T F.H F.U
    (F.invariant 1) F.U_le_H (le_normalizer_conjugateSpanBy _ _) (rankTwo_closure_geometry h F hne).two
  have hIJ : I≤J := conjugateSpanBy_le (hUT.trans le_sup_right) (inf_le_left.trans J.le_normalizer)
  have hNcore : N≤J.pCoreIn 2 := source_triple_twoCore_le_parabolic_core
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hNI : N⊓I=⊥ := bot_unique (by
    have hh : N⊓I≤N⊓I.pCoreIn 2 := le_inf inf_le_left
      ((le_inf inf_le_right (inf_le_left.trans hNcore)).trans (inf_pCoreIn_le_of_le 2 hIJ))
    exact hh.trans_eq (source_triple_twoCore_inf_R hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself))
  refine ⟨hNI,?_⟩
  have hNP : N≤F.P (sourceResidual M Mc) := by
    rw [F.P_rankTwo]
    exact hNcore.trans (pCoreIn_le 2 J)
  have hNK : N≤normalizer (I⊓C:Set G) :=
    (le_inf (hNP.trans (le_normalizer_conjugateSpanBy _ _))
      ((pCoreIn_le 2 C).trans C.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hKN : I⊓C≤normalizer (N:Set G) := inf_le_right.trans (C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C)))
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  exact (le_inf (le_normalizer_iff_commutator_le_left.mp hKN)
    ((le_normalizer_iff_commutator_le_right.mp hNK).trans inf_le_left)).trans_eq hNI


/-- The actual two-core is central in C_H(w). The abelian transfer quotient
and its literal Sylow intersection remove its commutators with C_H(w). -/
theorem source_triple_twoCore_central_in_point_centralizer
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    (centralizer ({tripleProduct d a}:Set G)).pCoreIn 2 ≤
      _root_.centerIn (F.H⊓centralizer ({tripleProduct d a}:Set G)) := by
  let C := centralizer ({tripleProduct d a}:Set G)
  let N := C.pCoreIn 2
  let I := F.I₂ (sourceResidual M Mc)
  let B := localResidual F⊔I.pCoreIn 2
  let Hc := F.H⊓C
  have hlocal := source_triple_local_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨S,hS⟩ := source_triple_global_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hNT : N≤(T:Subgroup G) := ((pCoreIn_le_sylow C S).trans_eq hS).trans inf_le_left
  have hNH : N≤F.H := hNT.trans (F.invariant 1)
  have hNHC : N≤Hc := le_inf hNH (pCoreIn_le 2 C)
  have hCN : C≤normalizer (N:Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hHderived : ⁅F.H,F.H⁆≤B := by
    let BB := B.subgroupOf F.H
    let : BB.Normal := hlocal.quotient_normal
    have hcardBB : Nat.card (F.H⧸BB)=2^2 := hlocal.quotient_index
    have hab : IsMulCommutative (F.H⧸BB) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcardBB
    have hle : _root_.commutator F.H≤BB := Normal.quotient_commutative_iff_commutator_le.mp hab
    rw [←map_subtype_commutator]
    rintro _ ⟨x,hx,rfl⟩
    exact hle hx
  have hcommN : ⁅N,Hc⁆≤N := le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hCN)
  have hcommI : ⁅N,Hc⁆≤I := by
    have hle : ⁅N,Hc⁆≤B⊓(T:Subgroup G) :=
      le_inf ((commutator_mono hNH inf_le_left).trans hHderived) (hcommN.trans hNT)
    have heq := (source_transfer_subgroup_sylow hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2
    exact (hle.trans_eq heq).trans (sup_le (le_conjugateSpanBy _ _) (pCoreIn_le 2 I))
  have hbot : ⁅N,Hc⁆=⊥ := bot_unique ((le_inf hcommN hcommI).trans_eq
    (source_triple_twoCore_parabolic_centralizer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).1)
  exact le_inf hNHC (commutator_eq_bot_iff_le_centralizer.mp hbot)


omit s in
/-- The complete local construction supplies the same opposite involution
with its source two-core exclusions and centralizer bounds. There is no
assumed core equality or recognition callback. -/
theorem source_opposite_core_bounds_of_cyclicTI
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    ∃ z w : G, LocalGeometry F (sourceResidual M Mc) z w ∧
      z∉(centralizer ({w}:Set G)).pCoreIn 2 ∧
      (centralizer ({w}:Set G)).pCoreIn 2⊓F.H.pCoreIn 2=zpowers w ∧
      (centralizer ({w}:Set G)).pCoreIn 2≤_root_.centerIn (F.H⊓centralizer ({w}:Set G)) ∧
      (centralizer ({w}:Set G)).pCoreIn 2⊓F.I₂ (sourceResidual M Mc)=⊥ ∧
      (centralizer ({w}:Set G)).pCoreIn 2≤
        centralizer ((F.I₂ (sourceResidual M Mc)⊓centralizer ({w}:Set G):Subgroup G):Set G) := by
  obtain ⟨z,d,a,s,_,_⟩ := source_triple_involution hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc
  refine ⟨z,tripleProduct d a,
    source_triple_local_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself,
    source_triple_point_not_mem_twoCore hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself,
    source_triple_twoCore_inf_Q hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself,
    source_triple_twoCore_central_in_point_centralizer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself,?_⟩
  exact source_triple_twoCore_parabolic_centralizer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer

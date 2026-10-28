module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry.Core
public import Theory.GroupAction.FixedIndexTwoResidual
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.SylowCentralizerOfNormalizer
/-!
# The adjacent and remote Sylow distinctions on the common flag

Conjugating the fixed-plane centralizer by the original exchanging element
gives [S:C_T(V)]=2. An incident root in the adjacent residual lifts to an
element of S outside the first core. This proves P₂=C_T(V)Y₂ and excludes
C_T(V) from Syl₂(P₂).

At the remote node, the residual fixes the marked point and preserves the
moving plane. Two-perfectness kills its action on this plane, since the
point has index two. Restricting the original Sylow to the plane centralizer
then proves C_T(V) belongs to Syl₂(C_T(V)Y₃).

The final theorem uses these actual subgroups to force T-normalization
once the end-node orbit is established. That orbit is still an obligation
of the natural-parabolic construction; no MS classification is used here.

Source: Aschbacher--Smith, 15.1.29, printed pp.1103--1104 of
`refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryLinear.OrderedResidualConjugators
open CFSG.Quasithin.ChapterD.UniqueFactor
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

omit [Finite G] in
private theorem map_centralizer_equiv (e : G ≃* G) (W : Subgroup G) :
    (centralizer (W : Set G)).map e.toMonoidHom =
      centralizer (W.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul,e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- Exchange transports the fixed-plane centralizer index to the moving plane. -/
theorem NineSource.moving_centralizer_index (s : d.NineSource) :
    (centralizer (d.nineMovingPlane : Set G)).relIndex d.S = 2 := by
  obtain ⟨x,hx,hxs⟩ := s.exchange_exists
  have hn := (normal_subgroupOf_iff_le_normalizer d.S_le_T).mp s.sylow_normal
  have he := relIndex_map_map_of_injective (f := (MulAut.conj x).toMonoidHom) (centralizer (d.nineFixedPlane : Set G))
    d.S (MulAut.conj x).injective
  have hS : d.S.map (MulAut.conj x).toMonoidHom = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (hn hx)
  rw [map_centralizer_equiv, (s.exchanges x hx hxs).1,hS] at he
  exact he.trans s.fixed_centralizer_index

/-- The source full-module centralizer has index two in S. -/
theorem NineSource.core_index (s : d.NineSource)
    (hM : CFSG.Quasithin.ChapterA.Section05To06.IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) :
    ((T : Subgroup G) ⊓ centralizer (V : Set G)).relIndex d.S = 2 := by
  rw [← s.sylow_plane_centralizer_eq hM h, inf_comm,
    inf_relIndex_right]
  exact s.moving_centralizer_index

namespace NaturalFlag

/-- The original S is the full preimage of the upper-unitriangular action. -/
theorem mem_sylow_iff (a : NaturalFlag d t) (s : d.ExchangedSource)
    (g : (d.L ⊔ d.S : Subgroup G)) :
    g.val ∈ d.S ↔ a.action g ∈ cutStabilizer a.basis Set.univ := by
  have hSyl := s.centralizer_sylow.restrict (show d.S ≤ d.L ⊔ d.S from le_sup_right)
    (sup_le d.L_component.1 d.S_le_G1)
  obtain ⟨P,hP⟩ := hSyl
  have hk : a.action.ker ≤ d.S.subgroupOf (d.L ⊔ d.S) := by
    intro x hx
    have hx' : x ∈ pCore 2 (d.L ⊔ d.S : Subgroup G) := by
      rwa [show a.action.ker = pCore 2 (d.L ⊔ d.S : Subgroup G) from a.kernel] at hx
    change x.val ∈ d.S
    exact hP.le (mem_map_of_mem (d.L ⊔ d.S).subtype
      (pCore_isPGroup.le_sylow_of_normal P hx'))
  have he := comap_map_eq_self hk
  have hmap : (d.S.subgroupOf (d.L ⊔ d.S)).map a.action =
      cutStabilizer a.basis Set.univ := a.sylow
  rw [hmap] at he
  exact (SetLike.ext_iff.mp he g).symm

/-- An incident root lifts to a Sylow element of Y₂ outside O₂(P₀). -/
theorem second_residual_sylow_escape (a : NaturalFlag d t) (s : d.ExchangedSource) :
    ∃ x ∈ d.S, x ∈ a.parabolics.Y2 ∧ x ∉ a.parabolics.P0.pCoreIn 2 := by
  let i : Fin a.m := ⟨1,by have := a.dimension; omega⟩
  let r : Fin (a.m + 1) := ⟨0,by omega⟩
  let v : Fin (a.m + 1) := ⟨1,by have := a.dimension; omega⟩
  have hrv : r ≠ v := by simp [r,v,Fin.ext_iff]
  let u := root a.basis r v hrv
  have hu : u ∈ nodeResidual a.basis i :=
    incident_root_mem_nodeResidual a.basis i r v hrv
      (Or.inl ⟨by simp [r,i], Or.inl (by rfl)⟩)
  rw [← a.node_residual_image i] at hu
  obtain ⟨g,hg,he⟩ := hu
  have hsg : g.val ∈ d.S := (a.mem_sylow_iff s g).mpr (he ▸
    root_mem_cutStabilizer a.basis Set.univ r v hrv (by intro j _ _; simp [r]))
  refine ⟨g.val,hsg,hg,?_⟩
  intro hcore
  have hc := (a.node_core_mem_iff _ g).mp hcore
  have hfix := ((mem_first_core_iff (by have := a.dimension; omega) a.basis _).mp hc.2).2
  have hv := hfix (a.basis v) ((basis_mem_cutSpace a.basis _ v).mpr (by simp [v]))
  rw [he,root_basis,if_pos rfl] at hv
  apply a.basis.ne_zero r
  apply add_left_cancel (a := a.basis v)
  simpa only [add_zero] using hv

private theorem second_join_of_core (a : NaturalFlag d t) (s : d.NineSource)
    (hM : CFSG.Quasithin.ChapterA.Section05To06.IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V)
    (hc : a.parabolics.P0.pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G)) :
    a.parabolics.P2 = ((T : Subgroup G) ⊓ centralizer (V : Set G)) ⊔ a.parabolics.Y2 := by
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  have hQS : Q ≤ d.S := by
    change (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ d.S
    rw [← s.sylow_plane_centralizer_eq hM h]
    exact inf_le_left
  obtain ⟨x,hx,hxy,hxq⟩ := a.second_residual_sylow_escape s.toExchangedSource
  rw [hc] at hxq
  have hi : (Q.subgroupOf d.S).index = 2 := s.core_index hM h
  have hS : d.S ≤ Q ⊔ a.parabolics.Y2 := by
    intro y hy
    by_cases hyQ : y ∈ Q
    · exact (show Q ≤ Q ⊔ a.parabolics.Y2 from le_sup_left) hyQ
    have hxyQ : y * x ∈ Q := by
      exact ((Q.subgroupOf d.S).mul_mem_iff_of_index_two hi).mpr
        (show (⟨y,hy⟩ : d.S) ∈ Q.subgroupOf d.S ↔ (⟨x,hx⟩ : d.S) ∈ Q.subgroupOf d.S from
          ⟨fun hh => (hyQ hh).elim,fun hh => (hxq hh).elim⟩)
    have hh := (Q ⊔ a.parabolics.Y2).mul_mem ((show Q ≤ Q ⊔ a.parabolics.Y2 from le_sup_left) hxyQ)
      ((Q ⊔ a.parabolics.Y2).inv_mem ((show a.parabolics.Y2 ≤ Q ⊔ a.parabolics.Y2 from le_sup_right) hxy))
    simpa only [mul_inv_cancel_right] using hh
  apply le_antisymm
  · rw [a.second_supplement s.toExchangedSource]
    exact sup_le le_sup_right hS
  · exact sup_le (hQS.trans a.sylow_le.2.1) (map_subtype_le _)

/-- The adjacent parabolic is the join of the original core and its residual. -/
theorem second_join (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : CFSG.Quasithin.ChapterA.Section05To06.IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    a.parabolics.P2 = ((T : Subgroup G) ⊓ centralizer (V : Set G)) ⊔ a.parabolics.Y2 := by
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  exact a.second_join_of_core s hM h (a.first_core hG hM hu h hs ht htS hnat)

/-- The original full-module centralizer is too small to be Sylow in P₂. -/
theorem adjacent_not_sylow (a : NaturalFlag d t) (s : d.NineSource)
    (hM : CFSG.Quasithin.ChapterA.Section05To06.IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) :
    ¬ Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (V : Set G)) a.parabolics.P2 := by
  intro hh
  have hQS : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ d.S := by
    rw [← s.sylow_plane_centralizer_eq hM h]
    exact inf_le_left
  have he := (Chapter1.isSylowIn_iff.mp hh).2.2 d.S
    (T.isPGroup'.to_le d.S_le_T) hQS a.sylow_le.2.1
  have hi := s.core_index hM h
  rw [← he,relIndex_self] at hi
  norm_num at hi

/-- A remote residual fixes the plane containing the marked point. -/
theorem remote_residual_centralizes_plane (a : NaturalFlag d t)
    (W Z : Subgroup G) (hW : W ≤ d.UL t) (hZ : Z ≤ d.UL t)
    (hWcard : Nat.card W = 4) (hZcard : Nat.card Z = 2)
    (hWcut : a.spaceOf W = cutSpace a.basis ⟨1,by have := a.dimension; omega⟩)
    (hZcut : a.spaceOf Z = cutSpace a.basis ⟨0,by have := a.dimension; omega⟩) :
    a.parabolics.Y3 ≤ centralizer (W : Set G) := by
  have hm : 3 ≤ a.m := by have := a.dimension; omega
  have hZW : Z ≤ W := (a.spaceOf_le_iff hZ).mp (by
    rw [hZcut,hWcut]
    exact cutSpace_mono a.basis (by simp))
  have hnW : a.parabolics.P3 ≤ normalizer (W : Set G) :=
    a.node_normalizes_cut W hW _ _ (by intro he; have := congrArg Fin.val he; dsimp at this; omega) hWcut
  have hnZ : a.parabolics.P3 ≤ normalizer (Z : Set G) :=
    a.node_normalizes_cut Z hZ _ _ (by intro he; have := congrArg Fin.val he; dsimp at this; omega) hZcut
  have hcen : a.parabolics.Y3 ≤ centralizer (Z : Set G) :=
    (map_subtype_le _).trans (hnZ.trans (normalizer_le_centralizer_of_card_two Z hZcard))
  let ρ : a.parabolics.Y3 →* MulAut W :=
    W.normalizerMonoidHom.comp (inclusion ((map_subtype_le _).trans hnW))
  have hi : (Z.subgroupOf W).index ≤ 2 := by
    have hh := (Z.subgroupOf W).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv,hZcard,hWcard] at hh
    omega
  have hfix (y : a.parabolics.Y3) : ρ y = 1 :=
    MulAut.eq_one_of_pPerfect_of_fixed_index_le_two ρ
      (isPPerfect_embedded_pResidual 2 a.parabolics.P3)
      (IsPGroup.of_card (n := 2) (by simpa using hWcard)) (Z.subgroupOf W) hi (by
        intro y w hw
        apply Subtype.ext
        change y.val * w.val * y.val⁻¹ = w.val
        have hh : w.val * y.val = y.val * w.val := hcen y.property w.val hw
        rw [← hh,mul_inv_cancel_right]) y
  intro y hy w hw
  have he := congrArg (fun f : MulAut W => (f ⟨w,hw⟩ : G)) (hfix ⟨y,hy⟩)
  change y * w * y⁻¹ = w at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end NaturalFlag
private theorem sylow_in_centralizer {S H W : Subgroup G}
    (hs : Chapter1.IsSylowIn 2 S H) (hWH : W ≤ H)
    (hn : S ≤ normalizer (W : Set G)) :
    Chapter1.IsSylowIn 2 (S ⊓ centralizer (W : Set G))
      (H ⊓ centralizer (W : Set G)) := by
  have hSH := (Chapter1.isSylowIn_iff.mp hs).2.1
  obtain ⟨P,hP⟩ := hs
  let C : Subgroup H := centralizer (W.subgroupOf H : Set H)
  have hC : C.map H.subtype = H ⊓ centralizer (W : Set G) := by
    ext x
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨x.property,?_⟩
      intro w hw
      exact congrArg Subtype.val (hx ⟨w,hWH hw⟩ hw)
    · rintro ⟨hxH,hxC⟩
      refine ⟨⟨x,hxH⟩,?_,rfl⟩
      intro w hw
      exact Subtype.ext (hxC w.val hw)
  have hnP : (P : Subgroup H) ≤ normalizer (W.subgroupOf H : Set H) := by
    apply le_normalizer_iff.mpr
    intro p hp w hw
    change p.val * w.val * p.val⁻¹ ∈ W
    have hpS : p.val ∈ S := hP ▸ mem_map_of_mem H.subtype hp
    exact (mem_normalizer_iff.mp (hn hpS) w.val).mp hw
  obtain ⟨Q,hQ⟩ := P.exists_centralizer_sylow_of_normalizes (W.subgroupOf H) hnP
  have hh : Chapter1.IsSylowIn 2 ((P : Subgroup H) ⊓ C) C := ⟨Q,hQ⟩
  have hm := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hh
  rw [map_inf _ _ H.subtype H.subtype_injective,hP,hC,← inf_assoc,
    inf_eq_left.mpr hSH] at hm
  exact hm

namespace NaturalFlag

/-- The same source centralizer is Sylow in its join with the remote residual. -/
theorem remote_sylow (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : CFSG.Quasithin.ChapterA.Section05To06.IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (V : Set G))
      (((T : Subgroup G) ⊓ centralizer (V : Set G)) ⊔ a.parabolics.Y3) := by
  let := h.elementary
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  obtain ⟨n,hn,⟨e⟩⟩ := hs.2.2
  let hf := facts_of_small_binary_model (small_binary_model_of_marking hn e)
  have hW := d.nineMovingPlane_le_UL s hG h hf t ht htS
  have hcut := a.movingPlane_cut hG hM hu h hs ht htS hnat
  obtain ⟨Z,hZ,hZcard,_,_,hZcut⟩ := a.exists_markedLine hnat
  have hY := a.remote_residual_centralizes_plane d.nineMovingPlane Z hW hZ
    s.moving_card hZcard hcut hZcut
  have hWV : d.nineMovingPlane ≤ V := le_sup_right.trans_eq s.planes_sup
  have hWG : d.nineMovingPlane ≤ d.G1 :=
    hWV.trans (V.le_centralizer.trans (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))
  have hSyl := sylow_in_centralizer s.centralizer_sylow hWG s.fixes_planes.2
  rw [s.sylow_plane_centralizer_eq hM h] at hSyl
  apply hSyl.restrict le_sup_left
  apply sup_le
  · rw [← s.sylow_plane_centralizer_eq hM h]
    exact inf_le_inf_right _ d.S_le_G1
  · exact le_inf ((map_subtype_le _).trans (a.parabolics_le.2.2.trans
      (sup_le d.L_component.1 d.S_le_G1))) hY

end NaturalFlag

namespace NaturalFlag

/-- Once the original residual orbit is supplied, the proved Sylow distinction
forces T to normalize the actual second residual and its two-core. The orbit
is the remaining source obligation of this same construction owner. -/
theorem normalizes_second_of_end_orbit (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : CFSG.Quasithin.ChapterA.Section05To06.IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t)
    (horbit : ∀ x ∈ (T : Subgroup G),
      a.parabolics.Y2.map (MulAut.conj x).toMonoidHom = a.parabolics.Y2 ∨
        a.parabolics.Y2.map (MulAut.conj x).toMonoidHom = a.parabolics.Y3) :
    (T : Subgroup G) ≤ normalizer (a.parabolics.Y2 : Set G) ∧
      (T : Subgroup G) ≤ normalizer (a.parabolics.Q2 : Set G) := by
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  have hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      ((hM.1.2.trans h.normalized).trans (normalizer_le_normalizer_centralizer V))).trans
      inf_normalizer_le_normalizer_inf
  have hTY : (T : Subgroup G) ≤ normalizer (a.parabolics.Y2 : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rcases horbit x hx with he | he
    · exact he
    · exfalso
      have hQ : Q.map (MulAut.conj x).toMonoidHom = Q :=
        mem_normalizer_iff_map_conj_eq.mp (hTQ hx)
      have hjoin : a.parabolics.P2.map (MulAut.conj x).toMonoidHom = Q ⊔ a.parabolics.Y3 := by
        rw [a.second_join hG hM hu h hs ht htS hnat,Subgroup.map_sup,hQ,he]
      apply a.adjacent_not_sylow s hM h
      apply (Chapter1.IsSylowIn.map_iff (MulAut.conj x).toMonoidHom
        (MulAut.conj x).injective).mp
      rw [hQ,hjoin]
      exact a.remote_sylow hG hM hu h hs ht htS hnat
  refine ⟨hTY,?_⟩
  have hTS : (T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer d.S_le_T).mp s.sylow_normal
  have hTP : (T : Subgroup G) ≤ normalizer (a.parabolics.P2 : Set G) := by
    rw [a.second_supplement hs.1]
    exact (le_inf hTY hTS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact hTP.trans (normalizer_le_normalizer_characteristic_image a.parabolics.P2
    (pCore 2 a.parabolics.P2))

end NaturalFlag

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

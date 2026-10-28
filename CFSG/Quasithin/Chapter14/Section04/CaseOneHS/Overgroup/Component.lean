module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.PointResidual
public import Theory.GroupTheory.CComponent.SolvableImageNormality
public import Theory.GroupTheory.PResidual.PerfectImage
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.SpecificGroups.AlternatingFiveInvolutionCover
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# The original HS component core and its Sylow subgroup

The C-component supplied by 14.3.32 maps onto the actual A₅ in H/O₂(H).
Solvable-kernel component correspondence makes it normal, and H=KT
identifies it with O²(H). The original point residual, hence P, lies in K.

Since [P,L₁]=P and |P∩U|=16<64, some element of P escapes O₂(K).
Its square belongs to V≤U, so it gives an involution of K/U with nontrivial
A₅ image. The proved central-cover criterion excludes SL₂(5) and yields
U=O₂(K). Finally |PU|=256 and |K|=3840 give the literal Sylow subgroup.
This proves 14.3.33(2) conditional only on the earlier local structure and
same-ambient structural predecessors; the terminal transfer remains separate.

Source: Aschbacher--Smith, 14.3.33(2), printed p.1004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem alternating_quasisimple : IsQuasisimple (alternatingGroup (Fin 5)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

/-- The original component is normal in H, equals O²(H), and maps onto the
actual alternating subgroup in every marking of H/O₂(H) as S₅. -/
theorem component_residual
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (K : Subgroup G) (hKH : K ≤ F.H) (hK : (K.subgroupOf F.H).IsCComponent)
    (hKT : F.H = K ⊔ (T : Subgroup G)) :
    (K.subgroupOf F.H).Normal ∧
      (pResidual 2 F.H).map F.H.subtype = K ∧
      ∃ f : K →* alternatingGroup (Fin 5), Function.Surjective f ∧ f.ker = pCore 2 K := by
  obtain ⟨e⟩ := s.quotient F
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 F.H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let : Group.IsNilpotent q.ker := (hk ▸ pCore_isPGroup).isNilpotent
  have him := cComponent_map_of_solvable_ker hK q hq
  let := him.perfect
  let := alternating_quasisimple
  have hA : (alternatingGroup (Fin 5)).IsCComponent :=
    (show IsComponent (Equiv.Perm (Fin 5)) (alternatingGroup (Fin 5)) from
      ⟨(inferInstance : (alternatingGroup (Fin 5)).Normal).isSubnormal, inferInstance⟩).isCComponent
  have he : (K.subgroupOf F.H).map q = alternatingGroup (Fin 5) :=
    him.eq_of_le hA (le_of_isPerfect_of_index_eq_two _ _ alternatingGroup.index_eq_two)
  have hn := cComponent_normal_of_solvable_image_normal hK q hq (he ▸ inferInstance)
  let := hn
  let := hK.perfect
  have hperf : IsPPerfect 2 (K.subgroupOf F.H) :=
    (pResidual_eq_top_iff 2 _).mp (pResidual_eq_top_of_isPerfect 2)
  have hs : K.subgroupOf F.H ⊔ (T : Subgroup G).subgroupOf F.H = ⊤ := by
    apply (map_injective F.H.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKH,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1), ← hKT, ← MonoidHom.range_eq_map, range_subtype]
  have hr : pResidual 2 F.H = K.subgroupOf F.H :=
    pResidual_eq_of_isPPerfect_sup _ _ hperf T.isPGroup'.comap_subtype hs
  refine ⟨hn, by rw [hr, map_subgroupOf_eq_of_le hKH], ?_⟩
  let eK : K.subgroupOf F.H ≃* K := subgroupOfEquivOfLe hKH
  let f0 : K.subgroupOf F.H →* alternatingGroup (Fin 5) :=
    (MulEquiv.subgroupCongr he).toMonoidHom.comp (q.subgroupMap (K.subgroupOf F.H))
  have hf0 : Function.Surjective f0 :=
    (MulEquiv.subgroupCongr he).surjective.comp (q.subgroupMap_surjective _)
  have hk0 : f0.ker = pCore 2 (K.subgroupOf F.H) := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr he).injective,
      ker_subgroupMap, hk]
    exact (pCore_subnormal_eq_comap 2 hK.subnormal).symm
  let f := f0.comp eK.symm.toMonoidHom
  refine ⟨f, hf0.comp eK.symm.surjective, ?_⟩
  have hmap : f.ker.map eK.symm.toMonoidHom = f0.ker := by
    change (f0.ker.comap eK.symm.toMonoidHom).map eK.symm.toMonoidHom = f0.ker
    exact map_comap_eq_self_of_surjective eK.symm.surjective _
  apply (map_injective (f := eK.symm.toMonoidHom) eK.symm.injective)
  rw [hmap, hk0, pCore_map_iso]

/-- The actual L₁ and hence P lie in the original component K. -/
theorem point_residual_le_component
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (K : Subgroup G) (hKH : K ≤ F.H) (hK : (K.subgroupOf F.H).IsCComponent)
    (hKT : F.H = K ⊔ (T : Subgroup G)) : F.Li L 1 ≤ K := by
  have hr := (component_residual F s K hKH hK hKT).2.1
  have hlh : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hp : IsPPerfect 2 (F.Li L 1) := by
    change IsPPerfect 2 ((pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype)
    exact isPPerfect_embedded_pResidual 2 _
  have hp' : IsPPerfect 2 ((F.Li L 1).subgroupOf F.H) := hp.of_surjective
    (subgroupOfEquivOfLe hlh).symm.toMonoidHom (subgroupOfEquivOfLe hlh).symm.surjective
  have hh := map_mono (f := F.H.subtype) (le_pResidual_of_isPPerfect _ hp')
  rwa [map_subgroupOf_eq_of_le hlh, hr] at hh

/-- PU is contained in the actual selected component. -/
theorem core_closure_le_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (K : Subgroup G) (hKH : K ≤ F.H) (hK : (K.subgroupOf F.H).IsCComponent)
    (hKT : F.H = K ⊔ (T : Subgroup G)) (hU : F.U = ⁅K.pCoreIn 2, K⁆) :
    L.pCoreIn 2 ⊔ F.U ≤ K := by
  refine sup_le ((core_le_point_residual h structural alternatives F s hne).trans
    (point_residual_le_component F s K hKH hK hKT)) ?_
  rw [hU]
  exact (commutator_mono (pCoreIn_le 2 K) le_rfl).trans (commutator_le_self K)

/-- Original 14.3.33(2), the component-core equality. Squaring in P supplies
an involution with nontrivial A₅ image in K/U; hence the central two-cover
K/U→A₅ has trivial kernel. -/
theorem component_core_eq_closure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (K : Subgroup G) (hKH : K ≤ F.H) (hK : (K.subgroupOf F.H).IsCComponent)
    (hKT : F.H = K ⊔ (T : Subgroup G)) (hU : F.U = ⁅K.pCoreIn 2, K⁆) :
    F.U = K.pCoreIn 2 := by
  let := h.chosen.elementary
  have hPU := core_closure_le_component h structural alternatives F s hne K hKH hK hKT hU
  have hUK : F.U ≤ K := le_sup_right.trans hPU
  have hLP := point_residual_le_component F s K hKH hK hKT
  have hUP : F.U ≤ K.pCoreIn 2 := by
    rw [hU]
    exact le_normalizer_iff_commutator_le_left.mp
      (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hnot : ¬ L.pCoreIn 2 ≤ F.U := by
    intro hp
    have hc := centerSpan_inf_closure_card h structural alternatives F s hne
    rw [centerSpan_eq_core h structural alternatives F s hne, inf_eq_left.mpr hp] at hc
    have hc' := (centerSpan_square_kernel_and_card h structural alternatives F s hne).2
    rw [centerSpan_eq_core h structural alternatives F s hne] at hc'
    omega
  have hncore : ¬ L.pCoreIn 2 ≤ K.pCoreIn 2 := by
    intro hp
    apply hnot
    rw [core_eq_point_commutator h structural alternatives F s hne, hU]
    exact commutator_mono hp hLP
  obtain ⟨a, haP, haN⟩ := SetLike.not_le_iff_exists.mp hncore
  let aK : K := ⟨a, hPU (mem_sup_left haP)⟩
  let W := F.U.subgroupOf K
  let : W.Normal := normal_subgroupOf_of_le_normalizer (hKH.trans (le_normalizer_conjugateSpanBy V F.H))
  let := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  obtain ⟨f, hf, hfk⟩ := (component_residual F s K hKH hK hKT).2.2
  have hW : W ≤ f.ker := by
    rw [hfk]
    intro x hx
    obtain ⟨y, hy, he⟩ := hUP hx
    exact (Subtype.ext he : y = x) ▸ hy
  let r := QuotientGroup.mk' W
  let fbar : K ⧸ W →* alternatingGroup (Fin 5) := QuotientGroup.lift W f hW
  have hfb : Function.Surjective fbar := by
    intro b
    obtain ⟨x, rfl⟩ := hf b
    exact ⟨r x, rfl⟩
  have hkbar : fbar.ker = f.ker.map r := QuotientGroup.ker_lift W f hW
  have hc : fbar.ker ≤ center (K ⧸ W) := by
    rw [hkbar]
    rintro _ ⟨x, hx, rfl⟩
    apply mem_center_iff.mpr
    intro b
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective W b
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    change (⁅y, x⁆ : K).val ∈ F.U
    rw [hU, commutator_comm]
    exact commutator_mem_commutator y.property
      (mem_map_of_mem K.subtype (hfk ▸ hx))
  have hp : IsPGroup 2 fbar.ker := by
    rw [hkbar, hfk]
    exact pCore_isPGroup.map r
  have ha2 : r aK ^ 2 = 1 := by
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (le_conjugateSpanBy V F.H) (centerSpan_square_mem_seed h structural F s
      ((centerSpan_eq_core h structural alternatives F s hne).symm ▸ haP))
  have haneq : fbar (r aK) ≠ 1 := by
    intro he
    have hm : aK ∈ f.ker := he
    rw [hfk] at hm
    exact haN (mem_map_of_mem K.subtype hm)
  have hinj := alternatingGroup.injective_of_central_two_kernel_of_involution
    fbar hfb hc hp (r aK) ha2 haneq
  apply le_antisymm hUP
  rintro x ⟨y, hy, rfl⟩
  have hm : fbar (r y) = 1 := show y ∈ f.ker from hfk.symm ▸ hy
  have he : r y = 1 := hinj (hm.trans fbar.map_one.symm)
  exact show y ∈ W from (QuotientGroup.eq_one_iff y).mp he

/-- The literal PU is a Sylow two-subgroup of the original component K. -/
theorem core_closure_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (K : Subgroup G) (hKH : K ≤ F.H) (hK : (K.subgroupOf F.H).IsCComponent)
    (hKT : F.H = K ⊔ (T : Subgroup G)) (hU : F.U = ⁅K.pCoreIn 2, K⁆) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype = L.pCoreIn 2 ⊔ F.U := by
  have hPU := core_closure_le_component h structural alternatives F s hne K hKH hK hKT hU
  have hcore := component_core_eq_closure h structural alternatives F s hne K hKH hK hKT hU
  obtain ⟨f, hf, hfk⟩ := (component_residual F s K hKH hK hKT).2.2
  have hcardCore : Nat.card (pCore 2 K) = 64 := by
    rw [← card_map_of_injective K.subtype_injective]
    change Nat.card (K.pCoreIn 2) = 64
    rw [← hcore]
    exact s.core_shape.card
  have hcardK : Nat.card K = 3840 := by
    have hc := f.ker.card_mul_index
    rw [index_ker, MonoidHom.range_eq_top.mpr hf, card_top, hfk, hcardCore] at hc
    have ha : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      norm_num
    rw [ha] at hc
    omega
  let R := (L.pCoreIn 2 ⊔ F.U).subgroupOf K
  have hR : Nat.card R = 256 :=
    (Nat.card_congr (subgroupOfEquivOfLe hPU).toEquiv).trans
      (core_closure_card h structural alternatives F s hne)
  have hi : R.index = 15 := by
    have hc := R.card_mul_index
    rw [hR, hcardK] at hc
    omega
  let S := (IsPGroup.of_card (p := 2) (n := 8) hR).toSylow (by rw [hi]; decide)
  exact ⟨S, map_subgroupOf_eq_of_le hPU⟩

/-- The selected local component satisfies all clauses of original
14.3.33(2), together with its residual identification inside H. -/
theorem exists_component_core_and_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
      F.H = K ⊔ (T : Subgroup G) ∧ (pResidual 2 F.H).map F.H.subtype = K ∧
      F.U = K.pCoreIn 2 ∧
      ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype = L.pCoreIn 2 ⊔ F.U := by
  obtain ⟨K, hKH, hK, hKT, hU, _⟩ := s.component
  exact ⟨K, hKH, hK, hKT, (component_residual F s K hKH hK hKT).2.1,
    component_core_eq_closure h structural alternatives F s hne K hKH hK hKT hU,
    core_closure_sylow h structural alternatives F s hne K hKH hK hKT hU⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup

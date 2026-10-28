module
public import Theory.GroupTheory.PushingUp.BaumannBinary.NaturalAll
public import Glauberman.MaximumAbelianKernelIntersection
public import Glauberman.PushingUpOmegaSplitting
public import Theory.GroupTheory.RankOneInvariantKernelQuotient
public import Theory.GroupTheory.ReducedNormal.MovedCentralizer
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal

/-!
# A residual-centralized kernel at every nontrivial binary field degree

The natural quotient of the original Sylow-center closure has full fixed
index q² on any supplement of the two-core. Sharp maximum-abelian replacement
selects a supplement with the same intersection with the core and the maximal
automorphism-invariant normal kernel. The enlarged central omega layer then
splits over the original closure by fixed points. Its moved centralizer
identifies the invariant kernel with the cyclic intersection of core images.
Intersecting over all Sylow automorphisms forces one kernel to omit the
original closure; Niles's centralizer argument makes the two-residual
centralize that kernel.

This extends the reduction argument of Niles, *Pushing-up in finite groups*
(1979), Lemmas 7.3–7.6 and Theorem 7.2, pp.60–62, to the actual marked
SL₂(2ⁿ) quotient for n>1. The module uses the already proved original V,
not a substituted Frattini module. `Commutator` applies the result to the
full commutator assertion in DGS85 (6.3), printed p.120.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open NilesRankOneKernel
open scoped MatrixGroups IsMulCommutative
namespace Theory.GroupTheory.BaumannBinary
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
local instance residualKernelAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

omit [Finite G] in
private theorem commutator_supplement (V Q L : Subgroup G) [V.Normal]
    (hVQ : V ≤ centralizer (Q : Set G)) (hgen : L ⊔ Q = ⊤) :
    ⁅V,L⁆ = ⁅V,(⊤ : Subgroup G)⁆ := by
  have hn : (⁅V,L⁆ : Subgroup G).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←hgen]
    exact sup_le (normalizer_commutator_ge_right V L)
      (((le_centralizer_iff.mp hVQ).trans (centralizer_le (commutator_le_left V L))).trans
        (Subgroup.centralizer_le_normalizer _))
  let _ := hn
  apply le_antisymm (commutator_mono le_rfl le_top)
  rw [commutator_comm]
  have hh := commutator_sup_le_of_relative_normal (⊤ : Subgroup G) L Q V ⁅V,L⁆
    le_normalizer_of_normal le_top le_top (by rw [commutator_comm])
    ((commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hVQ)).le.trans bot_le)
  rwa [hgen] at hh

/-- A supplement acts with the same full fixed index and moved centralizer. -/
theorem centerClosure_supplement_action (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (L : Subgroup G) (hgen : L ⊔ pCore 2 G = ⊤) :
    (centralizer (L : Set G)).relIndex (centerClosure (P : Subgroup G)) = Nat.card F ^ 2 ∧
    centralizer ((⁅centerClosure (P : Subgroup G),L⁆ : Subgroup G) : Set G) = pCore 2 G := by
  let V := centerClosure (P : Subgroup G)
  have hred := centerClosure_reduced P hc
  let _ := hred.elementary
  have hC := centerClosure_centralizer P hc hP q hq hk hn hF
  have hker := hk.trans hC.symm
  let ρ := NormalElementaryQuotient.representation V q hq hker
  have hL : L.map q = ⊤ := by
    have hQmap : (pCore 2 G).map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hk.ge
    have hmap := congrArg (Subgroup.map q) hgen
    rw [Subgroup.map_sup,hQmap,sup_bot_eq,
      map_top_of_surjective q hq] at hmap
    exact hmap
  constructor
  · rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim V q hq hker,hL]
    obtain ⟨E,_⟩ := centerClosure_natural_quotient_all P hc hP q hq hk hn hF
    change 2 ^ Module.finrank (ZMod 2) (Additive V ⧸ fixedSpace ρ ⊤) = _
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive V ⧸ fixedSpace ρ ⊤)
    rw [Nat.card_zmod] at hcard
    rw [←hcard,Nat.card_congr E.toEquiv,Nat.card_fun,Nat.card_fin]
  · rw [commutator_supplement V (pCore 2 G) L hred.le_centralizer_pCore hgen]
    exact (hred.centralizer_commutator_eq V q hq hker ⊤ (by
      rw [map_top_of_surjective q hq]; exact le_top)).trans hC

private theorem sylow_ne_bot (P : Sylow 2 G)
    (q : G →* SL(2,F)) (hq : Function.Surjective q) : (P : Subgroup G) ≠ ⊥ := by
  intro hb
  have hT : ((P.mapSurjective hq : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) = ⊥ := by
    change (P : Subgroup G).map q = ⊥
    rw [hb,Subgroup.map_bot]
  exact Matrix.SpecialLinearGroup.no_normal_sylow F 2 (P.mapSurjective hq)
    (by rw [hT]; infer_instance)

/-- The original all-degree action discharges Niles's cyclic-kernel formula. -/
theorem centerClosure_kernel_orbit (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (α : MulAut P)
    (hVN : centerClosure (P : Subgroup G) ≤
      (invariantNormalKernel (P : Subgroup G) α).map (P : Subgroup G).subtype) :
    invariantNormalKernel (P : Subgroup G) α =
      ⨅ k : ℤ, ((pCore 2 G).subgroupOf (P : Subgroup G)).map ((α ^ k).toMonoidHom) := by
  let Q := pCore 2 G
  let V := centerClosure (P : Subgroup G)
  let N := invariantNormalKernel (P : Subgroup G) α
  let Z := N.map (P : Subgroup G).subtype
  have hred := centerClosure_reduced P hc
  let _ := hred.elementary
  have hVQ : V ≤ Q := hred.le_pCore
  have hVc : V ≤ centralizer (Q : Set G) := hred.le_centralizer_pCore
  have hQS : Q ≤ (P : Subgroup G) := pCore_isPGroup.le_sylow_of_normal P
  have hNS : Z ≤ (P : Subgroup G) := map_subtype_le _
  have hNQ : Z ≤ Q := le_sSup ⟨inferInstance,P.isPGroup'.to_le hNS⟩
  have hC := centerClosure_centralizer P hc hP q hq hk (by omega) hF
  have hlower (A : Subgroup G) (hA : A ∈ thompsonAbelianSubgroups (P : Subgroup G))
      (hout : ¬ A ≤ Q) : Q.relIndex (P : Subgroup G) ≤
        (V ⊓ centralizer (A : Set G)).relIndex V := by
    rw [inf_relIndex_left,Matrix.SpecialLinearGroup.sylow_core_relIndex q hq hk P]
    exact Representation.SL2.normal_two_subgroup_fixed_index_lower V q hq
      (hk.trans hC.symm) hn hF A (P.isPGroup'.to_le hA.1) (hk.symm ▸ hout)
  have hex : ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups (P : Subgroup G) ∧ ¬ A ≤ Q := by
    by_contra! hh
    exact Glauberman.allAbelianThompson_not_le_normal (P : Subgroup G) Q hQS
      (sylow_ne_bot P q hq) hP (sSup_le hh)
  obtain ⟨A₀,hA₀,hout₀⟩ := hex
  have hfamily := (Glauberman.maximum_abelian_replacement_of_fixedIndex hA₀ hQS hVQ
    inferInstance hVc le_normalizer_of_normal (hlower A₀ hA₀ hout₀)).2.2.2.2.2
  obtain ⟨A,hA,hout,hinter⟩ := Glauberman.exists_maximum_abelian_kernel_intersection
    (P : Subgroup G) α Q V hQS hfamily ⟨A₀,hA₀,hout₀⟩ (by
      intro B hB houtB
      refine ⟨(Glauberman.maximum_abelian_saturation hB hQS hVQ inferInstance hVc
        (hlower B hB houtB)).2.2.2.1,?_⟩
      intro hvb
      exact houtB ((le_centralizer_iff.mp (hvb.trans (show B ≤ centralizer (B : Set G) from
        @Subgroup.le_centralizer _ _ B hB.2.1))).trans hC.le)) hNQ hVN
  have hsupp := Glauberman.maximum_abelian_supplements_normal hA hQS hVQ inferInstance
    hVc le_normalizer_of_normal (hlower A hA hout)
  obtain ⟨g,_,hgenP,_⟩ := Matrix.SpecialLinearGroup.exists_residual_generating_sylow_pair q hq hk P
  have hgen : (A ⊔ A.map (MulAut.conj g).toMonoidHom) ⊔ Q = ⊤ := by
    have hQg : Q.map (MulAut.conj g).toMonoidHom = Q := Normal.map_conj_eq Q g
    rw [←hsupp,Subgroup.map_sup,hQg] at hgenP
    simpa only [sup_assoc,sup_left_comm,sup_comm,sup_idem,sup_left_idem] using hgenP
  let L := A ⊔ A.map (MulAut.conj g).toMonoidHom
  have hidx : Q.relIndex A ≤ Nat.card F :=
    (relIndex_le_of_le_right hA.1 index_ne_zero_of_finite).trans_eq
      (Matrix.SpecialLinearGroup.sylow_core_relIndex q hq hk P)
  have hVW : V ≤ omegaCenterIn Z := by
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨hVN hx,centralizer_le hNQ (hVc hx),
      elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx⟩
  let _ : (omegaCenterIn Z).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←Z.normalizer_eq_top]
    exact normalizer_le_normalizer_omegaCenterIn Z
  obtain ⟨hi,hcommC⟩ := centerClosure_supplement_action P hc hP q hq hk (by omega) hF L hgen
  have hsplit : omegaCenterIn Z = V ⊔ (omegaCenterIn Z ⊓ centralizer (L : Set G)) :=
    Glauberman.abelian_eq_sup_fixed_of_conjugate_bounds V (omegaCenterIn Z) A g
      (Nat.card F) hVW inferInstance
      (Glauberman.maximum_abelian_omega_fixed_bound (P : Subgroup G) Q Z A hA hNS hinter
        (Nat.card F) hidx) (by simpa only [pow_two] using hi.ge)
  have hcomm : ⁅omegaCenterIn Z,L⁆ = ⁅V,L⁆ :=
    Glauberman.commutator_eq_of_abelian_fixed_splitting V _ L inferInstance
      le_normalizer_of_normal hsplit
  have hSL : (P : Subgroup G) ⊔ L = ⊤ := by
    apply top_unique
    rw [←hgen]
    exact sup_le le_sup_right (hQS.trans le_sup_left)
  let _ : ((Q.subgroupOf (P : Subgroup G)).map (P : Subgroup G).subtype).Normal := by
    rw [map_subgroupOf_eq_of_le hQS]
    infer_instance
  apply invariantKernel_eq_orbit_inf_of_omega_commutator (P : Subgroup G) α
    (Q.subgroupOf (P : Subgroup G)) L hSL
  apply map_injective (P : Subgroup G).subtype_injective
  rw [centralizer_map_subtype,map_subgroupOf_eq_of_le hQS]
  have hm : ⁅(omegaCenterIn N).map (P : Subgroup G).subtype,L⁆ ≤ (P : Subgroup G) := by
    rw [omegaCenterIn_map_injective _ (P : Subgroup G).subtype_injective]
    exact (commutator_le_left _ _).trans
      ((show omegaCenterIn Z ≤ Z from fun _ hx => ((mem_omegaCenterIn_iff Z _).mp hx).1).trans hNS)
  rw [map_subgroupOf_eq_of_le hm,omegaCenterIn_map_injective _
    (P : Subgroup G).subtype_injective,hcomm,hcommC,inf_eq_right.mpr hQS]


/-- An actual invariant kernel centralized by the two-residual, at every
binary degree greater than one. -/
theorem exists_residual_central_kernel (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    ∃ α : MulAut P, pResidual 2 G ≤ centralizer
      ((invariantNormalKernel (P : Subgroup G) α).map (P : Subgroup G).subtype : Set G) := by
  let Q := pCore 2 G
  let V := centerClosure (P : Subgroup G)
  have hred := centerClosure_reduced P hc
  have hQS : Q ≤ (P : Subgroup G) := pCore_isPGroup.le_sylow_of_normal P
  have hVS : V ≤ (P : Subgroup G) := hred.le_pCore.trans hQS
  let e : (G ⧸ Q) ≃* SL(2,F) := QuotientGroup.liftEquiv Q hq hk.symm
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ n by omega)
  let _ : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let _ : IsSimpleGroup SL(2,F) := (Theory.PSL2.sl2QuotientEquiv F).isSimpleGroup
  let _ : IsSimpleGroup (G ⧸ Q) := e.isSimpleGroup
  have hK : ¬ IsPGroup 2 (G ⧸ Q) := by
    intro hp
    have hp' : IsPGroup 2 SL(2,F) := hp.of_equiv e
    have ht : (⊤ : Subgroup SL(2,F)) ≤ pCore 2 SL(2,F) :=
      le_sSup ⟨inferInstance,hp'.to_subgroup ⊤⟩
    rw [Matrix.SL2.twoCore_eq_bot F] at ht
    exact top_ne_bot (le_antisymm ht bot_le)
  have hu : Order.HasUniqueMaximalOver (P : Subgroup G) ⊤ :=
    hasUniqueMaximalOver_of_surjective q hq (hk ▸ hQS)
      (Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver 2 (P.mapSurjective hq))
  have hne : V.subgroupOf (P : Subgroup G) ≠ ⊥ := by
    intro hb
    have hh := congrArg (Subgroup.map (P : Subgroup G).subtype) hb
    rw [map_subgroupOf_eq_of_le hVS,Subgroup.map_bot] at hh
    exact centerClosure_not_le_center P hP (sylow_ne_bot P q hq) (by change V ≤ _; rw [hh]; exact bot_le)
  obtain ⟨α,hα⟩ := exists_not_le_invariantNormalKernel (P : Subgroup G) hP
    (Q.subgroupOf (P : Subgroup G)) (V.subgroupOf (P : Subgroup G)) hne (by
      intro α hVN
      apply centerClosure_kernel_orbit P hc hP q hq hk hn hF α
      change V ≤ _
      rw [←map_subgroupOf_eq_of_le hVS]
      exact map_mono hVN)
  refine ⟨α,MinimalParabolicKernel.residual_centralizes_normal_sylow_kernel P hu Q hK
    ((invariantNormalKernel (P : Subgroup G) α).map (P : Subgroup G).subtype) V
    (map_subtype_le _) hred.le_pCore hred.le_centralizer_pCore ?_
    (sylow_inf_centralizer_le_kernel_of_le_twoCore P α)⟩
  intro hl
  apply hα
  intro v hv
  obtain ⟨w,hw,he⟩ := hl hv
  exact (Subtype.ext he : w = v) ▸ hw

end Theory.GroupTheory.BaumannBinary

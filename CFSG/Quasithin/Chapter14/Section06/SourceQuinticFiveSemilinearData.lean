module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveResidualStructure
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveSymmetry
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveRootAction
public import Theory.SpecificGroups.ReeTwo.SemilinearExtensionFrame
public import Theory.GroupAction.Order512FiveOrbit
public import Theory.SpecificGroups.ReeTwo.CoreFaithfulness

/-!
# Intrinsic semilinear data for the original large quintic core

The native residual structure, fixed cyclic root and squaring symmetry supply
all structural and action fields of the Ree extension interface. The remaining
inputs are the ambient residual centralizer equality and an involution outside
the original derived layer. The root action is proved from that centralizer
equality. The involution's actual five-orbit generates
the residual by Parrott's orbit theorem. No coordinate or model identification
is assumed by this bridge.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem map_relative_centralizer
    {K L : Type*} [Group K] [Group L] (U V : Subgroup K) (f : K →* L)
    (hf : Function.Injective f) :
    (U ⊓ centralizer (V : Set K)).map f =
      U.map f ⊓ centralizer (V.map f : Set L) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨mem_map_of_mem f hx.1,mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨v,hv,rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hx.2 v hv)
  · rintro _ ⟨⟨x,hx,rfl⟩,hc⟩
    refine mem_map_of_mem f ⟨hx,mem_centralizer_iff.mpr ?_⟩
    intro v hv
    apply hf
    simpa only [map_mul] using mem_centralizer_iff.mp hc (f v) (mem_map_of_mem f hv)

/-- Assemble native semilinear data from the exact original large branch.
The remaining geometric inputs are the ambient residual centralizer equality
and an involution seed. Root action and orbit generation are constructed. -/
theorem source_quintic_large_five_semilinear_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5)
    (hcentral : H.pCoreIn 2 ⊓ centralizer ((⁅H.pCoreIn 2,A⁆ : Subgroup G) : Set G) = centralInvolutions T)
    (hseed : ∃ b ∈ ⁅H.pCoreIn 2,A⁆, b ^ 2 = 1 ∧
      b ∉ conjugateSpanBy (localModule T M) H) :
    let Q := H.pCoreIn 2
    let R := (⁅Q,A⁆).subgroupOf Q
    ∃ (t z : Q) (b : R) (ρ : A →* MulAut Q) (σ : MulAut Q),
      (∀ a q, (ρ a q : G) = (a : G) * (q : G) * (a : G)⁻¹) ∧
      zpowers (t : G) = Q ⊓ centralizer (A : Set G) ∧
      zpowers (z : G) = centralInvolutions T ∧
      ReeTwo.SemilinearExtensionData ρ R t z b σ := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let P := ⁅Q,A⁆
  let R := P.subgroupOf Q
  let C := H ⊓ centralizer (U : Set G)
  let ZG := centralInvolutions T
  have hAQ : A ≤ normalizer (Q : Set G) := hAH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hPQ : P ≤ Q := le_normalizer_iff_commutator_le_left.mp hAQ
  let eR : R ≃* P := subgroupOfEquivOfLe hPQ
  obtain ⟨_,_,t,htB,htP,ht4,htgen,hzgen,htsup,htU⟩ :=
    source_quintic_large_five_fixed_root hG T hempty hM hu hmany hcard e H hH hi
      hlarge A hAH hA
  obtain ⟨htcentral,htcomm⟩ := source_quintic_large_five_root_action
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA hcentral t htB htP
  let tQ : Q := ⟨t,htB.1⟩
  let z : Q := tQ ^ 2
  obtain ⟨b,hbP,hb2,hbU⟩ := hseed
  let bP : P := ⟨b,hbP⟩
  let bR : R := eR.symm bP
  obtain ⟨ρ,σ,hρ,hσsq,hρR,hσR,hroots⟩ :=
    source_quintic_five_squaring_automorphism hG T hempty hM hu hmany hcard e H hH hi A hAH hA
  obtain ⟨hρt,hσt⟩ := hroots tQ ht4 htgen
  obtain ⟨_,_,hPcard,hPclass,_,hPderived,_,_,hPcenter,_⟩ :=
    source_quintic_large_five_residual_structure hG T hempty hM hu hmany hcard e H hH hi
      hlarge A hAH hA
  obtain ⟨_,_,_,_,_,hUP,_,hPC⟩ := source_quintic_large_five_residual
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  have hUQ : U ≤ Q := hUP.trans hPQ
  have hHZ : H ≤ centralizer (ZG : Set G) :=
    (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hZQ : ZG ≤ centralizer (Q : Set G) :=
    le_centralizer_iff.mp ((pCoreIn_le 2 H).trans hHZ)
  have hZcard : Nat.card ZG = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hUcard : Nat.card U = 32 :=
    (source_quintic_span_card_and_core_radical hG T hempty hM hu hmany hcard e H hH hi).1
  let : IsElementaryAbelian 2 U :=
    (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
  let D := (commutator R).map R.subtype
  let Z := (center R).map R.subtype
  have hRmap : R.map Q.subtype = P := map_subgroupOf_eq_of_le hPQ
  have hecomp : P.subtype.comp eR.toMonoidHom = Q.subtype.comp R.subtype := rfl
  have hcenter_e : (center R).map eR.toMonoidHom = center P := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr eR ⟨y,hy⟩).property
    · intro hx
      exact ⟨eR.symm x,(centerCongr eR.symm ⟨x,hx⟩).property,eR.apply_symm_apply x⟩
  have hDmap : D.map Q.subtype = U := by
    dsimp only [D]
    rw [map_subtype_commutator,map_commutator,hRmap,hPderived]
  have hZmap : Z.map Q.subtype = ZG := by
    dsimp only [Z]
    rw [map_map,←hecomp,←map_map,hcenter_e,hPcenter]
  have hDsub : D = U.subgroupOf Q := by
    rw [←hDmap]
    exact (comap_map_eq_self_of_injective Q.subtype_injective D).symm
  have hZsub : Z = ZG.subgroupOf Q := by
    rw [←hZmap]
    exact (comap_map_eq_self_of_injective Q.subtype_injective Z).symm
  have hRcard : Nat.card R = 512 := (Nat.card_congr eR.toEquiv).trans hPcard
  have hRtwo : IsPGroup 2 R := IsPGroup.of_card (n := 9) hRcard
  let : Group.IsNilpotent R := hRtwo.isNilpotent
  let : Group.IsNilpotent P := (hRtwo.of_equiv eR).isNilpotent
  have hclass : Group.nilpotencyClass R = 3 := by
    have hlo := Group.nilpotencyClass_le_of_surjective eR.toMonoidHom eR.surjective
    have hhi := Group.nilpotencyClass_le_of_surjective eR.symm.toMonoidHom eR.symm.surjective
    rw [hPclass] at hlo hhi
    omega
  have hCZ : centralizer (R : Set Q) = Z := by
    apply map_injective Q.subtype_injective
    rw [←top_inf_eq (centralizer (R : Set Q)),map_relative_centralizer _ _ _ Q.subtype_injective,
      ←MonoidHom.range_eq_map,range_subtype,hRmap,hZmap]
    exact hcentral
  have hcenter : center Q = Z := by
    apply le_antisymm
    · rw [←hCZ]
      intro x hx
      exact mem_centralizer_iff.mpr (fun r _ => mem_center_iff.mp hx r)
    · intro x hx
      apply mem_center_iff.mpr
      intro q
      exact Subtype.ext (hZQ (hZmap ▸ mem_map_of_mem Q.subtype hx) q q.property)
  have hzZ : z ∈ Z := by
    rw [hZsub]
    change t ^ 2 ∈ ZG
    exact hzgen.le (mem_zpowers (t ^ 2))
  have htorder : orderOf tQ = 4 := by rw [←orderOf_coe]; exact ht4
  have hzorder : orderOf z = 2 := by dsimp only [z]; rw [orderOf_pow,htorder]; decide
  have hbval : ((bR : R) : G) = b := congrArg (fun p : P => (p : G)) (eR.apply_symm_apply bP)
  have hfixed (x : R) (hx : ∀ a, ρ a x = x) : x ∈ center R := by
    have hxc : ((x : R) : G) ∈ P ⊓ (Q ⊓ centralizer (A : Set G)) := by
      refine ⟨x.property,(x : Q).property,mem_centralizer_iff.mpr ?_⟩
      intro a ha
      have he := congrArg (fun q : Q => (q : G)) (hx ⟨a,ha⟩)
      rw [hρ] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    have hxZ := (source_quintic_large_five_residual_center
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).2.1.le hxc
    have hm : (x : Q) ∈ Z := by rw [hZsub]; exact hxZ
    obtain ⟨y,hy,he⟩ := hm
    exact (Subtype.ext he : y = x) ▸ hy
  have hbD : bR ∉ commutator R := by
    intro hh
    apply hbU
    rw [←hbval]
    exact hDmap.le (mem_map_of_mem Q.subtype (mem_map_of_mem R.subtype hh))
  have hdata : ReeTwo.SemilinearExtensionData ρ R tQ z bR σ := by
    refine {
      actor_card := hA
      core_card := hlarge
      residual_card := hRcard
      residual_normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left Q A)
      residual_class := hclass
      invariant := hρR
      center_card := ?_
      derived_card := ?_
      derived_elementary := ?_
      derived_eq := ?_
      derived_commutator := ?_
      center_eq := hcenter
      residual_derived_centralizer := ?_
      residual_centralizer := hCZ
      fixed_central := hfixed
      root_outside := htP
      central_mem := hzZ
      central_order := hzorder
      root_square := rfl
      root_fixed := hρt
      root_centralizes := ?_
      root_generates := ?_
      root_centralizer := ?_
      root_commutator := ?_
      seed_square := ?_
      seed_outside := hbD
      seed_generates := ?_
      symmetry_invariant := hσR
      symmetry_squares := hσsq
      symmetry_root := hσt }
    · change Nat.card Z = 2
      rw [←card_map_of_injective Q.subtype_injective,hZmap,hZcard]
    · change Nat.card D = 32
      rw [←card_map_of_injective Q.subtype_injective,hDmap,hUcard]
    · change IsElementaryAbelian 2 D
      rw [hDsub]
      exact IsElementaryAbelian.subgroupOf hUQ
    · apply map_injective Q.subtype_injective
      rw [hDmap,map_subtype_commutator]
      exact (source_quintic_full_core_layers hG T hempty hM hu hmany hcard e H hH hi).1.symm
    · apply map_injective Q.subtype_injective
      rw [map_commutator,hDmap,hZmap,←MonoidHom.range_eq_map,range_subtype]
      exact (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2
    · apply map_injective Q.subtype_injective
      rw [map_relative_centralizer _ _ _ Q.subtype_injective,hRmap,hDmap]
      calc
        P ⊓ centralizer (U : Set G) = P ⊓ C := by
          dsimp only [C]
          rw [←inf_assoc,inf_eq_left.mpr (hPQ.trans (pCoreIn_le 2 H))]
        _ = U := hPC
    · exact mem_centralizer_iff.mpr (fun u hu => Subtype.ext
        (htU u (hDmap.le (mem_map_of_mem Q.subtype hu))))
    · apply map_injective Q.subtype_injective
      rw [Subgroup.map_sup,hRmap,MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype]
      exact htsup
    · apply map_injective Q.subtype_injective
      rw [map_inf _ _ _ Q.subtype_injective,hRmap,map_subtype_centralizer_singleton,
        hDmap,←inf_assoc,inf_eq_left.mpr hPQ]
      exact htcentral
    · apply map_injective Q.subtype_injective
      rw [map_commutator,hRmap,MonoidHom.map_zpowers,hDmap]
      exact htcomm
    · apply Subtype.ext
      apply Subtype.ext
      change ((bR : R) : G) ^ 2 = 1
      rw [hbval,hb2]
    · let : MulDistribMulAction A Q := MulDistribMulAction.compHom Q ρ
      let : IsInvariant A Q R := ⟨fun a x => (hρR a x).symm⟩
      have hfix : FixedPoints.subgroup A R ≤ center R := by
        intro x hx
        exact hfixed x (fun a => congrArg Subtype.val (hx a))
      have hg := Theory.GroupAction.parrott_orbit_closure_eq_top
        hRtwo hRcard hclass.ge hA hfix bR hbD
      have hm := congrArg (Subgroup.map R.subtype) hg
      rw [MonoidHom.map_closure,←Set.range_comp,←MonoidHom.range_eq_map,range_subtype] at hm
      exact hm
  exact ⟨tQ,z,bR,ρ,σ,hρ,htgen,hzgen,hdata⟩

/-- The intrinsic inputs construct the actual ten-root core equivalence, with
both the original central line and the original five-fixed cyclic root marked. -/
theorem source_quintic_large_five_core_marking
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5)
    (hcentral : H.pCoreIn 2 ⊓ centralizer ((⁅H.pCoreIn 2,A⁆ : Subgroup G) : Set G) = centralInvolutions T)
    (hseed : ∃ b ∈ ⁅H.pCoreIn 2,A⁆, b ^ 2 = 1 ∧
      b ∉ conjugateSpanBy (localModule T M) H) :
    ∃ eQ : ReeTwo.Core ≃* H.pCoreIn 2,
      zpowers (eQ (ReeTwo.Core.root 9) : G) = centralInvolutions T ∧
      zpowers (eQ (ReeTwo.Core.root 2) : G) = H.pCoreIn 2 ⊓ centralizer (A : Set G) := by
  obtain ⟨t,z,b,ρ,σ,_,htgen,hzgen,hdata⟩ :=
    source_quintic_large_five_semilinear_data hG T hempty hM hu hmany hcard e H hH hi
      hlarge A hAH hA hcentral hseed
  obtain ⟨a,ha⟩ := hdata.exists_frameCoordinates
  let D := (commutator ((⁅H.pCoreIn 2,A⁆).subgroupOf (H.pCoreIn 2))).map
    ((⁅H.pCoreIn 2,A⁆).subgroupOf (H.pCoreIn 2)).subtype
  let : IsElementaryAbelian 2 D := hdata.derived_elementary
  have hzC : z ∈ center (H.pCoreIn 2) := hdata.center_eq.symm ▸ hdata.central_mem
  have hz2 : z ^ 2 = 1 := by
    have hh := pow_orderOf_eq_one z
    rwa [hdata.central_order] at hh
  have hrel := ReeTwo.coreRelations_frameRoots_of_elementary D hdata.derived_eq.ge a t z ha
    hdata.root_centralizes hzC hdata.root_square hz2
  let f := ReeTwo.Core.lift hrel
  have hf9 : f (ReeTwo.Core.root 9) = z := by
    change ReeTwo.Core.lift hrel (ReeTwo.Core.root 9) = z
    rw [ReeTwo.Core.lift_root]
    rfl
  have hf2 : f (ReeTwo.Core.root 2) = t := by
    change ReeTwo.Core.lift hrel (ReeTwo.Core.root 2) = t
    rw [ReeTwo.Core.lift_root]
    rfl
  have hz : z ≠ 1 := by
    intro hh
    have ho := hdata.central_order
    rw [hh,orderOf_one] at ho
    contradiction
  have hinj := ReeTwo.Core.hom_injective_of_last_root f (by rw [hf9]; exact hz)
  have hbij := hinj.bijective_of_nat_card_le (by rw [ReeTwo.Core.card,hlarge])
  refine ⟨MulEquiv.ofBijective f hbij,?_,?_⟩
  · change zpowers (f (ReeTwo.Core.root 9) : G) = _
    rw [hf9]
    exact hzgen
  · change zpowers (f (ReeTwo.Core.root 2) : G) = _
    rw [hf2]
    exact htgen

end CFSG.Quasithin.Chapter14.Section06

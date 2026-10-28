module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.PairGeometry
public import Theory.GroupAction.SixteenOddComplements.Nine
public import Theory.GroupTheory.ReducedNormal.Basic

/-!
# The original moved module inside the two-core omega-center

The normal two-core of XT acts trivially on the original moved sixteen-group.
Its image commutes with the normal nine-group, whereas that nine-group has an
odd automorphism centralizer. Characteristic two then places the moved group
inside the two-core, and exponent two gives containment in its omega-center.

The faithful nine-on-sixteen action also has no common fixed vector. Thus the
source fixed summand is disjoint from the moved module, and the same conclusions
apply to each already constructed source factor. These discharge the containment
and disjointness fields of Earlier412; the whole-E decomposition is separate.
The full reduced normal subgroup of XT is also identified with this omega-center
using the known centralizer of the original internal normal closure.

Source: Aschbacher--Smith, 15.4.12(5), printed pp.1160--1161.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

private theorem core_kernel {H W : Type*} [Group H] [Finite H] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (f : H →* MulAut W)
    (A : Subgroup H) [A.Normal] (hA : Nat.card (A.map f) = 9)
    (hW : Nat.card W = 16) : pCore 2 H ≤ f.ker := by
  let R := (pCore 2 H).map f
  let B := A.map f
  have hR : IsPGroup 2 R := pCore_isPGroup.map f
  have hB : IsPGroup 3 B := IsPGroup.of_card (n := 2) hA
  have hd : Disjoint R B := IsPGroup.disjoint_of_ne 2 3 (by decide) R B hR hB
  have hc : ⁅R,B⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [show ⁅R,B⁆ = (⁅pCore 2 H,A⁆).map f from (map_commutator _ _ _).symm]
    exact ((map_mono (commutator_le_inf (pCore 2 H) A)).trans (map_inf_le _ _ _)).trans
      (disjoint_iff.mp hd).le
  have hRC : R ≤ centralizer (B : Set (MulAut W)) :=
    commutator_eq_bot_iff_le_centralizer.mp hc
  obtain ⟨n,hn⟩ := hR.exists_card_eq
  have hd' : Disjoint R (centralizer (B : Set (MulAut W))) :=
    disjoint_of_coprime_natCard (by
      rw [hn]
      exact (SixteenOddComplements.odd_centralizer_nine hW B hA).coprime_two_left.pow_left n)
  intro r hr
  exact disjoint_def.mp hd' (mem_map_of_mem f hr) (hRC (mem_map_of_mem f hr))

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.EarlierModule
open FamilySource FamilySource.ModuleStructure
open BinaryNormalizer Stellmacher Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}

theorem moved_core_centralizes (h : Input K T M X 2) :
    (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (movedModule T M X : Set G) := by
  let H := X ⊔ (T : Subgroup G)
  let W := movedModule (T : Subgroup G) M X
  let : IsElementaryAbelian 2 W := h.moved_elementary
  let f := moduleConjugation H W ((sup_le h.member_le h.sylow_le).trans h.moved_normalized)
  let A := X.subgroupOf H
  let : A.Normal := YFamily.normal_in_join h.member
  obtain ⟨ρ,hρinj,hρ⟩ := h.faithful_moved_action
  have he : A.map f = ρ.range := by
    ext a
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨memberProjection M X h.member_le ⟨x,hx⟩, ?_⟩
      ext w
      exact hρ ⟨x,hx⟩ w
    · rintro ⟨a,rfl⟩
      obtain ⟨x,rfl⟩ := memberProjection_surjective M X h.member_le a
      refine ⟨⟨x,(show X ≤ H from le_sup_left) x.property⟩,x.property,?_⟩
      ext w
      exact (hρ x w).symm
  have hA : Nat.card (A.map f) = 9 := by
    rw [he, ← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
    simpa using h.image_structure.2
  have hk := core_kernel f A hA (by simpa using h.moved_card)
  rintro q ⟨q,hq,rfl⟩ w hw
  have heq := DFunLike.congr_fun (hk hq) (⟨w,hw⟩ : W)
  have heq' : (q:G) * w * (q:G)⁻¹ = w := congrArg Subtype.val heq
  exact (mul_inv_eq_iff_eq_mul.mp heq').symm

theorem moved_le_omega (h : Input K T M X 2) :
    movedModule T M X ≤ omegaOneCenterAmbient ((X ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let W := movedModule (T : Subgroup G) M X
  let : IsElementaryAbelian 2 W := h.moved_elementary
  have hWT : W ≤ (T : Subgroup G) := h.moved_le.trans
    (localV_le_sylow T M h.sylow_le (h.ambient.evenCharacteristic T M h.maximal h.sylow_le))
  have hWH : W ≤ X ⊔ (T : Subgroup G) := hWT.trans le_sup_right
  have hWC := le_centralizer_iff.mp (moved_core_centralizes h)
  intro w hw
  have hwQ : w ∈ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
    apply mem_map.mpr
    refine ⟨⟨w,hWH hw⟩,h.join_characteristic ?_,rfl⟩
    intro q hq
    exact Subtype.ext (hWC hw q (mem_map_of_mem _ hq))
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨hwQ,elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := W) w hw,hWC hw⟩

theorem moved_fixed_eq_bot (h : Input K T M X 2) :
    movedModule T M X ⊓ centralizer (X : Set G) = ⊥ := by
  let W := movedModule (T : Subgroup G) M X
  let : IsElementaryAbelian 2 W := h.moved_elementary
  let : IsElementaryAbelian 3 (image M X) := h.image_structure.1
  obtain ⟨ρ,hρinj,hρ⟩ := h.faithful_moved_action
  let := MulDistribMulAction.compHom W ρ
  let : FaithfulSMul (image M X) W := ⟨fun {a b} hab => hρinj (MulEquiv.ext hab)⟩
  have hfix := common_fixed_eq_bot (W := W) (by simpa using h.image_structure.2)
    (by simpa using h.moved_card)
  apply le_bot_iff.mp
  intro w hw
  have hwf : (⟨w,hw.1⟩ : W) ∈ FixedPoints.subgroup (image M X) W := by
    intro a
    obtain ⟨x,rfl⟩ := memberProjection_surjective M X h.member_le a
    apply Subtype.ext
    change (ρ (memberProjection M X h.member_le x) (⟨w,hw.1⟩ : W) : G) = w
    rw [hρ]
    exact mul_inv_eq_iff_eq_mul.mpr (hw.2 x x.property)
  exact congrArg Subtype.val (show (⟨w,hw.1⟩ : W) = 1 from hfix.le hwf)

theorem fixedSummand_disjoint_moved (h : Input K T M X 2) :
    Disjoint (fixedSummand (T : Subgroup G) X) (movedModule T M X) := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro w hw
  exact (moved_fixed_eq_bot h).le ⟨hw.2,hw.1.2⟩
/-- The actual pair's two commutator modules occupy the original omega-center
and are disjoint from the original fixed summand; no pair is reselected. -/
theorem pair_factor_omega (h : Input K T M X 2) (p : Pair T M X) (i : Bool) :
    p.quotient.moduleFactor i ≤ omegaOneCenterAmbient ((X ⊔ (T : Subgroup G)).pCoreIn 2) ∧
    Disjoint (fixedSummand (T : Subgroup G) X) (p.quotient.moduleFactor i) := by
  have hi : p.quotient.moduleFactor i ≤ movedModule (T : Subgroup G) M X := by
    rw [← p.module_join]
    cases i
    · exact le_sup_left
    · exact le_sup_right
  exact ⟨hi.trans (moved_le_omega h), (fixedSummand_disjoint_moved h).mono_right hi⟩

private theorem omega_normal {H : Type*} [Group H] (Q : Subgroup H) [Q.Normal] :
    (omegaOneCenterAmbient Q).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  intro g _
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
    mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (Q : Set H) from by
      rw [normalizer_eq_top]; trivial)]

/-- The omega-center of the two-core is itself a reduced normal subgroup.
This is the internal R₂ placement used before applying the source E.2.3
decomposition. -/
theorem core_omega_reduced (h : Input K T M X 2) :
    IsPReduced 2 (omegaOneCenterAmbient
      (pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G))) := by
  let H := X ⊔ (T : Subgroup G)
  let Q := pCore 2 H
  let U := internalModule (T : Subgroup G) H
  let R := omegaOneCenterAmbient Q
  let : R.Normal := omega_normal Q
  have hUR : U ≤ R := internalModule_le_core_omega T H le_sup_right h.join_characteristic
  have hCQ : centralizer (R : Set H) = Q := by
    apply le_antisymm
    · exact (centralizer_le hUR).trans_eq
        (internal_centralizer T H le_sup_right h.center_centralizer)
    · intro q hq r hr
      exact ((mem_omegaOneCenterAmbient_iff Q r).mp hr).2.2 q hq |>.symm
  refine ⟨inferInstance, omegaOneCenterAmbient_elementaryAbelian Q, ?_⟩
  let q := QuotientGroup.mk' (centralizer (R : Set H))
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk',hCQ]
    exact pCore_isPGroup
  apply comap_injective (QuotientGroup.mk'_surjective _)
  rw [q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk]
  change pCore 2 H = q.ker
  rw [QuotientGroup.ker_mk',hCQ]

/-- The full reduced normal subgroup of XT is the omega-center of its
two-core, retaining the literal subgroup embedding in G. -/
theorem reduced_eq_omega (h : Input K T M X 2) :
    reducedTwoSubgroup (X ⊔ (T : Subgroup G) : Subgroup G) =
      omegaOneCenterAmbient
        (pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G)) := by
  let H := X ⊔ (T : Subgroup G)
  let R := reducedTwoSubgroup H
  let := (isPReduced_reducedPSubgroup (p := 2) (G := H)).elementary
  apply le_antisymm
  · intro v hv
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨reducedPSubgroup_le_pCore 2 H hv,
        elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := R) v hv,
        reducedPSubgroup_le_centralizer_pCore 2 H hv⟩
  · exact (core_omega_reduced h).le_reducedPSubgroup

theorem reduced_map_eq_omega (h : Input K T M X 2) :
    (reducedTwoSubgroup (X ⊔ (T : Subgroup G) : Subgroup G)).map
      (X ⊔ (T : Subgroup G)).subtype =
      omegaOneCenterAmbient ((X ⊔ (T : Subgroup G)).pCoreIn 2) := by
  rw [reduced_eq_omega h, ← omegaOneCenterAmbient_map_injective _
    (X ⊔ (T : Subgroup G)).subtype_injective]
  rfl

theorem moved_le_reduced (h : Input K T M X 2) :
    movedModule (T : Subgroup G) M X ≤
      (reducedTwoSubgroup (X ⊔ (T : Subgroup G) : Subgroup G)).map
        (X ⊔ (T : Subgroup G)).subtype := by
  rw [reduced_map_eq_omega h]
  exact moved_le_omega h

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.EarlierModule

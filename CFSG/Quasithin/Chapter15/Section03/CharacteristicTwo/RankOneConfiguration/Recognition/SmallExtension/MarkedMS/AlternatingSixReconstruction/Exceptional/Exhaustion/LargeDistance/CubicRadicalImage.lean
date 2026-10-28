module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicTerminalLine
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift

/-!
# The original radical image through the cubic quotient

For the original exceptional MS pair, the prescribed radical maps onto the
full two-core of its proper odd-index witness in S₆. First quotient by the
actual ambient two-core. The remaining kernel has order three and centralizes
the component. Its intersection with the odd-index witness is either trivial
or the whole kernel. In the latter case, normality of the witness's two-core
and coprime orders make that core centralize the kernel; the original product
then makes the kernel central. Central-kernel transport identifies the full
two-core image. Perfectness of the original component keeps the witness image
proper, using the retained kernel's no-supplement theorem.

The actual six-letter odd-index witness is a conjugate of a point parabolic,
plane parabolic, or Borel subgroup. Its radical image is consequently a full
point core, full plane core, or Sylow two-subgroup. In particular, point-core
containment implies equality. The original cubic graph's critical distance is
then exactly four by CubicTerminalLine. Whole-core and literal C.1.32 consumers
retain the plane and Sylow branches, both moving covers of orders 16 and 32,
and the same cubic projection. Distance-four exclusion, the other radical
branches, natural exhaustion, and both final reconstruction outcomes remain.

Source: Aschbacher--Smith C.1.31(MS2)(a) and the preliminary quotient argument
in C.1.32, printed pp.135--136; Meierfrankenfeld--Stellmacher (1993), (5.0)
and (5.11)--(5.12), printed pp.912,923--927. The permutation subgroup argument
uses the existing six-letter parabolic classification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
private theorem radical_restricted_kernel_central {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (C H : Subgroup A) (hcard : Nat.card f.ker = 3)
    (hC : f.ker ≤ centralizer (C : Set A)) (hsup : C ⊔ H.pCoreIn 2 = ⊤) :
    (f.subgroupMap H).ker ≤ center H := by
  let : Fact (Nat.card f.ker).Prime := ⟨hcard ▸ Nat.prime_three⟩
  rcases (H.subgroupOf f.ker).eq_bot_or_eq_top_of_prime_card with hbot | htop
  · intro x hx
    have hxk : (x : A) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxH : (⟨x,hxk⟩ : f.ker) ∈ H.subgroupOf f.ker := x.property
    rw [hbot,mem_bot] at hxH
    have he : x = 1 := Subtype.ext (congrArg (fun z : f.ker => (z : A)) hxH)
    rw [he]
    exact one_mem _
  · have hkH : f.ker ≤ H := subgroupOf_eq_top.mp htop
    have hk3 : IsPGroup 3 f.ker := IsPGroup.of_card (n := 1) (by simpa using hcard)
    have hd := hk3.disjoint_of_coprime (isPGroup_pCoreIn 2 H) (by decide : Nat.Coprime 3 2)
    have hn : H ≤ normalizer (H.pCoreIn 2 : Set A) := by
      have hh := (pCore 2 H).le_normalizer_map H.subtype
      rwa [normalizer_eq_top_iff.mpr (inferInstance : (pCore 2 H).Normal),
        ←MonoidHom.range_eq_map,range_subtype] at hh
    have hcomm : ⁅f.ker,H.pCoreIn 2⁆ = ⊥ := by
      apply le_bot_iff.mp
      rw [← hd.eq_bot]
      exact le_inf
        (le_normalizer_iff_commutator_le_left.mp le_normalizer_of_normal)
        (le_normalizer_iff_commutator_le_right.mp (hkH.trans hn))
    have hc : f.ker ≤ center A := by
      rw [← centralizer_univ,← coe_top,← hsup]
      apply le_centralizer_iff.mp
      exact sup_le (le_centralizer_iff.mp hC)
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm))
    intro x hx
    have hxk : (x : A) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hc hxk) y)

private theorem radical_map_core_of_cubic_kernel {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (C H : Subgroup A) (hcard : Nat.card f.ker = 3)
    (hC : f.ker ≤ centralizer (C : Set A)) (hsup : C ⊔ H.pCoreIn 2 = ⊤) :
    (H.pCoreIn 2).map f = (H.map f).pCoreIn 2 := by
  have he := (f.subgroupMap H).map_pCore_of_central_kernel
    (f.subgroupMap_surjective H) (radical_restricted_kernel_central f C H hcard hC hsup) (p := 2)
  have hh := congrArg (map (H.map f).subtype) he
  change (H.pCoreIn 2).map f = _
  rw [pCoreIn,map_map]
  rw [map_map] at hh
  exact hh

private theorem radical_between_prime_index {A : Type*} [Group A]
    (P H F : Subgroup A) (hPH : P ≤ H) (hHF : H ≤ F)
    (hi : P.relIndex F = 3) : H = P ∨ H = F := by
  have he := relIndex_mul_relIndex P H F hPH hHF
  rw [hi] at he
  rcases (Nat.dvd_prime Nat.prime_three).mp (dvd_of_mul_right_eq _ he) with h1 | h3
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp h1) hPH)
  · have h1 : H.relIndex F = 1 := by
      rw [h3] at he
      omega
    exact Or.inr (le_antisymm hHF (relIndex_eq_one.mp h1))

open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
private theorem radical_odd_index_subgroup_cases (H : Subgroup S)
    (hH : H ≠ ⊤) (ho : Odd H.index) :
    ∃ g : S, H = borel.map (MulAut.conj g).toMonoidHom ∨
      H = duadStabilizer.map (MulAut.conj g).toMonoidHom ∨
      H = synthemeStabilizer.map (MulAut.conj g).toMonoidHom := by
  let T : Sylow 2 H := Classical.choice (inferInstance : Nonempty (Sylow 2 H))
  have hnot : ¬2 ∣ ((T : Subgroup H).map H.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two T.not_dvd_index ho.not_two_dvd_nat
  let P : Sylow 2 S := (T.isPGroup'.map H.subtype).toSylow hnot
  have hPH : (P : Subgroup S) ≤ H := map_subtype_le _
  clear_value P T
  obtain ⟨F,hF,hHF⟩ := (eq_top_or_exists_le_coatom H).resolve_left hH
  obtain ⟨g,hg,hmax⟩ := coatoms_over_sylow P
  change borel.map (MulAut.conj g).toMonoidHom = (P : Subgroup S) at hg
  refine ⟨g,?_⟩
  rcases (hmax F).mp ⟨hF,hPH.trans hHF⟩ with hduad | hsyn
  · change F = duadStabilizer.map (MulAut.conj g).toMonoidHom at hduad
    have hi : (P : Subgroup S).relIndex F = 3 := by
      rw [←hg,hduad,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
      exact borel_relIndex_duad
    rcases radical_between_prime_index (P : Subgroup S) H F hPH hHF hi with he | he
    · exact Or.inl (he.trans hg.symm)
    · exact Or.inr (Or.inl (he.trans hduad))
  · change F = synthemeStabilizer.map (MulAut.conj g).toMonoidHom at hsyn
    have hi : (P : Subgroup S).relIndex F = 3 := by
      rw [←hg,hsyn,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
      exact borel_relIndex_syntheme
    rcases radical_between_prime_index (P : Subgroup S) H F hPH hHF hi with he | he
    · exact Or.inl (he.trans hg.symm)
    · exact Or.inr (Or.inr (he.trans hsyn))

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- MS2(a) descends through the literal cubic projection: the image of the
original radical is the two-core of a proper odd-index subgroup of S₆. -/
theorem radical_image_msOddIndex : ChapterC.MSOddIndexRadical ((Rg).map π) := by
  obtain ⟨H,hH,ho,hR⟩ := h.relative_radical
  change H.pCoreIn 2 = Rg at hR
  let q := QuotientGroup.mk' (pCore 2 M)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hqker : IsPGroup 2 q.ker := by
    rw [show q.ker = pCore 2 M from QuotientGroup.ker_mk' _]
    exact pCore_isPGroup
  have hQH : pCore 2 M ≤ H :=
    (h.relative_radical.twoCore_le).trans (hR.symm.le.trans (H.pCoreIn_le 2))
  have hQπ : pCore 2 M ≤ (π).ker := by
    rw [CubicAction.projection_kernel]
    exact le_sup_right
  let f := QuotientGroup.lift (pCore 2 M) π hQπ
  have hcomp : f.comp q = π := rfl
  have hfker : f.ker = (extensionKernel h).map q := by
    rw [QuotientGroup.ker_lift,CubicAction.projection_kernel]
  have hcard : Nat.card f.ker = 3 := by
    rw [hfker,←relIndex_ker,show q.ker = pCore 2 M from QuotientGroup.ker_mk' _]
    change ((pCore 2 M).comap (extensionKernel h).subtype).index = 3
    rw [← pCore_subnormal_eq_comap 2
      (inferInstance : (extensionKernel h).Normal).isSubnormal]
    exact extensionKernel_core_index h hz
  have hC : f.ker ≤ centralizer ((K).map q : Set (M ⧸ pCore 2 M)) := by
    rw [hfker,extensionKernel_image_eq_centralizer h e]
  have hcores := map_pCoreIn_of_ker_isPGroup q hqker H (p := 2)
  have hKR : K ⊔ Rg = ⊤ := by
    rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hsup : (K).map q ⊔ (H.map q).pCoreIn 2 = ⊤ := by
    rw [←hcores,hR,←Subgroup.map_sup,hKR,map_top_of_surjective q hq]
  have hcore : (H.pCoreIn 2).map π = (H.map π).pCoreIn 2 := by
    rw [←hcomp,←map_map,hcores,
      radical_map_core_of_cubic_kernel f ((K).map q) (H.map q) hcard hC hsup,map_map]
  refine ⟨H.map π,lt_top_iff_ne_top.mpr ?_,
    ho.of_dvd_nat (H.index_map_dvd (CubicEven.projection_surjective h e hz hk)),?_⟩
  · intro ht
    have hHE : H ⊔ extensionKernel h = ⊤ := by
      rw [←CubicAction.projection_kernel h e hz hk,←comap_map_eq,ht,comap_top]
    have hE := extensionKernel_no_supplement h H (show K ≤ H ⊔ extensionKernel h by
      rw [hHE]; exact le_top)
    rw [extensionKernel_twoCore,sup_of_le_left hQH] at hE
    exact hH.ne (by rwa [sup_of_le_left hE] at hHE)
  · change (H.map π).pCoreIn 2 = (Rg).map π
    rw [←hcore,hR]

include h e hz hk in
/-- The original radical has exactly a point-core, plane-core, or Sylow image.
The conjugation maps belong to the original cubic permutation action. -/
theorem radical_image_cases : ∃ g : S,
    (Rg).map π = pointCore.map (MulAut.conj g).toMonoidHom ∨
    (Rg).map π = D.map (MulAut.conj g).toMonoidHom ∨
    (Rg).map π = borel.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨H,hH,ho,hcore⟩ := radical_image_msOddIndex h e hz hk
  change H.pCoreIn 2 = (Rg).map π at hcore
  obtain ⟨g,hB | hP | hD⟩ := radical_odd_index_subgroup_cases H hH.ne ho
  · refine ⟨g,Or.inr (Or.inr ?_)⟩
    rw [←hcore,hB,←map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
      pCoreIn_eq_self_of_isPGroup 2 borel borelSylow.isPGroup']
  · refine ⟨g*flagRelabel⁻¹,Or.inl ?_⟩
    rw [←hcore,hP,←map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
      ←H1_core_eq_pointCore,←flagRelabel_duad,
      ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj flagRelabel).injective,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change g*x*g⁻¹ = (g*flagRelabel⁻¹)*(flagRelabel*x*flagRelabel⁻¹)*(g*flagRelabel⁻¹)⁻¹
    group
  · refine ⟨g,Or.inr (Or.inl ?_)⟩
    rw [←hcore,hD,←map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
    exact congrArg (map (MulAut.conj g).toMonoidHom) H2_core_eq_D

include h e hz hk in
/-- The prescribed odd-index radical has image order eight or sixteen. -/
theorem radical_image_card : Nat.card ((Rg).map π) = 8 ∨ Nat.card ((Rg).map π) = 16 := by
  obtain ⟨g,hP | hD | hB⟩ := radical_image_cases h e hz hk
  · left
    rw [hP,card_map_of_injective (MulAut.conj g).injective,pointCore_card]
  · left
    rw [hD,card_map_of_injective (MulAut.conj g).injective,D_card]
  · right
    rw [hB,card_map_of_injective (MulAut.conj g).injective,borel_order]

include h e hz hk in
/-- Containment in a point core is already equality for the original radical;
this uses its original proper odd-index witness, not a Sylow assumption. -/
theorem full_point_image_of_contained (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom := by
  apply eq_of_le_of_card_ge hR
  rw [card_map_of_injective (MulAut.conj u).injective,pointCore_card]
  rcases radical_image_card h e hz hk with he | he <;> omega

include h e hz hk in
/-- The original cubic point-image branch has critical distance exactly four. -/
theorem point_image_distance_eq_four (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    sourceDistance h = 4 := by
  have hb := distance_gt_two h e hz hk
  exact (full_point_distance_two_or_four h e hz hk u
    (full_point_image_of_contained h e hz hk u hR)).resolve_left (by omega)

omit hk in
include h e hz in
/-- Whole-core exhaustion now leaves the exact original radical images.
The point-core branch is confined to distance four; plane and Sylow images
remain separate source obligations. Both full moving covers are retained. -/
theorem coreExhaustion_or_cubic_radical_cases :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg,
        color Rg a = false →
        Nat.card (U Rg a) = 16 ∨
        Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (sourceDistance h = 4 ∧ (Rg).map (CubicAction.projection h e hz hk) =
          pointCore.map (MulAut.conj u).toMonoidHom) ∨
        (Rg).map (CubicAction.projection h e hz hk) = D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) = borel.map (MulAut.conj u).toMonoidHom := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,?_⟩
    obtain ⟨u,hP | hD | hB⟩ := radical_image_cases h e hz hk
    · exact ⟨u,Or.inl ⟨point_image_distance_eq_four h e hz hk u hP.le,hP⟩⟩
    · exact ⟨u,Or.inr (Or.inl hD)⟩
    · exact ⟨u,Or.inr (Or.inr hB)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the original cubic radical classification.
The same quotient map, graph, and full moving covers are retained. -/
theorem rankTwo_or_cubic_radical_cases :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg,
        color Rg a = false →
        Nat.card (U Rg a) = 16 ∨
        Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (sourceDistance h = 4 ∧ (Rg).map (CubicAction.projection h e hz hk) =
          pointCore.map (MulAut.conj u).toMonoidHom) ∨
        (Rg).map (CubicAction.projection h e hz hk) = D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) = borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_radical_cases h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

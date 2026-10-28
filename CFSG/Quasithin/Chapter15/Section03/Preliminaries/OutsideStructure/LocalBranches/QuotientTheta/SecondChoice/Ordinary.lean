module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.Cores
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# The ordinary second-choice quotient in 15.3.11

The action of Y₊S on the moving plane is onto SL₂(2): Y₊ supplies the
cubic rotation and S acts nontrivially on that plane. In the ordinary
alternative of 15.3.7, the kernel in Y₊ lies in O₂(Y), because it fixes
both definite planes. The full kernel is therefore a two-group extension
of a two-group. The actual S₃ action identifies that kernel with O₂(Y₊S).
The supplied Sylow subgroup of I puts this normal kernel inside S, giving
R = C_S(V₂). No current local quotient or rank-one alternative is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.7(1)
and the second-choice proof of 15.3.11(5ii), printed pp.1122–1124.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta
open RankTwo RankTwo.FullActionCoordinates
local instance : MulDistribMulAction OrthogonalPlaneActor OrthogonalPlaneVector :=
  FourGroupMatrixCoordinates.naturalAction
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem chosen_le_m (d : CharacteristicTwo.LocalData G) :
    d.Yplus ⊔ d.S ≤ d.M :=
  sup_le ((choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice).trans
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc))
    (inf_le_left.trans d.sylow_le)

private theorem chosen_normalizes_plane (d : CharacteristicTwo.LocalData G)
    (i : OrthogonalPlaneIndex) : d.Yplus ⊔ d.S ≤ normalizer (d.action.plane i : Set G) :=
  (sup_le_sup_right (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice) _).trans
    (ys_normalizes_plane d i)

private def planeActor (d : CharacteristicTwo.LocalData G) (i : OrthogonalPlaneIndex) :
    (d.Yplus ⊔ d.S : Subgroup G) →* OrthogonalPlaneActor where
  toFun x := (d.action.actor ⟨x, chosen_le_m d x.property⟩).left i
  map_one' := by
    change (d.action.actor 1).left i = 1
    rw [map_one]
    rfl
  map_mul' x y := by
    have hx := plane_actor_shift_eq_one d.action
      ⟨x, chosen_le_m d x.property⟩ i (chosen_normalizes_plane d i x.property)
    change (d.action.actor (⟨x, chosen_le_m d x.property⟩ * ⟨y, chosen_le_m d y.property⟩)).left i = _
    rw [map_mul]
    change (d.action.actor ⟨x, chosen_le_m d x.property⟩).left i *
      (d.action.actor ⟨y, chosen_le_m d y.property⟩).left ((d.action.actor ⟨x, chosen_le_m d x.property⟩).right⁻¹ * i) = _
    rw [hx, inv_one, one_mul]

private theorem mem_planeActor_ker (d : CharacteristicTwo.LocalData G)
    (i : OrthogonalPlaneIndex) (x : (d.Yplus ⊔ d.S : Subgroup G)) :
    x ∈ (planeActor d i).ker ↔ (x : G) ∈ centralizer (d.action.plane i : Set G) := by
  let m : d.M := ⟨x, chosen_le_m d x.property⟩
  have hs : (d.action.actor m).right = 1 :=
    plane_actor_shift_eq_one d.action m i (chosen_normalizes_plane d i x.property)
  have hfix : (x : G) ∈ centralizer (d.action.plane i : Set G) ↔
      ∀ w ∈ orthogonalCoordinatePlane i, d.action.actor m • w = w := by
    have he := d.action.centralizer_map_eq_comap (orthogonalCoordinatePlane i)
    rw [← d.action.plane_eq_map] at he
    exact Iff.of_eq (congrArg (fun K : Subgroup d.M => m ∈ K) he)
  rw [hfix]
  constructor
  · intro hx w hw
    change (d.action.actor m).left i = 1 at hx
    funext j
    change (d.action.actor m).left j • w ((d.action.actor m).right⁻¹ * j) = w j
    rw [hs, inv_one, one_mul]
    by_cases hj : j = i
    · rw [hj, hx, one_smul]
    · rw [hw j hj, smul_one]
  · intro hx
    change (d.action.actor m).left i = 1
    let _ := FourGroupMatrixCoordinates.naturalAction_faithful
    apply FaithfulSMul.eq_of_smul_eq_smul (α := OrthogonalPlaneVector)
    intro v
    let w : OrthogonalVector := fun j => if j = i then v else 1
    have hw : w ∈ orthogonalCoordinatePlane i := fun j hj => if_neg hj
    have he := congrFun (hx w hw) i
    change (d.action.actor m).left i • w ((d.action.actor m).right⁻¹ * i) = w i at he
    simpa only [hs, inv_one, one_mul, w, if_pos rfl, one_smul] using he


omit [Finite G] in
private theorem planeStabilizer_eq (d : CharacteristicTwo.LocalData G)
    (i : OrthogonalPlaneIndex) : d.S = planeStabilizer d.T (d.action.plane i) := by
  apply le_antisymm
  · exact le_inf inf_le_left (s_normalizes_plane d i)
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have hn : (⟨x, d.sylow_le hx.1⟩ : d.M) ∈
        (normalizer (d.action.plane i : Set G)).subgroupOf d.M := hx.2
    rw [d.action.plane_normalizer_eq_comap,
      OrthogonalGeometry.setwise_plane_eq_ker] at hn
    change (⟨x, d.sylow_le hx.1⟩ : d.M) ∈
      (normalizer (d.action.plane 1 : Set G)).subgroupOf d.M
    rwa [d.action.plane_normalizer_eq_comap, OrthogonalGeometry.setwise_plane_eq_ker]

private theorem planeActor_onto (d : CharacteristicTwo.LocalData G)
    (hsecond : OutsideStructure.SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    Function.Surjective (planeActor d (Multiplicative.ofAdd (1 : ZMod 2))) := by
  let j : OrthogonalPlaneIndex := Multiplicative.ofAdd (1 : ZMod 2)
  let f := planeActor d j
  have hc : cubicMatrix ∈ f.range := by
    have hh : coordinateCubic j ∈ d.action.image d.Yplus := by
      rw [hsecond.2]
      change coordinateCubic j ∈ d.action.image (centralizingFactor d.Y d.V₁)
      rw [residualY_centralizingFactor_image_eq_coordinateCubic d.action h7image
        (show (1 : OrthogonalPlaneIndex) ≠ j from by decide)]
      exact mem_zpowers _
    obtain ⟨m, hm, he⟩ := hh
    refine ⟨⟨m, mem_sup_left hm⟩, ?_⟩
    change (d.action.actor m).left j = cubicMatrix
    rw [he]
    simp [coordinateCubic, coordinateEmbedding]
  have hS : ¬ d.S ≤ centralizer (d.action.plane j : Set G) := by
    intro h
    have hh : fixedPlane (d.action.plane j) d.S = d.action.plane j :=
      inf_eq_left.mpr (le_centralizer_iff.mp h)
    have hhcard := d.action.card_plane_fixed_planeStabilizer d.T d.sylow_le j
    rw [← planeStabilizer_eq d j, hh, d.action.card_plane] at hhcard
    omega
  obtain ⟨s, hs, hsc⟩ := SetLike.not_le_iff_exists.mp hS
  let s₀ : (d.Yplus ⊔ d.S : Subgroup G) := ⟨s, mem_sup_right hs⟩
  have ht : f s₀ ≠ 1 := fun he => hsc ((mem_planeActor_ker d j s₀).mp he)
  have ht2 : (f s₀) ^ 2 = 1 := by
    let r : d.S →* OrthogonalPlaneActor := f.comp (inclusion le_sup_right)
    have hr := (d.T.isPGroup'.to_le (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).of_surjective r.rangeRestrict r.rangeRestrict_surjective
    have hcop := hr.orderOf_coprime (by decide : Nat.Coprime 2 3)
      (⟨r ⟨s, hs⟩, ⟨⟨s, hs⟩, rfl⟩⟩ : r.range)
    rw [← Subgroup.orderOf_coe] at hcop
    have hd : orderOf (f s₀) ∣ 6 := by
      have hcard : Nat.card OrthogonalPlaneActor = 6 := by
        rw [Nat.card_eq_fintype_card]; decide +kernel
      rw [← hcard]
      exact orderOf_dvd_natCard _
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_mul_right.mp hd)
  have hgen : ∀ t : OrthogonalPlaneActor, t ≠ 1 → t ^ 2 = 1 →
      ∀ a : OrthogonalPlaneActor,
      a = 1 ∨ a = cubicMatrix ∨ a = cubicMatrix ^ 2 ∨ a = t ∨
        a = cubicMatrix * t ∨ a = cubicMatrix ^ 2 * t := by decide +kernel
  intro a
  apply MonoidHom.mem_range.mp
  rcases hgen (f s₀) ht ht2 a with he | he | he | he | he | he <;> rw [he]
  · exact f.range.one_mem
  · exact hc
  · exact f.range.pow_mem hc 2
  · exact ⟨s₀, rfl⟩
  · exact f.range.mul_mem hc ⟨s₀, rfl⟩
  · exact f.range.mul_mem (f.range.pow_mem hc 2) ⟨s₀, rfl⟩

private theorem ordinary_plane_kernel_isPGroup (d : CharacteristicTwo.LocalData G)
    (hsecond : OutsideStructure.SecondChoice d)
    (hord : FusionCore.CosetSetup.ExtraspecialLocal.OrdinaryCase d.M d.Y d.V) :
    IsPGroup 2 (planeActor d (Multiplicative.ofAdd (1 : ZMod 2))).ker := by
  let H := d.Yplus ⊔ d.S
  let N := d.Yplus.subgroupOf H
  let _ : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    ((sup_le_sup_right (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice) _).trans
      (ys_normalizes_yplus d))
  have hgen : N ⊔ d.S.subgroupOf H = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  have hquot : IsPGroup 2 (H ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (d.S.subgroupOf H)
      (d.T.isPGroup'.to_le (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).comap_subtype hgen
  let f := planeActor d (Multiplicative.ofAdd (1 : ZMod 2))
  let q := (QuotientGroup.mk' N).comp f.ker.subtype
  have hplus (x : q.ker) : ((x.val.val : H) : G) ∈ d.Yplus :=
    (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property
  let r : q.ker →* d.Y :=
    (H.subtype.comp (f.ker.subtype.comp q.ker.subtype)).codRestrict d.Y (by
      intro x
      exact choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice (hplus x))
  have hr : ∀ x : q.ker, r x ∈ pCore 2 d.Y := by
    intro x
    have hC1 : ((x.val.val : H) : G) ∈ centralizer (d.V₁ : Set G) := by
      have hle : d.Yplus ≤ centralizer (d.V₁ : Set G) := by
        rw [hsecond.2]
        exact (map_subtype_le _).trans inf_le_right
      exact hle (hplus x)
    have hC2 : ((x.val.val : H) : G) ∈ centralizer (d.V₂ : Set G) :=
      (mem_planeActor_ker d _ _).mp x.val.property
    have hCV : ((x.val.val : H) : G) ∈ centralizer (d.V : Set G) := by
      apply centralizer_le (natural_planes_sup d.action (show (1 : OrthogonalPlaneIndex) ≠
        Multiplicative.ofAdd (1 : ZMod 2) from by decide)).ge
      rw [sup_eq_closure, centralizer_closure]
      intro v hv
      rcases hv with hv | hv
      · exact hC1 v hv
      · exact hC2 v hv
    have hh : ((x.val.val : H) : G) ∈ d.Y.pCoreIn 2 :=
      hord.centralizer_eq ▸ ⟨(r x).property, hCV⟩
    obtain ⟨y, hy, he⟩ := hh
    exact (Subtype.ext he : y = r x) ▸ hy
  let r' : q.ker →* pCore 2 d.Y := r.codRestrict _ hr
  have hqker : IsPGroup 2 q.ker := by
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 d.Y => (x.val : G)) hab
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv


omit [Finite G] in
/-- A Sylow witness in the outside overgroup contains the intrinsic core
of its intermediate subgroup Y₊S. This bound applies to both source choices. -/
theorem chosen_core_le_s_of_sylow (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus)
    (hSylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S) : d.R ≤ d.S := by
  obtain ⟨P, hP⟩ := hSylow
  let f : (d.Yplus ⊔ d.S : Subgroup G) →* I := inclusion hI.1.2
  have hrange : (P : Subgroup I) ≤ f.range := by
    intro p hp
    have hs : (p : G) ∈ d.S := hP ▸ mem_map_of_mem I.subtype hp
    exact ⟨⟨p, mem_sup_right hs⟩, rfl⟩
  let Q : Sylow 2 (d.Yplus ⊔ d.S : Subgroup G) :=
    P.comapOfInjective f (inclusion_injective hI.1.2) hrange
  rintro x ⟨a, ha, rfl⟩
  have hh := (pCore_isPGroup (p := 2) (G := (d.Yplus ⊔ d.S : Subgroup G))).le_sylow_of_normal Q ha
  have hm : (a : G) ∈ (P : Subgroup I).map I.subtype := ⟨f a, hh, rfl⟩
  exact hP.le hm

/-- In the ordinary earlier alternative, the actual moving-plane action
has S₃ quotient and kernel C_S(V₂). -/
theorem second_choice_ordinary_quotient_and_core (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus)
    (hsecond : OutsideStructure.SecondChoice d)
    (hord : FusionCore.CosetSetup.ExtraspecialLocal.OrdinaryCase d.M d.Y d.V)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hSylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S) :
    Nonempty ((↥(d.Yplus ⊔ d.S) ⧸ pCore 2 ↥(d.Yplus ⊔ d.S)) ≃* Equiv.Perm (Fin 3)) ∧
      d.R = d.S ⊓ centralizer (d.V₂ : Set G) := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let a := planeActor d (Multiplicative.ofAdd (1 : ZMod 2))
  let f := e.toMonoidHom.comp a
  have hf : Function.Surjective f := e.surjective.comp (planeActor_onto d hsecond h7image)
  have hker : f.ker = a.ker := MonoidHom.ker_comp_of_injective a e.toMonoidHom e.injective
  have hp : IsPGroup 2 f.ker := hker ▸ ordinary_plane_kernel_isPGroup d hsecond hord
  have he : a.ker = pCore 2 ↥(d.Yplus ⊔ d.S) :=
    hker.symm.trans (ker_eq_twoCore_of_surjective_perm_three f hf hp)
  refine ⟨⟨(QuotientGroup.quotientMulEquivOfEq
    (ker_eq_twoCore_of_surjective_perm_three f hf hp).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩, ?_⟩
  apply le_antisymm
  · refine le_inf (chosen_core_le_s_of_sylow d I hI hSylow) ?_
    rintro x ⟨a, ha, rfl⟩
    exact (mem_planeActor_ker d _ a).mp (he.ge ha)
  · rintro x ⟨hs, hc⟩
    exact ⟨⟨x, mem_sup_right hs⟩, he.le ((mem_planeActor_ker d _ _).mpr hc), rfl⟩

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta

end

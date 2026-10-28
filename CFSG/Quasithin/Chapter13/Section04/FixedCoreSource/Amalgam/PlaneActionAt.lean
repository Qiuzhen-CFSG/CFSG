module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneAction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryAugmentationAt

/-!
# Guarded simultaneous markings for the original plane

Extend the original augmentation action to LT, align its Sylow image,
and identify the actual plane normalizer and its full kernel. Every
structural call is at the same G,T with its Hypothesis1223 guard.
PlaneAlphaAt and PlaneBaumannAt use these literal action coordinates.
Source: Aschbacher--Smith 13.2.2(10), p.878, and 13.4.7(4), pp.902--903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher BinaryPermutation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

private theorem sylowCarrier_eq_flags : ChapterB.Offenders.Six.sylowCarrier = H1 ⊓ H2 := by
  have hc : ∀ i, ChapterB.Offenders.Six.sylowWords i ∈ H1 ⊓ H2 := by
    simp only [mem_inf]
    decide +kernel
  have hh : (ChapterB.Offenders.Six.sylow : Subgroup S) ≤ canonicalSylow := by
    rw [canonicalSylow_coe]
    intro x hx
    obtain ⟨i,rfl⟩ := (ChapterB.Offenders.Six.mem_sylowCarrier_iff x).mp hx
    exact hc i
  exact (ChapterB.Offenders.Six.sylow.3 canonicalSylow.isPGroup' hh).symm.trans canonicalSylow_coe

private theorem planeCube_eq : D = ChapterB.Offenders.D 6 := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x (rfl | rfl | rfl)
    · exact subset_closure ⟨0,by decide,rfl⟩
    · exact subset_closure ⟨1,by decide,rfl⟩
    · exact subset_closure ⟨2,by decide,rfl⟩
  · apply (closure_le _).mpr
    rintro x ⟨i,hi,rfl⟩
    fin_cases i <;> exact subset_closure (by simp [ChapterB.Offenders.pairSwap, swap01, swap23, swap45])

private theorem exists_sylow_alignment {E : Type*} [Group E] [Finite E]
    (T : Sylow 2 E) (q : E →* S) :
    ∃ g : S, ((T : Subgroup E).map q).map (MulAut.conj g).toMonoidHom =
      ChapterB.Offenders.Six.sylowCarrier ⊓ (q.range.map (MulAut.conj g).toMonoidHom) := by
  let P := T.mapSurjective q.rangeRestrict_surjective
  obtain ⟨U,hU⟩ := P.exists_comap_subtype_eq
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S U ChapterB.Offenders.Six.sylow
  have hmap : (T : Subgroup E).map q = (U : Subgroup S) ⊓ q.range := by
    have he := congrArg (fun A : Subgroup q.range => A.map q.range.subtype) hU
    change ((U : Subgroup S).comap q.range.subtype).map q.range.subtype =
      ((T : Subgroup E).map q.rangeRestrict).map q.range.subtype at he
    rw [map_comap_eq,range_subtype,map_map] at he
    have hcomp : q.range.subtype.comp q.rangeRestrict = q := by ext x; rfl
    simpa only [inf_comm,hcomp] using he.symm
  refine ⟨g,?_⟩
  rw [hmap,map_inf _ _ _ (MulAut.conj g).injective]
  have hu : (U : Subgroup S).map (MulAut.conj g).toMonoidHom = ChapterB.Offenders.Six.sylowCarrier := by
    exact congrArg (fun P : Sylow 2 S => (P : Subgroup S)) hg
  rw [hu]


universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem original_plane_image
    (D : ChosenModule T L V) (m : CoreMarking D)
    (X : Subgroup G) (hn : X ≤ normalizer (V : Set G)) (q : X →* S)
    (he : ∀ (x : X) (v : V),
      (m.coordinate (V.normalizerMonoidHom ⟨x.val,hn x.property⟩ v)).toAdd =
        coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd)
    (W : Submodule (ZMod 2) (natural (Fin 6))) :
    ((X ⊓ normalizer (m.naturalPreimage W : Set G)).subgroupOf X).map q =
      flagStabilizer W ⊓ q.range := by
  have hc (x : X) (v : V) :
      coreToNatural (Fin 6)
        (m.coordinate (V.normalizerMonoidHom ⟨x.val,hn x.property⟩ v)).toAdd =
      naturalRepresentation (Fin 6) (q x)
        (coreToNatural (Fin 6) (m.coordinate v).toAdd) := by
    rw [he,coreToNatural_equivariant]
  have hi (x : X) : x.val ∈ normalizer (m.naturalPreimage W : Set G) ↔
      q x ∈ flagStabilizer W := by
    constructor
    · intro hx w
      obtain ⟨c,rfl⟩ := coreToNatural_surjective w
      obtain ⟨v,hv⟩ := m.coordinate.surjective (Multiplicative.ofAdd c)
      have hh : (m.coordinate v).toAdd = c := congrArg Multiplicative.toAdd hv
      rw [←hh,←hc,←m.mem_naturalPreimage,←m.mem_naturalPreimage]
      exact ((mem_normalizer_iff.mp hx) v.val).symm
    · intro hx
      apply mem_normalizer_iff.mpr
      intro y
      by_cases hy : y ∈ V
      · have hh := hx (coreToNatural (Fin 6) (m.coordinate ⟨y,hy⟩).toAdd)
        rw [←hc,←m.mem_naturalPreimage,←m.mem_naturalPreimage] at hh
        exact hh.symm
      · have hy' : x.val*y*x.val⁻¹ ∉ V := fun hh =>
          hy (((mem_normalizer_iff.mp (hn x.property)) y).mpr hh)
        exact iff_of_false (fun hh => hy (m.naturalPreimage_le W hh))
          (fun hh => hy' (m.naturalPreimage_le W hh))
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨(hi x).mp hx.2,⟨x,rfl⟩⟩
  · rintro ⟨ha,x,rfl⟩
    exact ⟨x,⟨x.property,(hi x).mpr ha⟩,rfl⟩

/-- A single actual action aligns the Sylow image and the two-core of the
original plane normalizer. The entire action kernel is retained. -/
theorem exists_original_plane_action_coordinates_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    let X := L ⊔ (T : Subgroup G)
    let B := X ⊓ normalizer (m.naturalPreimage W : Set G)
    ∃ q : X →* S, ∃ e : V ≃* Multiplicative (core (Fin 6)),
      (∀ (x : X) (v : V),
        (e (V.normalizerMonoidHom
          ⟨x.val,(sup_le D.normalizes ((structural L h).2.2 V D).1) x.property⟩ v)).toAdd =
          coreRepresentation (Fin 6) (q x) (e v).toAdd) ∧
      q.ker = pCore 2 X ∧
      q.ker = centralizer (V.subgroupOf X : Set X) ∧
      alternatingGroup (Fin 6) ≤ q.range ∧
      ((T : Subgroup G).subgroupOf X).map q =
        ChapterB.Offenders.Six.sylowCarrier ⊓ q.range ∧
      ((B.pCoreIn 2).subgroupOf X).map q ≤ ChapterB.Offenders.D 6 := by
  let X := L ⊔ (T : Subgroup G)
  let B := X ⊓ normalizer (m.naturalPreimage W : Set G)
  let TX := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  have hn : X ≤ normalizer (V : Set G) :=
    sup_le D.normalizes ((structural L h).2.2 V D).1
  obtain ⟨q₀,he₀,_,hL₀,hk₀⟩ :=
    LocalGeometry.exists_core_product_permutation_at D m h structural eL
  have hi₀ := original_plane_image D m X hn q₀ he₀ W
  have hA₀ : alternatingGroup (Fin 6) ≤ q₀.range := hL₀ ▸ map_le_range q₀ _
  obtain ⟨g,hg⟩ := exists_sylow_alignment TX q₀
  let q := (MulAut.conj g).toMonoidHom.comp q₀
  have hr : q.range = q₀.range.map (MulAut.conj g).toMonoidHom := MonoidHom.range_comp _ _
  have ht : ((T : Subgroup G).subgroupOf X).map q =
      ChapterB.Offenders.Six.sylowCarrier ⊓ q.range := by
    rw [hr,←map_map]
    exact hg
  have hA : alternatingGroup (Fin 6) ≤ q.range := by
    rw [hr,←conjugate_alternating g]
    exact map_mono hA₀
  have hker : q.ker = q₀.ker := MonoidHom.ker_comp_of_injective q₀ _ (MulAut.conj g).injective
  have hflag : move g W = canonicalPlane := by
    apply (invariant_unique_conjugate T0 le_rfl (1 : S) (move g W) ?_).2
      ((move_finrank _ _).trans hW) |>.trans (move_one canonicalPlane)
    intro a ha
    have ha0 : a ∈ T0 := by simpa using ha
    have hat : a ∈ ((T : Subgroup G).subgroupOf X).map q := by
      rw [ht,sylowCarrier_eq_flags]
      exact ⟨ha0.1,hA ha0.2⟩
    rw [←map_map] at hat
    obtain ⟨b,⟨x,hx,rfl⟩,rfl⟩ := hat
    change move ((MulAut.conj g) (q₀ x)) (move g W) = move g W
    rw [move_conjugate]
    congr 1
    apply Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.mem_stabilizer_iff_map W (q₀ x) |>.mp
    exact (show q₀ x ∈ flagStabilizer W ⊓ q₀.range from
      hi₀ ▸ mem_map_of_mem q₀ (show x ∈ B.subgroupOf X from ⟨x.property,hTW hx⟩)).1
  have hBimage : (B.subgroupOf X).map q = H2 ⊓ q.range := by
    rw [←map_map,hi₀,map_inf _ _ _ (MulAut.conj g).injective,
      ←flagStabilizer_move,hflag,flagStabilizer_plane,←hr]
  have hk : q.ker = pCore 2 X := hker.trans hk₀
  have hVH : V ≤ X := D.le_sylow.trans le_sup_right
  let : (V.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer hn
  let c := (subgroupOfEquivOfLe hVH).trans m.coordinate
  have hkc : q₀.ker = centralizer (V.subgroupOf X : Set X) :=
    ChapterB.Offenders.SixCorePoint.kernel_centralizer (V.subgroupOf X) q₀ c
      (fun x v => he₀ x (subgroupOfEquivOfLe hVH v))
  let e := m.coordinate.trans (LinearMap.GeneralLinearGroup.toLinearEquiv
    ((coreRepresentation (Fin 6)).asGroupHom g)).toAddEquiv.toMultiplicative
  have he (x : X) (v : V) :
      (e (V.normalizerMonoidHom ⟨x.val,hn x.property⟩ v)).toAdd =
        coreRepresentation (Fin 6) (q x) (e v).toAdd := by
    change coreRepresentation (Fin 6) g (m.coordinate
      (V.normalizerMonoidHom ⟨x.val,hn x.property⟩ v)).toAdd =
      coreRepresentation (Fin 6) (g*q₀ x*g⁻¹)
        (coreRepresentation (Fin 6) g (m.coordinate v).toAdd)
    rw [he₀,←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,
      inv_mul_cancel_right]
  refine ⟨q,e,he,hk,hker.trans hkc,hA,ht,?_⟩
  rw [←pCoreIn_subgroupOf 2 B X inf_le_left,
    map_pCoreIn_of_ker_isPGroup q (hk.symm ▸ pCore_isPGroup),hBimage,←planeCube_eq]
  have hnormal : q.range.Normal := by
    have hd : q.range.index ∣ 2 := by
      simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le hA
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · rw [index_eq_one.mp he]
      infer_instance
    · rw [Equiv.Perm.eq_alternatingGroup_of_index_eq_two he]
      infer_instance
  let := hnormal
  exact (pCoreIn_mono_of_normalizes inf_le_left
    ((le_inf H2.le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf)).trans_eq H2_core_eq_D

/-- The simultaneous marking, forgetting only its explicit vector coordinates. -/
theorem exists_original_plane_action_marking_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    let X := L ⊔ (T : Subgroup G)
    let B := X ⊓ normalizer (m.naturalPreimage W : Set G)
    ∃ q : X →* S,
      q.ker = pCore 2 X ∧
      q.ker = centralizer (V.subgroupOf X : Set X) ∧
      alternatingGroup (Fin 6) ≤ q.range ∧
      ((T : Subgroup G).subgroupOf X).map q =
        ChapterB.Offenders.Six.sylowCarrier ⊓ q.range ∧
      ((B.pCoreIn 2).subgroupOf X).map q ≤ ChapterB.Offenders.D 6 := by
  obtain ⟨q,e,he,hk,hc,hA,hT,hQ⟩ :=
    exists_original_plane_action_coordinates_at h structural D m eL W hW hTW
  exact ⟨q,hk,hc,hA,hT,hQ⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Inputs
public import Theory.GroupAction.FourthPowerFixed

/-!
# The distinguished plane in the cyclic Sylow-four branch

An order-four generator of the actual Sylow image has strictly fewer fixed
points than its square. The square is the common involution image, whose
fixed plane has order four. Transport through the literal conjugation map
identifies the generator's fixed subgroup with the Sylow-central seed,
which therefore has order two. The action on the source plane fixes that
seed and has nontrivial image of order two, giving the exact centralizer
index in the original Sylow subgroup.

Together with the existing S₃ and D₁₀ equal-plane calculation, this proves
both numerical alternatives after restricted-model recognition. Recognition
remains with qt-e-152-action-plane; no numerical premise is added to it.
Source: Aschbacher--Smith 15.2.14(2), printed p.1112,
combined manuscript of 1 March 2004, refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G]

private theorem fixed_image_ambient {M V B : Subgroup G}
    (hn : M ≤ normalizer (V : Set G)) (hBM : B ≤ M) :
    (FixedPoints.subgroup ((actor M V B hn).map
      (internalActionImage M V hn).subtype) V).map V.subtype =
      V ⊓ centralizer (B : Set G) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.property, fun b hb => ?_⟩
    have hbim : (actionHom M V hn).rangeRestrict ⟨b,hBM hb⟩ ∈ actor M V B hn :=
      mem_map_of_mem _ (show (⟨b,hBM hb⟩ : M) ∈ B.subgroupOf M from hb)
    have he := hw ⟨actionHom M V hn ⟨b,hBM hb⟩,
      mem_map_of_mem (internalActionImage M V hn).subtype hbim⟩
    have hv := congrArg (fun x : V => (x : G)) he
    change b * (w : G) * b⁻¹ = w at hv
    exact mul_inv_eq_iff_eq_mul.mp hv
  · rintro ⟨hv,hc⟩
    refine ⟨⟨v,hv⟩,?_,rfl⟩
    rintro ⟨_,a,⟨b,hb,rfl⟩,rfl⟩
    apply Subtype.ext
    change (b : G) * v * (b : G)⁻¹ = v
    rw [hc b hb,mul_inv_cancel_right]

variable [Finite G]

private theorem seed_eq_module_centralizer {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hfull : V = localModule T M) :
    centralInvolutions T = V ⊓ centralizer ((T : Subgroup G) : Set G) := by
  let := h.prepared.elementary
  apply le_antisymm
  · exact le_inf (by rw [hfull]; exact le_conjugateSpanBy _ _)
      (centralInvolutions_le_centralizer_sylow T)
  · intro v hv
    exact (mem_omegaOneCenterAmbient_iff _ v).mpr
      ⟨h.le_sylow hv.1,elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv.1,
        fun t ht => hv.2 t ht⟩

/-- A cyclic Sylow image of order four gives the order-two Sylow-central seed. -/
theorem Preceding.seed_card_of_sylow_four {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hP : Nat.card (actor M V (T : Subgroup G) h.prepared.normalized) = 4)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) : Nat.card (centralInvolutions T) = 2 := by
  let := h.prepared.elementary
  let D := internalActionImage M V h.prepared.normalized
  let P := actor M V (T : Subgroup G) h.prepared.normalized
  let A := actor M V B h.prepared.normalized
  let := sylow_image_cyclic h d.alternatives d.non_omega
  obtain ⟨a,ha⟩ := P.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  change zpowers a = actor M V (T : Subgroup G) h.prepared.normalized at ha
  have hac : orderOf a = 4 := by rw [←Nat.card_zpowers,ha]; exact hP
  have hsqc : Nat.card (zpowers (a^2)) = 2 := by
    rw [Nat.card_zpowers,orderOf_pow,hac]; decide
  have hsqa : zpowers (a^2) = A := order_two_images_eq h d.alternatives d.non_omega
    (by rw [←ha]; exact zpowers_le.mpr (pow_mem (mem_zpowers a) 2))
    (map_mono (comap_mono (d.actor_le_sylow hB))) hsqc
    (quadratic_fixed_eq_moved h _ (d.planes B hB).1 (d.planes B hB).2.1).1
  change zpowers (a^2) = actor M V B h.prepared.normalized at hsqa
  have hamap := congrArg (Subgroup.map D.subtype) ha
  have hsqmap := congrArg (Subgroup.map D.subtype) hsqa
  rw [MonoidHom.map_zpowers] at hamap
  rw [MonoidHom.map_zpowers,map_pow] at hsqmap
  change zpowers (a : MulAut V) = (actor M V (T : Subgroup G) h.prepared.normalized).map D.subtype at hamap
  change zpowers ((a : MulAut V)^2) = (actor M V B h.prepared.normalized).map D.subtype at hsqmap
  have hfa : (FixedPoints.subgroup (zpowers (a : MulAut V)) V).map V.subtype =
      centralInvolutions T := by
    rw [hamap,fixed_image_ambient h.prepared.normalized h.maximal.1.2,
      seed_eq_module_centralizer h d.full]
  have hfs : (FixedPoints.subgroup (zpowers ((a : MulAut V)^2)) V).map V.subtype =
      ⁅V,B⁆ := by
    rw [hsqmap,fixed_image_ambient h.prepared.normalized ((d.actor_le_sylow hB).trans h.maximal.1.2)]
    exact ambient_fixed_eq_commutator h ((d.actor_le_sylow hB).trans h.maximal.1.2)
      (d.planes B hB).1 (d.planes B hB).2.1
  have hlt := MulAut.fixed_card_lt_square_fixed_card_of_fourth_power_eq_one
    (a : MulAut V) (by
      have hh := congrArg Subtype.val (hac ▸ pow_orderOf_eq_one a)
      exact hh) (by
      intro he
      have he' : a = 1 := Subtype.ext he
      simp [he'] at hac)
  have hcfa := card_map_of_injective (K := FixedPoints.subgroup (zpowers (a : MulAut V)) V)
    V.subtype_injective
  have hcfs := card_map_of_injective
    (K := FixedPoints.subgroup (zpowers ((a : MulAut V)^2)) V) V.subtype_injective
  rw [hfa] at hcfa
  rw [hfs] at hcfs
  have hzlt : Nat.card (centralInvolutions T) < 4 :=
    hcfa.trans_lt (hlt.trans_eq (hcfs.symm.trans (d.planes B hB).2.2.2.1))
  have hge := (one_lt_card_iff_ne_bot (H := centralInvolutions T)).mpr
    (centralInvolutions_ne_bot_of_maximal_local T h.maximal.1)
  have hd : Nat.card (centralInvolutions T) ∣ 2^2 := by
    change Nat.card (centralInvolutions T) ∣ 4
    rw [←(d.planes B hB).2.2.2.1]
    exact card_dvd_of_le (seed_le_commutator h d.full (d.actor_le_sylow hB)
      (d.planes B hB).1 (d.planes B hB).2.1)
  obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases n
  · norm_num only [pow_zero] at he
    exact (Nat.ne_of_gt hge he).elim
  · exact he
  · norm_num only [Nat.reducePow] at he
    exact (ne_of_lt hzlt he).elim

/-- A source plane with a seed of order two has centralizer of index two in T. -/
theorem Preceding.plane_index_of_seed_two {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hZ : Nat.card (centralInvolutions T) = 2)
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    (planeCentralizer T ⁅V,B⁆).relIndex (T : Subgroup G) = 2 := by
  let := h.prepared.elementary
  let E := ⁅V,B⁆
  have hEV : E ≤ V := (d.planes B hB).2.2.1
  have hE : Nat.card E = 4 := (d.planes B hB).2.2.2.1
  have hTN : (T : Subgroup G) ≤ normalizer (E : Set G) := (d.planes B hB).2.2.2.2.2.1
  have hZE : centralInvolutions T ≤ E := seed_le_commutator h d.full
    (d.actor_le_sylow hB) (d.planes B hB).1 (d.planes B hB).2.1
  obtain ⟨z,hz,hzne⟩ := (centralInvolutions T).bot_or_exists_ne_one.resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T h.maximal.1)
  let f := actionHom (T : Subgroup G) E hTN
  have hfix : ∀ a ∈ f.range, a (⟨z,hZE hz⟩ : E) = ⟨z,hZE hz⟩ := by
    rintro a ⟨t,rfl⟩
    apply Subtype.ext
    change (t : G) * z * (t : G)⁻¹ = z
    rw [(centralInvolutions_le_centralizer_sylow T hz) t t.property,mul_inv_cancel_right]
  have hle := card_mulAut_subgroup_le_two_of_fixed_point hE (⟨z,hZE hz⟩ : E)
    (fun he => hzne (congrArg Subtype.val he)) f.range hfix
  have hne : f.range ≠ ⊥ := by
    intro he
    have hET : E ≤ centralizer ((T : Subgroup G) : Set G) := by
      intro v hv t ht
      have ht1 : f ⟨t,ht⟩ = 1 := (show f ⟨t,ht⟩ ∈ (⊥ : Subgroup (MulAut E)) from
        he ▸ (show f ⟨t,ht⟩ ∈ f.range from ⟨⟨t,ht⟩,rfl⟩))
      have hh := congrArg (fun a : MulAut E => (a ⟨v,hv⟩ : G)) ht1
      change t * v * t⁻¹ = v at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hEZ : E ≤ centralInvolutions T := by
      rw [seed_eq_module_centralizer h d.full]
      exact le_inf hEV hET
    have hh := card_le_of_le hEZ
    rw [hE,hZ] at hh
    omega
  have hc : Nat.card f.range = 2 := by
    have hgt := (one_lt_card_iff_ne_bot (H := f.range)).mpr hne
    omega
  have hk : f.ker = (planeCentralizer T E).subgroupOf (T : Subgroup G) := by
    rw [show f = actionHom (T : Subgroup G) E hTN from rfl,actionHom_ker]
    ext t
    exact ⟨fun ht => ⟨t.property,ht⟩,fun ht => ht.2⟩
  change ((planeCentralizer T E).subgroupOf (T : Subgroup G)).index = 2
  rw [←hk,index_ker,hc]

/-- The Sz(2) model gives exactly the source order and centralizer index. -/
theorem Preceding.suzuki_plane {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hm : Nonempty (internalActionImage M V h.prepared.normalized ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0))
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    Nat.card (centralInvolutions T) = 2 ∧
      (planeCentralizer T ⁅V,B⁆).relIndex (T : Subgroup G) = 2 := by
  let P : Sylow 2 (internalActionImage M V h.prepared.normalized) :=
    (T.subtype h.maximal.1.2).mapSurjective
      (actionHom M V h.prepared.normalized).rangeRestrict_surjective
  have hP : Nat.card (actor M V (T : Subgroup G) h.prepared.normalized) = 4 := by
    obtain ⟨e⟩ := hm
    change Nat.card P = 4
    rw [P.card_eq_multiplicity,Nat.card_congr e.toEquiv,
      BenderSuzuki.MatrixGroups.suzukiZero_card]
    decide +kernel
  have hz := d.seed_card_of_sylow_four hP hB
  exact ⟨hz,d.plane_index_of_seed_two hz hB⟩

/-- Both exact numerical alternatives of 15.2.14(2) in the cyclic rows. -/
theorem Preceding.plane_alternatives {T : Sylow 2 G} {M Mc V H B : Subgroup G}
    {h : ChosenSmallSource T M Mc V} (d : Preceding h H)
    (hr : RestrictedModels h) (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    centralInvolutions T ≤ ⁅V,B⁆ ∧
      ((planeCentralizer T ⁅V,B⁆ = (T : Subgroup G) ∧ centralInvolutions T = ⁅V,B⁆) ∨
        (Nonempty (internalActionImage M V h.prepared.normalized ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∧
          Nat.card (centralInvolutions T) = 2 ∧
          (planeCentralizer T ⁅V,B⁆).relIndex (T : Subgroup G) = 2)) := by
  let := h.prepared.elementary
  refine ⟨seed_le_commutator h d.full (d.actor_le_sylow hB)
    (d.planes B hB).1 (d.planes B hB).2.1,?_⟩
  rcases hr with ⟨_,hm⟩ | ⟨_,hm⟩
  · exact Or.inl (d.equal_plane (Or.inl hm) hB)
  · rcases hm with hm | hm
    · exact Or.inl (d.equal_plane (Or.inr hm) hB)
    · exact Or.inr ⟨hm,d.suzuki_plane hm hB⟩

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic

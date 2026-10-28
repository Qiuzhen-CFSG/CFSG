module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.PlaneCentralizers
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The plane family in a characteristic-two symplectic Sylow subgroup

The q+1 subgroups fixing the isotropic planes through the standard point
have order q², share the order-q transvection root, and pairwise generate
the elementary point radical. The finite-parameter members have literal
coordinates (b,u,lambda*b,0); the infinite member is the Sylow center.

For an arbitrary subgroup T, a finite-parameter plane together with an
element whose fourth coordinate is nonzero forces |T intersect Q1|≥2q².
The common commutator row first recovers the whole Sylow center; canceling
the first coordinate then supplies an element outside that center.
This is the arbitrary-radical step in the maximum-small-mover argument,
not an assumption that T is a full Sylow subgroup.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.4), printed p.915. The exact natural-action classification and
source choice of parabolic labels are separate consumers.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2]

/-- Two actual field parameters in a finite-parameter plane subgroup. -/
def planeHom (l : F) : (Multiplicative F × Multiplicative F) →* unipotent (F := F) where
  toFun x := element x.1.toAdd x.2.toAdd (l*x.1.toAdd) 0
  map_one' := by simpa using (element_zero (F := F))
  map_mul' x y := by
    simp only [element_mul, mul_zero, zero_mul, add_zero]
    apply (element_eq_iff _ _ _ _ _ _ _ _).mpr
    dsimp
    constructor
    · rfl
    constructor
    · ring_nf
      simp [CharTwo.two_eq_zero]
    constructor
    · ring
    · rfl

theorem planeHom_injective (l : F) : Function.Injective (planeHom l) := by
  intro x y h
  have hh := (element_eq_iff _ _ _ _ _ _ _ _).mp h
  exact Prod.ext (congrArg Multiplicative.ofAdd hh.1)
    (congrArg Multiplicative.ofAdd hh.2.1)

/-- The plane group with w=lambda*b and v=0. -/
def finitePlane (l : F) : Subgroup (unipotent (F := F)) := (planeHom l).range

theorem element_mem_finitePlane (l b u w v : F) :
    element b u w v ∈ finitePlane l ↔ v=0 ∧ w=l*b := by
  constructor
  · rintro ⟨⟨c,z⟩,h⟩
    have hh := (element_eq_iff _ _ _ _ _ _ _ _).mp h
    exact ⟨hh.2.2.2.symm, by rw [← hh.1]; exact hh.2.2.1.symm⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨(Multiplicative.ofAdd b,Multiplicative.ofAdd u),rfl⟩

/-- The transvection root in the first central coordinate. -/
def rootHom : Multiplicative F →* unipotent (F := F) where
  toFun x := theta x.toAdd 0
  map_one' := element_zero
  map_mul' x y := by simpa using (theta_add x.toAdd 0 y.toAdd 0).symm

theorem rootHom_injective : Function.Injective (rootHom (F := F)) := by
  intro x y h
  exact congrArg Multiplicative.ofAdd ((element_eq_iff _ _ _ _ _ _ _ _).mp h).2.1

/-- The common order-q root of all plane groups. -/
def root : Subgroup (unipotent (F := F)) := rootHom.range

theorem element_mem_root (b u w v : F) :
    element b u w v ∈ root ↔ b=0 ∧ w=0 ∧ v=0 := by
  constructor
  · rintro ⟨z,h⟩
    have hh := (element_eq_iff _ _ _ _ _ _ _ _).mp h
    exact ⟨hh.1.symm,hh.2.2.1.symm,hh.2.2.2.symm⟩
  · rintro ⟨rfl,rfl,rfl⟩
    exact ⟨Multiplicative.ofAdd u,rfl⟩

variable [Finite F]

/-- The complete projective-line family; none denotes the Sylow center. -/
def plane : Option F → Subgroup (unipotent (F := F))
  | none => center (unipotent (F := F))
  | some l => finitePlane l

omit [Finite F] in
theorem card_finitePlane (l : F) : Nat.card (finitePlane l) = Nat.card F ^ 2 := by
  change Nat.card (planeHom l).range = _
  rw [← Nat.card_congr (MonoidHom.ofInjective (planeHom_injective l)).toEquiv]
  simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F), pow_two]

omit [Finite F] in
theorem card_root : Nat.card (root (F := F)) = Nat.card F :=
  (Nat.card_congr (MonoidHom.ofInjective rootHom_injective).toEquiv).symm

theorem card_center : Nat.card (center (unipotent (F := F))) = Nat.card F ^ 2 := by
  rw [← Nat.card_congr (centerEquiv (F := F)).toEquiv]
  simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F), pow_two]

theorem card_plane (s : Option F) : Nat.card (plane s) = Nat.card F ^ 2 := by
  cases s with
  | none => exact card_center
  | some l => exact card_finitePlane l

theorem plane_le_wing (s : Option F) : plane s ≤ wing false := by
  intro x hx
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  rw [element_mem_wing]
  cases s with
  | none => exact ((mem_center_iff_coordinates _ _ _ _).mp hx).2
  | some l => exact ((element_mem_finitePlane _ _ _ _ _).mp hx).1

theorem finitePlane_inf_center (l : F) :
    finitePlane l ⊓ center (unipotent (F := F)) = root := by
  ext x
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  simp only [mem_inf, element_mem_finitePlane,mem_center_iff_coordinates,element_mem_root]
  constructor
  · rintro ⟨⟨hv,hw⟩,hb,_⟩
    exact ⟨hb,by simp [hb] at hw; exact hw,hv⟩
  · rintro ⟨rfl,rfl,rfl⟩
    simp

theorem finitePlane_inf_finitePlane {l m : F} (hne : l ≠ m) :
    finitePlane l ⊓ finitePlane m = root := by
  ext x
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  simp only [mem_inf,element_mem_finitePlane,element_mem_root]
  constructor
  · rintro ⟨⟨hv,hl⟩,_,hm⟩
    have hb : b=0 := by
      have hh : (l-m)*b=0 := by rw [sub_mul,← hl,← hm,sub_self]
      exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hne)
    exact ⟨hb,by simp [hb] at hl; exact hl,hv⟩
  · rintro ⟨rfl,rfl,rfl⟩
    simp

theorem plane_inf {s t : Option F} (hne : s ≠ t) :
    plane s ⊓ plane t = root := by
  cases s with
  | none =>
    cases t with
    | none => exact False.elim (hne rfl)
    | some m => exact (inf_comm _ _).trans (finitePlane_inf_center m)
  | some l =>
    cases t with
    | none => exact finitePlane_inf_center l
    | some m => exact finitePlane_inf_finitePlane (fun hh => hne (congrArg some hh))

/-- Any two different members generate the full point radical. -/
theorem plane_sup {s t : Option F} (hne : s ≠ t) :
    plane s ⊔ plane t = wing false := by
  let := wing_elementary (F := F) false
  have hn : plane t ≤ normalizer (plane s : Set (unipotent (F := F))) :=
    (plane_le_wing t).trans (((wing false).le_centralizer.trans
      (centralizer_le (plane_le_wing s))).trans (Subgroup.centralizer_le_normalizer _))
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (plane s) (plane t) hn
  rw [card_plane,card_plane,plane_inf hne,card_root] at hc
  have hcard : Nat.card (plane s ⊔ plane t : Subgroup (unipotent (F := F))) =
      Nat.card F ^ 3 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := F))
    rw [← hc]
    ring
  exact eq_of_le_of_card_ge (sup_le (plane_le_wing s) (plane_le_wing t))
    (by rw [hcard,card_wing])

theorem plane_injective : Function.Injective (plane (F := F)) := by
  intro s t he
  by_contra hne
  have hh := plane_inf hne
  rw [he,inf_idem] at hh
  have hcard : Nat.card F ^ 2 = Nat.card F := by
    rw [← card_plane t, hh,card_root]
  have hq := Finite.one_lt_card (α := F)
  nlinarith

theorem plane_family_card (hF : Nat.card F = 4) :
    Nat.card (Set.range (plane (F := F))) = 5 := by
  let : Fintype F := Fintype.ofFinite F
  rw [Nat.card_range_of_injective plane_injective]
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option] using congrArg (fun n => n+1) hF

omit [Finite F] in
/-- The common commutator row, independent of the plane parameter. -/
theorem element_plane_commutator (b u w v l c : F) :
    ⁅element b u w v,element c 0 (l*c) 0⁆ = theta (v*c^2) (v*c) := by
  have hh : element b u w v * element c 0 (l*c) 0 =
      theta (v*c^2) (v*c) * (element c 0 (l*c) 0 * element b u w v) := by
    simp only [theta,element_mul]
    apply (element_eq_iff _ _ _ _ _ _ _ _).mpr
    constructor
    · simp [add_comm]
    constructor
    · ring_nf
      simp [CharTwo.two_eq_zero]
    constructor
    · simp [add_comm,add_left_comm]
    · simp
  rw [commutatorElement_def,hh]
  group

theorem root_le_finitePlane (l : F) : root ≤ finitePlane l := by
  intro x hx
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  obtain ⟨rfl,rfl,rfl⟩ := (element_mem_root _ _ _ _).mp hx
  exact (element_mem_finitePlane _ _ _ _ _).mpr ⟨rfl,by simp⟩

/-- A plane and an element outside the point wing recover the whole center. -/
theorem center_le_of_plane_and_mixed (T : Subgroup (unipotent (F := F)))
    (l : F) (hP : finitePlane l ≤ T) {b u w v : F}
    (hg : element b u w v ∈ T) (hv : v ≠ 0) : center (unipotent (F := F)) ≤ T := by
  intro z hz
  obtain ⟨⟨a,r,s,d⟩,rfl⟩ := element_surjective z
  obtain ⟨rfl,rfl⟩ := (mem_center_iff_coordinates _ _ _ _).mp hz
  let c := s / v
  have hvc : v*c = s := by dsimp [c]; field_simp
  have hx : element c 0 (l*c) 0 ∈ T :=
    hP ((element_mem_finitePlane _ _ _ _ _).mpr ⟨rfl,rfl⟩)
  have hc : theta (v*c^2) s ∈ T := by
    rw [← hvc,← element_plane_commutator b u w v l c]
    exact T.mul_mem (T.mul_mem (T.mul_mem hg hx) (T.inv_mem hg)) (T.inv_mem hx)
  have hr : theta (r+v*c^2) 0 ∈ T := by
    apply (root_le_finitePlane l).trans hP
    exact (element_mem_root _ _ _ _).mpr ⟨rfl,rfl,rfl⟩
  have hm := T.mul_mem hr hc
  rw [theta_add] at hm
  simpa [add_assoc,CharTwo.add_self_eq_zero,theta] using hm

/-- The recovered center has a proper overgroup inside the plane wing. -/
theorem mixed_plane_intersection_bound (T : Subgroup (unipotent (F := F)))
    (l : F) (hP : finitePlane l ≤ T) {b u w v : F}
    (hg : element b u w v ∈ T) (hv : v ≠ 0) :
    2 * Nat.card F ^ 2 ≤ Nat.card (T ⊓ wing true : Subgroup (unipotent (F := F))) := by
  let A := T ⊓ wing (F := F) true
  have hZ : center (unipotent (F := F)) ≤ A :=
    le_inf (center_le_of_plane_and_mixed T l hP hg hv)
      (center_le_wings.trans inf_le_right)
  have hn : ¬ A ≤ center (unipotent (F := F)) := by
    intro hh
    have hx : element b 0 (l*b) 0 ∈ T :=
      hP ((element_mem_finitePlane _ _ _ _ _).mpr ⟨rfl,rfl⟩)
    have hy : element b u w v * element b 0 (l*b) 0 ∈ A := by
      apply Subgroup.mem_inf.mpr
      refine ⟨T.mul_mem hg hx,?_⟩
      rw [element_mul,element_mem_wing]
      exact CharTwo.add_self_eq_zero _
    have hz := hh hy
    rw [element_mul,mem_center_iff_coordinates] at hz
    exact hv (by simpa using hz.2)
  have hlt : Nat.card (center (unipotent (F := F))) < Nat.card A := by
    have hle := card_le_of_le hZ
    apply lt_of_le_of_ne hle
    intro he
    exact hn (eq_of_le_of_card_ge hZ he.ge).ge
  obtain ⟨k,hk⟩ := card_dvd_of_le hZ
  have hpos := Nat.card_pos (α := center (unipotent (F := F)))
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k=0 ∨ k=1 := by omega
    rcases this with rfl|rfl <;> simp_all
  rw [card_center] at hk hlt hpos
  change 2 * Nat.card F ^ 2 ≤ Nat.card A
  rw [hk]
  nlinarith

/-- The order-four field specialization used by the small-mover consumer. -/
theorem mixed_plane_intersection_bound_four (hF : Nat.card F = 4)
    (T : Subgroup (unipotent (F := F))) (l : F) (hP : finitePlane l ≤ T)
    {b u w v : F} (hg : element b u w v ∈ T) (hv : v ≠ 0) :
    32 ≤ Nat.card (T ⊓ wing true : Subgroup (unipotent (F := F))) := by
  simpa [hF] using mixed_plane_intersection_bound T l hP hg hv

/-- The maximum-mover cardinal bound excludes every element outside Q2. -/
theorem le_point_wing_of_plane_and_card_bound (T : Subgroup (unipotent (F := F)))
    (l : F) (hP : finitePlane l ≤ T)
    (hcard : Nat.card (T ⊓ wing true : Subgroup (unipotent (F := F))) ≤ Nat.card F ^ 2) :
    T ≤ wing false := by
  intro g hg
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
  rw [element_mem_wing]
  change v=0
  by_contra hv
  have hb := mixed_plane_intersection_bound T l hP hg hv
  have hpos := Nat.card_pos (α := F)
  nlinarith

/-- The literal arbitrary-T consumer of pairwise plane generation. -/
theorem eq_point_wing_of_two_planes (T : Subgroup (unipotent (F := F)))
    (hT : T ≤ wing false) {s t : Option F} (hne : s ≠ t)
    (hs : plane s ≤ T) (ht : plane t ≤ T) : T=wing false := by
  apply le_antisymm hT
  rw [← plane_sup hne]
  exact sup_le hs ht

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers

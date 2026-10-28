module

public import Theory.AlgebraicGroup.Morphism.ClosedImage

universe u

/-! Pointwise products of closed subgroups.  Besides identifying the product
sets as morphism ranges, this module upgrades dense products to open products
by translating a nonempty open subset of the range. -/

namespace Theory.AlgebraicGroup

open scoped Pointwise

variable {k : Type u} [Field k]

/-- The pointwise product of two closed subgroups is the range of a regular
multiplication morphism from the product of their carrier varieties. -/
public theorem exists_closedSubgroup_productMorphism_range_eq_pointwise_mul
    {G : Variety k} [AlgebraicGroup G] (B C : ClosedSubgroup G) :
    ∃ m : Variety.Morphism
      (Variety.prod B.carrierVariety C.carrierVariety) G,
      Set.range m.toFun =
        (B.toSubgroup : Set (Variety.Point G)) *
          (C.toSubgroup : Set (Variety.Point G)) := by
  let : AlgebraicGroup B.carrierVariety := B.carrierAlgebraicGroup
  let : AlgebraicGroup C.carrierVariety := C.carrierAlgebraicGroup
  let : AlgebraicGroup (Variety.prod B.carrierVariety C.carrierVariety) :=
    AlgebraicGroup.prod B.carrierVariety C.carrierVariety
  let left := B.inclusion.comp
    (AlgebraicGroup.Morphism.fst B.carrierVariety C.carrierVariety)
  let right := C.inclusion.comp
    (AlgebraicGroup.Morphism.snd B.carrierVariety C.carrierVariety)
  let pair := AlgebraicGroup.Morphism.prod left right
  let m := (AlgebraicGroup.mulMorphism G).comp pair.toVariety
  have hm (z : Variety.Point
      (Variety.prod B.carrierVariety C.carrierVariety)) :
      m.toFun z =
        B.inclusion.onPoints
          (Variety.prodPointEquiv B.carrierVariety C.carrierVariety z).1 *
        C.inclusion.onPoints
          (Variety.prodPointEquiv B.carrierVariety C.carrierVariety z).2 := by
    rfl
  refine ⟨m, ?_⟩
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    rw [hm]
    apply Set.mem_mul.mpr
    exact ⟨B.inclusion.onPoints
        (Variety.prodPointEquiv B.carrierVariety C.carrierVariety z).1,
      (B.pointEquiv
        (Variety.prodPointEquiv B.carrierVariety C.carrierVariety z).1).property,
      C.inclusion.onPoints
        (Variety.prodPointEquiv B.carrierVariety C.carrierVariety z).2,
      (C.pointEquiv
        (Variety.prodPointEquiv B.carrierVariety C.carrierVariety z).2).property,
      rfl⟩
  · intro hg
    obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_mul.mp hg
    let b' : Variety.Point B.carrierVariety := B.pointEquiv.symm ⟨b, hb⟩
    let c' : Variety.Point C.carrierVariety := C.pointEquiv.symm ⟨c, hc⟩
    let z :=
      (Variety.prodPointEquiv B.carrierVariety C.carrierVariety).symm (b', c')
    refine ⟨z, ?_⟩
    rw [hm, Equiv.apply_symm_apply]
    have hb' : B.inclusion.onPoints b' = b := by
      change (B.pointEquiv b').val = b
      dsimp [b']
      rw [B.pointEquiv.apply_symm_apply]
    have hc' : C.inclusion.onPoints c' = c := by
      change (C.pointEquiv c').val = c
      dsimp [c']
      rw [C.pointEquiv.apply_symm_apply]
    rw [hb', hc']

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A dense pointwise product of closed subgroups is open.

The product is the range of the multiplication morphism.  Constructibility
and density give a nonempty open subset of that range; left and right
translations of this subset provide an open neighborhood inside the product
at every product point. -/
public theorem closedSubgroup_product_isOpen_of_dense
    {G : Variety k} [AlgebraicGroup G] [Nonempty (Variety.Point G)]
    [PreirreducibleSpace (Variety.Point G)]
    (B C : ClosedSubgroup G)
    (hdense : Dense
      ((B.toSubgroup : Set (Variety.Point G)) *
        (C.toSubgroup : Set (Variety.Point G)))) :
    IsOpen
      ((B.toSubgroup : Set (Variety.Point G)) *
        (C.toSubgroup : Set (Variety.Point G))) := by
  obtain ⟨m, hm⟩ := exists_closedSubgroup_productMorphism_range_eq_pointwise_mul B C
  have hmDense : Dense (Set.range m.toFun) := by
    rw [hm]
    exact hdense
  obtain ⟨U, hUopen, hUne, hUsub⟩ :=
    m.exists_nonempty_open_subset_range_of_dense hmDense
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨u, huU⟩ := hUne
  rw [hm] at hUsub
  obtain ⟨b₀, hb₀, c₀, hc₀, hu⟩ := Set.mem_mul.mp (hUsub huU)
  have hu' : u = b₀ * c₀ := hu.symm
  let V : Set (Variety.Point G) :=
    (Homeomorph.mulLeft (b * b₀⁻¹)) ''
      ((Homeomorph.mulRight (c₀⁻¹ * c)) '' U)
  have hVopen : IsOpen V := by
    apply (Homeomorph.mulLeft (b * b₀⁻¹)).isOpenMap
    apply (Homeomorph.mulRight (c₀⁻¹ * c)).isOpenMap
    exact hUopen
  have hxV : b * c ∈ V := by
    refine ⟨u * (c₀⁻¹ * c), ⟨u, huU, rfl⟩, ?_⟩
    simp [hu', mul_assoc]
  have hVsub : V ⊆
      ((B.toSubgroup : Set (Variety.Point G)) *
        (C.toSubgroup : Set (Variety.Point G))) := by
    rintro z ⟨y, ⟨w, hwU, rfl⟩, rfl⟩
    obtain ⟨b₁, hb₁, c₁, hc₁, hw⟩ := Set.mem_mul.mp (hUsub hwU)
    refine Set.mem_mul.mpr ⟨b * b₀⁻¹ * b₁, ?_, c₁ * c₀⁻¹ * c, ?_, ?_⟩
    · exact B.toSubgroup.mul_mem
        (B.toSubgroup.mul_mem hb (B.toSubgroup.inv_mem hb₀)) hb₁
    · simpa [mul_assoc] using C.toSubgroup.mul_mem hc₁
        (C.toSubgroup.mul_mem (C.toSubgroup.inv_mem hc₀) hc)
    · simp [Homeomorph.mulLeft, Homeomorph.mulRight, mul_assoc, ← hw]
  exact Filter.mem_of_superset (hVopen.mem_nhds hxV) hVsub

end

/-- A subgroup containing two closed subgroups is top when their pointwise
product is dense in the connected ambient algebraic group. -/
public theorem closedSubgroup_product_dense_contained_subgroup_eq_top
    {G : Variety k} [AlgebraicGroup G] [IsAlgClosed k]
    [Nonempty (Variety.Point G)] [PreirreducibleSpace (Variety.Point G)]
    (H : Subgroup (Variety.Point G)) (B C : ClosedSubgroup G)
    (hconn : _root_.IsConnected (Set.univ : Set (Variety.Point G)))
    (hB : B.toSubgroup ≤ H) (hC : C.toSubgroup ≤ H)
    (hdense : Dense ((B.toSubgroup : Set (Variety.Point G)) *
      (C.toSubgroup : Set (Variety.Point G)))) :
    H = ⊤ := by
  obtain ⟨m, hm⟩ :=
    exists_closedSubgroup_productMorphism_range_eq_pointwise_mul B C
  have hmDense : Dense (Set.range m.toFun) := by
    rw [hm]
    exact hdense
  obtain ⟨U, hUopen, hUne, hUsub⟩ :=
    m.exists_nonempty_open_subset_range_of_dense hmDense
  rw [hm] at hUsub
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_mul.mp (hUsub hxU)
  let V : Set (Variety.Point G) :=
    (Homeomorph.mulLeft b⁻¹) '' ((Homeomorph.mulRight c⁻¹) '' U)
  have hVopen : IsOpen V := by
    apply (Homeomorph.mulLeft b⁻¹).isOpenMap
    apply (Homeomorph.mulRight c⁻¹).isOpenMap
    exact hUopen
  have hVone : (1 : Variety.Point G) ∈ V := by
    refine ⟨b, ?_, ?_⟩
    · exact ⟨b * c, hxU, by simp⟩
    · simp
  have hVsub : V ⊆ (H : Set (Variety.Point G)) := by
    rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨b', hb', c', hc', rfl⟩ := Set.mem_mul.mp (hUsub hx)
    have hleft : b⁻¹ * b' ∈ H :=
      hB (B.toSubgroup.mul_mem (B.toSubgroup.inv_mem hb) hb')
    have hright : c' * c⁻¹ ∈ H :=
      hC (C.toSubgroup.mul_mem hc' (C.toSubgroup.inv_mem hc))
    simpa [Homeomorph.mulLeft, Homeomorph.mulRight, mul_assoc] using
      H.mul_mem hleft hright
  have hHopen : IsOpen (H : Set (Variety.Point G)) :=
    Subgroup.isOpen_of_mem_nhds H
      (Filter.mem_of_superset (hVopen.mem_nhds hVone) hVsub)
  have hHclosed : IsClosed (H : Set (Variety.Point G)) :=
    Subgroup.isClosed_of_isOpen H hHopen
  have hHuniv : (H : Set (Variety.Point G)) = Set.univ := by
    by_contra hne
    rcases hconn with ⟨_, hpreconn⟩
    have hHne : ((Set.univ : Set (Variety.Point G)) ∩ H).Nonempty :=
      ⟨1, Set.mem_univ 1, H.one_mem⟩
    have hHcne :
        ((Set.univ : Set (Variety.Point G)) ∩
          (H : Set (Variety.Point G))ᶜ).Nonempty := by
      obtain ⟨x, hx⟩ := Set.nonempty_compl.mpr hne
      exact ⟨x, Set.mem_univ x, hx⟩
    have hinter := hpreconn (H : Set (Variety.Point G))
      (H : Set (Variety.Point G))ᶜ hHopen hHclosed.isOpen_compl
      (by
        intro x _
        by_cases hx : x ∈ H
        · exact Or.inl hx
        · exact Or.inr hx)
      hHne hHcne
    obtain ⟨x, _, hxH, hxHc⟩ := hinter
    exact hxHc hxH
  apply SetLike.ext'
  simpa using hHuniv

end Theory.AlgebraicGroup

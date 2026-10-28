module

public import Theory.AlgebraicGroup.Solvable.MaximalTorusConjugacy
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.Transport

/-!
# Separating normalizer cosets by conjugacy of tori

For a solvable closed subgroup `B` containing an ambient maximal torus `T`,
the equality `B ∩ N(T) = T` implies separation of its double cosets through
`N(T)`. Given `n = x m y` with `x,y ∈ B`, the two maximal tori `T` and
`x T x⁻¹` lie in `B ∩ n B n⁻¹`. Conjugating them inside this intersection
produces two elements of `B ∩ N(T)`, whose torus membership gives `n⁻¹m ∈ T`.

The intersection need not be connected: its maximal tori lie in its identity
component, where the proved solvable torus-conjugacy theorem applies. The
closed-subgroup restrictions and the return to ambient conjugation are proved
explicitly. No Bruhat coverage or Tits-system assertion enters this argument.

Source: the torus-conjugacy proof of Bruhat cell separation, GLS3 1.11.3--5
and Steinberg 6.3(a); `refs/KGroup/GLS3/Chapter1.tex` and
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.ConnectedCentralizer.Bruhat.Splitting.CellSeparation
open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : Variety k} [AlgebraicGroup G]

private theorem inside_maximal (H T : ClosedSubgroup G)
    (hT : IsMaximalTorus T) (hTH : T ≤ H) :
    IsMaximalTorus (H.inclusion.closedSubgroupPreimage T) := by
  let A := H.inclusion.closedSubgroupPreimage T
  let f := T.inclusion.codRestrictClosedSubgroup H
    (fun x => hTH (T.pointEquiv x).property)
  have hf (x : Variety.Point T.carrierVariety) :
      H.inclusion.onPoints (f.onPoints x) = T.inclusion.onPoints x :=
    T.inclusion.codRestrictClosedSubgroup_inclusion_apply H _ x
  have himage : f.imageClosedSubgroup = A := by
    apply SetLike.ext
    intro x
    change (∃ y, f.onPoints y = x) ↔ H.inclusion.onPoints x ∈ T
    constructor
    · rintro ⟨y, rfl⟩
      rw [hf]
      exact (T.pointEquiv y).property
    · intro hx
      refine ⟨T.pointEquiv.symm ⟨H.inclusion.onPoints x, hx⟩, H.inclusion_injective ?_⟩
      rw [hf]
      exact congrArg Subtype.val (T.pointEquiv.apply_symm_apply _)
  refine ⟨?_, ?_⟩
  · change IsSubtorus A
    rw [← himage]
    exact morphism_image_isTorus f hT.1
  · intro V hV hAV
    let : AlgebraicGroup V.carrierVariety := V.carrierAlgebraicGroup
    let j : Morphism V.carrierVariety G := H.inclusion.comp V.inclusion
    have hTj : T ≤ j.imageClosedSubgroup := by
      intro x hx
      let y := H.pointEquiv.symm ⟨x, hTH hx⟩
      have hy : H.inclusion.onPoints y = x :=
        congrArg Subtype.val (H.pointEquiv.apply_symm_apply _)
      have hyA : y ∈ A := by change H.inclusion.onPoints y ∈ T; rwa [hy]
      refine ⟨V.pointEquiv.symm ⟨y, hAV hyA⟩, ?_⟩
      change H.inclusion.onPoints (V.inclusion.onPoints _) = x
      rw [show V.inclusion.onPoints (V.pointEquiv.symm ⟨y, hAV hyA⟩) = y from
        congrArg Subtype.val (V.pointEquiv.apply_symm_apply _)]
      exact hy
    have hj : j.imageClosedSubgroup = T :=
      hT.2 _ (morphism_image_isTorus j hV) hTj
    apply SetLike.ext
    intro x
    constructor
    · intro hx
      change H.inclusion.onPoints x ∈ T
      rw [← hj]
      refine ⟨V.pointEquiv.symm ⟨x, hx⟩, ?_⟩
      change H.inclusion.onPoints (V.inclusion.onPoints _) = H.inclusion.onPoints x
      exact congrArg H.inclusion.onPoints
        (congrArg Subtype.val (V.pointEquiv.apply_symm_apply _))
    · exact fun hx => hAV hx

omit [IsAlgClosed k] in
private theorem carrier_connected (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- Ambient maximal tori contained in a solvable closed subgroup are conjugate
by an element of that subgroup, even if it is disconnected. -/
theorem tori_conjugate_in_solvable (H T₁ T₂ : ClosedSubgroup G)
    (hH : Group.IsSolvable (Variety.Point H.carrierVariety))
    (hT₁ : IsMaximalTorus T₁) (hT₂ : IsMaximalTorus T₂)
    (h₁ : T₁ ≤ H) (h₂ : T₂ ≤ H) :
    ∃ g : Variety.Point G, g ∈ H ∧ T₂ = T₁.conjugate g := by
  let J := H.identityComponentAmbient
  have hjH : J ≤ H := H.identityComponentAmbient_le
  have h₁J : T₁ ≤ J := maximalTorus_le_identityComponentAmbient_of_le T₁ H hT₁ h₁
  have h₂J : T₂ ≤ J := maximalTorus_le_identityComponentAmbient_of_le T₂ H hT₂ h₂
  let f := J.inclusion.codRestrictClosedSubgroup H
    (fun x => hjH (J.pointEquiv x).property)
  have hf : Function.Injective f.onPoints := by
    intro x y hxy
    apply J.inclusion_injective
    have := congrArg H.inclusion.onPoints hxy
    simpa only [f, Morphism.codRestrictClosedSubgroup_inclusion_apply] using this
  have hJ : Group.IsSolvable (Variety.Point J.carrierVariety) := by
    let := hH
    exact Group.isSolvable_of_isSolvable_injective hf
  obtain ⟨g, hg⟩ := maximalTori_conjugate_of_solvable_connected hJ
    (carrier_connected J H.identityComponentAmbient_isConnected)
    (inside_maximal J T₁ hT₁ h₁J) (inside_maximal J T₂ hT₂ h₂J)
  refine ⟨J.inclusion.onPoints g, hjH (J.pointEquiv g).property, ?_⟩
  apply SetLike.ext
  intro x
  constructor
  · intro hx
    let y := J.pointEquiv.symm ⟨x, h₂J hx⟩
    have hy : J.inclusion.onPoints y = x :=
      congrArg Subtype.val (J.pointEquiv.apply_symm_apply _)
    have hyT : y ∈ J.inclusion.closedSubgroupPreimage T₂ := by
      change J.inclusion.onPoints y ∈ T₂
      rwa [hy]
    rw [hg, ClosedSubgroup.mem_conjugate_iff] at hyT
    rw [ClosedSubgroup.mem_conjugate_iff]
    change J.inclusion.onPoints (g⁻¹ * y * g) ∈ T₁ at hyT
    change J.inclusion.onPoints (g⁻¹ * y * g) ∈ T₁.toSubgroup at hyT
    simpa only [map_mul, map_inv, hy] using hyT
  · intro hx
    have hxJ : x ∈ J := by
      have hh := (T₁.mem_conjugate_iff (J.inclusion.onPoints g) x).mp hx
      have hhJ := h₁J hh
      have := J.mul_mem (J.mul_mem (J.pointEquiv g).property hhJ)
        (J.inv_mem (J.pointEquiv g).property)
      change J.inclusion.onPoints g * ((J.inclusion.onPoints g)⁻¹ * x *
        J.inclusion.onPoints g) * (J.inclusion.onPoints g)⁻¹ ∈ J at this
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using this
    let y := J.pointEquiv.symm ⟨x, hxJ⟩
    have hy : J.inclusion.onPoints y = x :=
      congrArg Subtype.val (J.pointEquiv.apply_symm_apply _)
    have hyT : y ∈ (J.inclusion.closedSubgroupPreimage T₁).conjugate g := by
      rw [ClosedSubgroup.mem_conjugate_iff]
      change J.inclusion.onPoints (g⁻¹ * y * g) ∈ T₁.toSubgroup
      have hxT : (J.inclusion.onPoints g)⁻¹ * x * J.inclusion.onPoints g ∈ T₁.toSubgroup :=
        (T₁.mem_conjugate_iff (J.inclusion.onPoints g) x).mp hx
      simpa only [map_mul, map_inv, hy] using hxT
    rw [← hg] at hyT
    change J.inclusion.onPoints y ∈ T₂ at hyT
    rwa [hy] at hyT

/-- Separation from solvable torus conjugacy and the normalizer intersection. -/
theorem coset_separation (B T : ClosedSubgroup G)
    (hB : Group.IsSolvable (Variety.Point B.carrierVariety))
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hBN : B.toSubgroup ⊓ T.normalizer.toSubgroup = T.toSubgroup)
    (n m : T.normalizer.toSubgroup) (b c d e : Variety.Point G)
    (hb : b ∈ B.toSubgroup) (hc : c ∈ B.toSubgroup)
    (hd : d ∈ B.toSubgroup) (he : e ∈ B.toSubgroup)
    (heq : b * (n : Variety.Point G) * c = d * (m : Variety.Point G) * e) :
    (n : Variety.Point G)⁻¹ * (m : Variety.Point G) ∈ T.toSubgroup := by
  let x := b⁻¹ * d
  let y := e * c⁻¹
  have hx : x ∈ B.toSubgroup := B.mul_mem (B.inv_mem hb) hd
  have hy : y ∈ B.toSubgroup := B.mul_mem he (B.inv_mem hc)
  have hfactor : (n : Variety.Point G) = x * (m : Variety.Point G) * y := by
    have h := congrArg (fun z => b⁻¹ * z * c⁻¹) heq
    simpa only [x, y, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using h
  let H := B.inter (B.conjugate (n : Variety.Point G))
  have hHB : H ≤ B := fun _ h => h.1
  have hTH : T ≤ H := by
    have hconj := BorelIntersectionGeometry.conjugate_le hTB (n : Variety.Point G)
    rw [ClosedSubgroup.conjugate_eq_self_of_mem_normalizer _ n.property] at hconj
    exact fun z hz => ⟨hTB hz, hconj hz⟩
  obtain ⟨hxT, hxB, hxconj⟩ :=
    BorelIntersectionGeometry.common_maximalTorus_of_normal_form B T hT hTB x m hx m.property
  have hxTH : T.conjugate x ≤ H := by
    have hBn : B.conjugate (n : Variety.Point G) = B.conjugate (x * (m : Variety.Point G)) := by
      rw [hfactor]
      exact BorelIntersectionGeometry.conjugate_of_double_coset B x m y hy
    exact fun z hz => ⟨hxB hz, by rw [hBn]; exact hxconj hz⟩
  let f := H.inclusion.codRestrictClosedSubgroup B
    (fun z => hHB (H.pointEquiv z).property)
  have hf : Function.Injective f.onPoints := by
    intro z w hzw
    apply H.inclusion_injective
    have := congrArg B.inclusion.onPoints hzw
    simpa only [f, Morphism.codRestrictClosedSubgroup_inclusion_apply] using this
  have hH : Group.IsSolvable (Variety.Point H.carrierVariety) := by
    let := hB
    exact Group.isSolvable_of_isSolvable_injective hf
  obtain ⟨h, hh, hconj⟩ := tori_conjugate_in_solvable H (T.conjugate x) T hH hxT hT hxTH hTH
  rw [ClosedSubgroup.conjugate_conjugate] at hconj
  let r := h * x
  have hrN : r ∈ T.normalizer.toSubgroup := by
    change r ∈ Subgroup.normalizer (T.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hmem : r * z * r⁻¹ ∈ T.conjugate r ↔ r * z * r⁻¹ ∈ T := by rw [← hconj]
    rw [ClosedSubgroup.mem_conjugate_iff] at hmem
    change (r⁻¹ * (r * z * r⁻¹) * r ∈ T.toSubgroup) ↔
      r * z * r⁻¹ ∈ T.toSubgroup at hmem
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using hmem
  have hr : r ∈ T.toSubgroup := by
    rw [← hBN]
    exact ⟨B.mul_mem hh.1 hx, hrN⟩
  let q := (n : Variety.Point G)⁻¹ * r * (m : Variety.Point G)
  have hqN : q ∈ T.normalizer.toSubgroup :=
    T.normalizer.mul_mem (T.normalizer.mul_mem
      (T.normalizer.inv_mem n.property) hrN) m.property
  have hqB : q ∈ B.toSubgroup := by
    have hhB : (n : Variety.Point G)⁻¹ * h * (n : Variety.Point G) ∈ B.toSubgroup :=
      (B.mem_conjugate_iff _ h).mp hh.2
    have hq : q = ((n : Variety.Point G)⁻¹ * h * (n : Variety.Point G)) * y⁻¹ := by
      calc
        q = (n : Variety.Point G)⁻¹ * h * (x * (m : Variety.Point G) * y) * y⁻¹ := by
          dsimp [q, r]
          group
        _ = _ := by rw [← hfactor]
    rw [hq]
    exact B.mul_mem hhB (B.inv_mem hy)
  have hq : q ∈ T.toSubgroup := by rw [← hBN]; exact ⟨hqB, hqN⟩
  have hr' : (n : Variety.Point G)⁻¹ * r⁻¹ * (n : Variety.Point G) ∈ T.toSubgroup := by
    have h := (Subgroup.mem_normalizer_iff.mp (T.normalizer.inv_mem n.property) r⁻¹).mp
      (T.inv_mem hr)
    simpa only [inv_inv] using h
  have hprod := T.mul_mem hr' hq
  change ((n : Variety.Point G)⁻¹ * r⁻¹ * (n : Variety.Point G)) *
    ((n : Variety.Point G)⁻¹ * r * (m : Variety.Point G)) ∈ T.toSubgroup at hprod
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left] using hprod

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.ConnectedCentralizer.Bruhat.Splitting.CellSeparation

module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates.Transport
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates.SymplecticCore.QuaternionLifting
public import Theory.GroupTheory.PCoreSurjective
public import Theory.Mathieu.M12.Properties.Order

/-!
# The residual and core of the actual M₁₂ double cover

Once the marked centralizer lifts fully, its order is 384 and its two-residual
has image of order 96. Its quotient by the residual consequently has order
at most four and is abelian. Source restriction (i) then places the ambient
center in that residual. Lifting the model two-core through the binary kernel
gives the full preimage of the concrete quaternion core, with normality only
relative to the residual.

The center of this full preimage is exactly the inverse image of {1,z}; it is
fixed by the residual and has exponent two. The quaternion lifting theorem
supplies both the full centralizer and the square-one lift, discharging all
five fields of CoreLiftData without any further source premise.

Source: Aschbacher–Smith, I.2.2(5), common symplectic-core paragraph,
printed p.411 / PDF p.422, and restriction (i), printed p.410 / PDF p.421.
-/

@[expose] public section
noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates
open Sporadic.Mathieu.M12SmallPair

namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates.SymplecticCore

private theorem commutative_of_card_le_four {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 4) : IsMulCommutative G := by
  have hp : 0 < Nat.card G := Nat.card_pos
  have hc : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 := by omega
  rcases hc with h1 | h2 | h3 | h4
  · let : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
  · let : IsCyclic G := isCyclic_of_prime_card h2
    infer_instance
  · let : IsCyclic G := isCyclic_of_prime_card h3
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) h4

variable {K : Type*} [Group K] [Finite K]
  (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12) (u : K)
  (hZ : Nat.card (center K) = 2)
  (m : CoverOrbitData)
  (hc : (centralizer ({u} : Set K)).map (projection e) = firstParabolic)

include hc in
theorem residual_image : (centralizerTwoResidual u).map (projection e) = coverResidual := by
  rw [centralizerTwoResidual, map_embedded_pResidual, hc]
  rfl

omit [Finite K] in
include hZ hc in
theorem centralizer_card : Nat.card (centralizer ({u} : Set K)) = 384 := by
  let C := centralizer ({u} : Set K)
  let f := (projection e).subgroupMap C
  have hzC : center K ≤ C := by
    intro z hz
    exact mem_centralizer_singleton_iff.mpr ((mem_center_iff.mp hz u).symm)
  have hker : f.ker = (center K).subgroupOf C := by
    rw [ker_subgroupMap]
    ext x
    exact projection_eq_one e x
  have hkcard : Nat.card f.ker = 2 := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hzC).toEquiv, hZ]
  have h := f.ker.card_mul_index
  rw [index_ker, f.range_eq_top_of_surjective (projection e |>.subgroupMap_surjective C),
    card_top, hkcard] at h
  have ht : Nat.card (C.map (projection e)) = 192 := by
    rw [hc, card_firstParabolic]
  change 2 * Nat.card (C.map (projection e)) = Nat.card C at h
  rw [ht] at h
  exact h.symm

include hZ m hc in
theorem center_le_residual (hr : CentralCoverRestriction K) :
    center K ≤ centralizerTwoResidual u := by
  let C := centralizer ({u} : Set K)
  let N := pResidual 2 C
  have hcC : Nat.card C = 384 := centralizer_card e u hZ hc
  have hNX : Nat.card N = Nat.card (centralizerTwoResidual u) :=
    (card_map_of_injective C.subtype_injective).symm
  have hsmall : 96 ≤ Nat.card N := by
    have h := (centralizerTwoResidual u).card_map_dvd (projection e)
    rw [residual_image e u hc, m.residual_card] at h
    rw [hNX]
    exact Nat.le_of_dvd Nat.card_pos h
  have hquot : Nat.card (C ⧸ N) ≤ 4 := by
    have h := N.card_mul_index
    rw [hcC, ← index_eq_card] at *
    nlinarith
  let : IsMulCommutative (C ⧸ N) := commutative_of_card_le_four hquot
  let : CommGroup (C ⧸ N) := { (inferInstance : Group (C ⧸ N)) with
    mul_comm := fun x y => mul_comm x y }
  have hd : _root_.commutator C ≤ N := by
    simpa using Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  have hzC : center K ≤ C := by
    intro z hz
    exact mem_centralizer_singleton_iff.mpr ((mem_center_iff.mp hz u).symm)
  have hind : ¬ 2 ∣ (C.map (QuotientGroup.mk' (center K))).index := by
    have hindex : firstParabolic.index = 495 := by
      have h := firstParabolic.card_mul_index
      rw [card_firstParabolic, Sporadic.Mathieu.m12_order] at h
      omega
    have he := (C.map (QuotientGroup.mk' (center K))).index_map_equiv e
    rw [map_map] at he
    change (C.map (projection e)).index = _ at he
    rw [hc, hindex] at he
    rw [← he]
    decide
  exact (hr C hzC hind).trans (map_mono hd)

include hZ m hc in
theorem core_preimage (hr : CentralCoverRestriction K) :
    centralizerCore u = core.comap (projection e) := by
  let X := centralizerTwoResidual u
  have hX := residual_image e u hc
  have hZX := center_le_residual e u hZ m hc hr
  have hker : (projection e).ker = center K := by
    ext x
    exact projection_eq_one e x
  have hpre : coverResidual.comap (projection e) = X := by
    rw [← hX, comap_map_eq, hker, sup_eq_left.mpr hZX]
  let f : X →* coverResidual :=
    ((projection e).comp X.subtype).codRestrict _ (fun x => by
      rw [← hX]
      exact mem_map_of_mem _ x.property)
  have hf : Function.Surjective f := by
    intro y
    have hy : y.val ∈ X.map (projection e) := by
      rw [hX]
      exact y.property
    obtain ⟨x, hx, he⟩ := mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  have hp : IsPGroup 2 f.ker := by
    let g : f.ker →* center K :=
      (X.subtype.comp f.ker.subtype).codRestrict _ (fun x => by
        apply (projection_eq_one e x.val.val).mp
        exact congrArg Subtype.val (MonoidHom.mem_ker.mp x.property))
    have hg : Function.Injective g := by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : center K => (z : K)) h))
    exact (IsPGroup.of_card (p := 2) (n := 1) (by simpa using hZ)).of_injective g hg
  have hcore := f.comap_pCore_of_ker_isPGroup hf hp
  have hmodel (y : coverResidual) : y ∈ pCore 2 coverResidual ↔ (y : Sporadic.Mathieu.M12) ∈ core := by
    rw [← m.residual_core, mem_map]
    exact ⟨fun hy => ⟨y, hy, rfl⟩, fun ⟨z, hz, he⟩ => Subtype.ext he ▸ hz⟩
  have hcX : core ≤ coverResidual := by
    rw [← m.residual_core]
    exact map_subtype_le _
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    change projection e r ∈ core
    exact (hmodel (f r)).mp (hcore.ge hr)
  · intro hx
    have hxX : x ∈ X := hpre ▸ hcX hx
    refine mem_map.mpr ⟨⟨x, hxX⟩, ?_, rfl⟩
    exact hcore.le ((hmodel (f ⟨x, hxX⟩)).mpr hx)

omit [Finite K] in
theorem commute_of_projection_mem_center (hu : projection e u = z)
    (x r : K) (hx : x ∈ centralizer ({u} : Set K))
    (hr : projection e r = 1 ∨ projection e r = z) : Commute x r := by
  rcases hr with hr | hr
  · exact mem_center_iff.mp ((projection_eq_one e r).mp hr) x
  · have hk : r * u⁻¹ ∈ center K := by
      rw [← projection_eq_one e, map_mul, map_inv, hr, hu, mul_inv_cancel]
    have he : r = (r * u⁻¹) * u := by group
    rw [he]
    exact (show Commute x (r * u⁻¹) from mem_center_iff.mp hk x).mul_right
      (mem_centralizer_singleton_iff.mp hx)

omit [Finite K] in
theorem core_center_preimage (hu : projection e u = z)
    (hR : centralizerCore u = core.comap (projection e))
    (r : centralizerCore u) : r ∈ center (centralizerCore u) ↔
      projection e r = 1 ∨ projection e r = z := by
  constructor
  · intro hr
    have hrM : projection e r ∈ core := hR.le r.property
    apply (core_center_mem ⟨projection e r, hrM⟩).mp
    apply mem_center_iff.mpr
    intro s
    obtain ⟨t, ht⟩ := projection_surjective e s.val
    have htR : t ∈ centralizerCore u := by
      rw [hR, mem_comap, ht]
      exact s.property
    have he := congrArg (fun a : centralizerCore u => projection e a)
      (mem_center_iff.mp hr ⟨t, htR⟩)
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, map_mul, ht] using he
  · intro hr
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    exact commute_of_projection_mem_center e u hu s r
      (centralizerTwoResidual_le u ((map_subtype_le _) s.property)) hr

omit [Finite K] in
include hZ in
theorem core_center_square (hu : projection e u = z) (hu2 : u ^ 2 = 1)
    (hR : centralizerCore u = core.comap (projection e))
    (r : centralizerCore u) (hr : r ∈ center (centralizerCore u)) : r ^ 2 = 1 := by
  apply Subtype.ext
  rcases (core_center_preimage e u hu hR r).mp hr with hr | hr
  · exact CoreLiftData.ambient_center_square hZ r ((projection_eq_one e r).mp hr)
  · have hk : (r : K) * u⁻¹ ∈ center K := by
      rw [← projection_eq_one e, map_mul, map_inv, hr, hu, mul_inv_cancel]
    have he : (r : K) = ((r : K) * u⁻¹) * u := by group
    change (r : K) ^ 2 = 1
    rw [he, (show Commute ((r : K) * u⁻¹) u from (mem_center_iff.mp hk u).symm).mul_pow,
      CoreLiftData.ambient_center_square hZ _ hk, hu2, one_mul]

include hZ m hc in
theorem coreLiftData_of_full_centralizer_of_square (hr : CentralCoverRestriction K)
    (hu : projection e u = z) (hu2 : u ^ 2 = 1) : CoreLiftData e u := by
  have hR := core_preimage e u hZ m hc hr
  refine ⟨hc, hR, core_center_preimage e u hu hR,
    core_center_square e u hZ hu hu2 hR, ?_⟩
  intro x r hr
  exact commute_of_projection_mem_center e u hu x r
    (centralizerTwoResidual_le u x.property)
    ((core_center_preimage e u hu hR r).mp hr)

include hZ m in
/-- All five common symplectic-core facts for the actual M₁₂ cover. The
restriction (i) hypothesis and the explicit quotient model data are the only
inputs beyond the central quotient and its order-two kernel. In particular,
no involution-order or centralizer-lifting hypothesis remains. -/
theorem coreLiftData (hr : CentralCoverRestriction K)
    (hu : projection e u = z) : CoreLiftData e u := by
  obtain ⟨hu2, hcentralizer⟩ := quaternion_lifting e hZ u hu
  exact coreLiftData_of_full_centralizer_of_square e u hZ m hcentralizer hr hu hu2

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates.SymplecticCore

module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.BinaryAmbient
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.M22Center
public import Theory.Representation.BinaryPermutation.SixCoreExtension.VectorSquares
public import Theory.GroupTheory.SylowCentralSquareRoots
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# The nonsquare covering involution in an actual binary M₂₂ component

Every noncentral involution lies in its fixed-hexad radical. In the genuine
binary hexad model both nonconstant vector orbits have square roots, whereas
the covering involution has no square root anywhere in the component.
Sylow conjugacy inside the involution centralizer transports those roots
into any component Sylow in whose center the involution lies. Consequently
the covering line is the unique central nonsquare-involution line and is
characteristic in that component Sylow.

This does not assert characteristicness in the larger Sylow S of H.
Source: Aschbacher--Smith I.2.2(6b) and 2.3.9(7), pp.412 and 525--526.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open ChapterI.Section02.ExceptionalCovers
open M22Local
open Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The weight-two root is allowed in the full hexad, even though it is
excluded from the two-residual core used by the unique core-square theorem. -/
theorem LocalSetup.mathieuTwentyTwo_binary_noncentral_square
    (h : LocalSetup H L M S z) (e : (L ⧸ pCore 2 L) ≃* M22)
    (hc : Nat.card (pCore 2 L) = 2) (u : L)
    (hu : orderOf u = 2) (hun : u ∉ center L) : ∃ x : L, x ^ 2 = u := by
  let := h.finite
  let := h.quasisimple
  let eZ := h.mathieuTwentyTwo_centerQuotient e
  have hZ : Nat.card (center L) = 2 := by
    simpa only [h.mathieuTwentyTwo_center_eq e] using hc
  obtain ⟨hB,hr,_⟩ := M22Local.centralizer_le_fixedHexad eZ u hu hun
  obtain ⟨d⟩ := M22Local.Binary.exists_hexadRecognition_of_perfect eZ hZ hB
  let r : hexadRadical eZ (m22FixedPoints (projection eZ u)) := ⟨u,hr⟩
  have hv : BinaryPermutation.coreToNatural (Fin 6) (d.radicalEquiv r).toAdd ≠ 0 :=
    fun he => hun ((d.center_iff r).mpr he)
  obtain ⟨x,hx⟩ := BinaryPermutation.SixCoreExtension.exists_square_vector _ hv
  refine ⟨(d.modelEquiv.symm x).val,?_⟩
  have he : d.modelEquiv.symm x ^ 2 = fixedHexadElement eZ u := by
    apply d.modelEquiv.injective
    rw [map_pow,d.modelEquiv.apply_symm_apply,hx]
    exact (d.modelEquiv_radical r).symm
  exact congrArg Subtype.val he

/-- For a central involution of the component Sylow, failure to be a square
in that very Sylow characterizes membership in the original covering center. -/
theorem LocalSetup.mathieuTwentyTwo_binary_sylow_center_iff_nonsquare
    (h : LocalSetup H L M S z) (e : (L ⧸ pCore 2 L) ≃* M22)
    (hc : Nat.card (pCore 2 L) = 2) (R : Sylow 2 L) (u : R)
    (hu : u ∈ center R) (hu2 : orderOf u = 2) :
    (u : L) ∈ center L ↔ ¬ ∃ y : R, y ^ 2 = u := by
  let := h.finite
  constructor
  · intro huL ⟨y,hy⟩
    let k : pCore 2 L := ⟨u,h.mathieuTwentyTwo_center_eq e ▸ huL⟩
    have hk : k ≠ 1 := by
      intro he
      have hu1 : u = 1 := Subtype.ext (congrArg (fun a : pCore 2 L => (a : L)) he)
      simp [hu1] at hu2
    exact h.mathieuTwentyTwo_binary_kernel_not_square e hc k hk
      ⟨y,congrArg Subtype.val hy⟩
  · intro hns
    by_contra hn
    have hu_sq : (u : L) ^ 2 = 1 := congrArg (fun x : R => (x : L))
      (show u ^ 2 = 1 by simpa only [hu2] using pow_orderOf_eq_one u)
    exact hns (R.exists_square_root_of_central_involution u hu hu_sq
      (h.mathieuTwentyTwo_binary_noncentral_square e hc u
        ((Subgroup.orderOf_coe u).trans hu2) hn))

/-- Characteristicness holds in the literal component Sylow; no transfer
to the larger source Sylow is included or assumed. -/
theorem LocalSetup.mathieuTwentyTwo_binary_kernel_characteristic_component_sylow
    (h : LocalSetup H L M S z) (e : (L ⧸ pCore 2 L) ≃* M22)
    (hc : Nat.card (pCore 2 L) = 2) (R : Sylow 2 L) :
    ((center L).subgroupOf (R : Subgroup L)).Characteristic := by
  let := h.finite
  have hZcard : Nat.card (center L) = 2 := by
    simpa only [h.mathieuTwentyTwo_center_eq e] using hc
  apply characteristic_iff_le_comap.mpr
  intro a u hu
  change (a u : L) ∈ center L
  by_cases hu1 : u = 1
  · simp [hu1]
  have huZ : u ∈ center R := mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_center_iff.mp hu (x : L)))
  have huo : orderOf u = 2 := by
    let uz : center L := ⟨u,hu⟩
    have hn : uz ≠ 1 := fun hh => hu1 (Subtype.ext (congrArg (fun a : center L => (a : L)) hh))
    have hzord : orderOf uz = 2 := orderOf_eq_prime
      (by simpa only [hZcard] using pow_card_eq_one' (x := uz)) hn
    exact (Subgroup.orderOf_coe u).symm.trans ((Subgroup.orderOf_coe uz).trans hzord)
  have haZ : a u ∈ center R := (centerCongr a ⟨u,huZ⟩).property
  have hao : orderOf (a u) = 2 := (a.orderOf_eq u).trans huo
  apply (h.mathieuTwentyTwo_binary_sylow_center_iff_nonsquare e hc R (a u) haZ hao).mpr
  intro hh
  apply (h.mathieuTwentyTwo_binary_sylow_center_iff_nonsquare e hc R u huZ huo).mp hu
  obtain ⟨x,hx⟩ := hh
  exact ⟨a.symm x,by rw [← map_pow,hx,a.symm_apply_apply]⟩


/-- The original Γ₀ displacement must move the component Sylow itself.
Its covering line is now proved characteristic, so moving only a chosen
model or only its projection is insufficient. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_binary_component_sylow_displacement
    [Finite G] {C : GroupClass} (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE C G) (sourceC : LocalC129Input C G)
    (e : (L ⧸ pCore 2 L) ≃* M22) (hc : Nat.card (pCore 2 L) = 2) :
    ∃ R : Sylow 2 L,
      (R : Subgroup L) = ((S : Subgroup H).map H.subtype).subgroupOf L ∧
      ((center L).subgroupOf (R : Subgroup L)).Characteristic ∧
      ∃ g ∈ (c.T : Subgroup G),
        g ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
        g ∉ normalizer ((R : Subgroup L).map L.subtype : Set G) := by
  let h := c.localSetup hG structural115Input sourceC
  obtain ⟨R,hR⟩ := h.component_sylow
  let : ((center L).subgroupOf (R : Subgroup L)).Characteristic :=
    h.mathieuTwentyTwo_binary_kernel_characteristic_component_sylow e hc R
  have hk : pCore 2 L ≠ ⊥ := by
    intro hb
    rw [hb,card_bot] at hc
    omega
  obtain ⟨g,hg,hs,hn⟩ := c.mathieuTwentyTwo_kernel_displacement hG structural115Input sourceC e hk
  refine ⟨R,hR,inferInstance,g,hg,hs,?_⟩
  intro hgr
  have he := normalizer_le_normalizer_characteristic_map L.subtype L.subtype_injective
    (R : Subgroup L) ((center L).subgroupOf (R : Subgroup L)) hgr
  have hZR : center L ≤ (R : Subgroup L) := by
    rw [h.mathieuTwentyTwo_center_eq e]
    exact fitting_pCore_le_sylow R
  rw [map_subgroupOf_eq_of_le hZR,h.mathieuTwentyTwo_center_eq e] at he
  exact hn he

end CFSG.Quasithin.Chapter2.ComponentRefinement

module

public import Theory.GroupAction.PerfectCentralQuotientSylow
public import Theory.GroupAction.CentralKernelFixedResidual

/-!
# Fixed points of Sylow-fixing involutions in central quotients

For an equivariant central surjection, an involution fixing a Sylow
2-subgroup maps its fixed subgroup onto the full fixed subgroup downstairs.
On the preimage of that subgroup, the central displacement is a homomorphism.
It kills the source Sylow subgroup, so its image has odd order. The involution
inverts the image; taking a square root there corrects each lift to a fixed lift.
Thus no splitting of the central kernel and no assumed fixed-point lifting
are needed. The automorphisms and quotient map are retained literally.

Source: Aschbacher--Smith, proof of 1.1.5(3), printed pp.502--503.
-/

public section

open Subgroup
namespace MulAut
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- Fixed points lift through a central surjection when an involution fixes
an actual Sylow two-subgroup pointwise. -/
theorem fixedSubgroupMap_surjective_of_sylow_fixed (a : MulAut G) (b : MulAut H)
    (f : G →* H) (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (heq : ∀ x, f (a x) = b (f x)) (ha : a ^ 2 = 1)
    (P : Sylow 2 G) (hP : ∀ x ∈ P, a x = x) :
    Function.Surjective (fixedSubgroupMap a b f heq) := by
  let E := b.fixedSubgroup.comap f
  have hdmem (x : E) : (x : G)⁻¹ * a x ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq]
    have hx : b (f x) = f x := (mem_fixedSubgroup _ _).mp x.property
    rw [hx, inv_mul_cancel]
  let d : E →* G := {
    toFun x := (x : G)⁻¹ * a x
    map_one' := by simp
    map_mul' x y := by
      change ((x : G) * y)⁻¹ * a ((x : G) * y) =
        ((x : G)⁻¹ * a x) * ((y : G)⁻¹ * a y)
      rw [mul_inv_rev, map_mul]
      have hz := mem_center_iff.mp (hc (hdmem x)) (y : G)⁻¹
      calc
        _ = ((y : G)⁻¹ * ((x : G)⁻¹ * a x)) * a y := by group
        _ = (((x : G)⁻¹ * a x) * (y : G)⁻¹) * a y := by rw [hz]
        _ = _ := by group }
  have hPE : (P : Subgroup G) ≤ E := by
    intro x hx
    change f x ∈ b.fixedSubgroup
    rw [mem_fixedSubgroup]
    rw [← heq, hP x hx]
  have hmap : (((P.subtype hPE).mapSurjective d.rangeRestrict_surjective) :
      Subgroup d.range) = ⊥ := by
    apply le_bot_iff.mp
    rintro _ ⟨x, hx, rfl⟩
    apply Subtype.ext
    change (x : G)⁻¹ * a x = 1
    rw [hP x hx, inv_mul_cancel]
  have hodd : Odd (Nat.card d.range) := by
    have hn := ((P.subtype hPE).mapSurjective d.rangeRestrict_surjective).not_dvd_index
    rw [hmap, index_bot] at hn
    simpa only [← even_iff_two_dvd, Nat.not_even_iff_odd] using hn
  have haapply (x : G) : a (a x) = x := by
    have h := congrArg (fun c : MulAut G => c x) ha
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  have hinv (t : d.range) : a (t : G) = (t : G)⁻¹ := by
    obtain ⟨x, hx⟩ := t.property
    change d x = (t : G) at hx
    rw [← hx]
    change a ((x : G)⁻¹ * a x) = ((x : G)⁻¹ * a x)⁻¹
    rw [map_mul, map_inv, haapply, mul_inv_rev, inv_inv]
  intro y
  obtain ⟨x, hx⟩ := hf y
  let xE : E := ⟨x, by change f x ∈ b.fixedSubgroup; rw [hx]; exact y.property⟩
  obtain ⟨t, ht⟩ := hodd.coprime_two_right.pow_left_bijective.surjective
    (d.rangeRestrict xE)
  have htval : (t : G) ^ 2 = x⁻¹ * a x := congrArg Subtype.val ht
  have htker : (t : G) ∈ f.ker := by
    obtain ⟨z, hz⟩ := t.property
    rw [← hz]
    exact hdmem z
  have hfix : a (x * t) = x * t := by
    rw [map_mul, hinv]
    have hax : a x = x * (t : G) ^ 2 := by rw [htval]; group
    rw [hax, pow_two]
    group
  refine ⟨⟨x * t, (mem_fixedSubgroup _ _).mpr hfix⟩, ?_⟩
  apply Subtype.ext
  change f (x * t) = y
  rw [map_mul, show f t = 1 from htker, mul_one, hx]

/-- The fixed subgroup image is the full fixed subgroup of the genuine central
quotient action, not merely a subgroup of it. -/
theorem map_fixedSubgroup_eq_quotient_center_of_sylow_fixed
    (a : MulAut G) (ha : a ^ 2 = 1) (P : Sylow 2 G)
    (hP : ∀ x ∈ P, a x = x) :
    a.fixedSubgroup.map (QuotientGroup.mk' (center G)) =
      ((center G).quotientAut a).fixedSubgroup := by
  apply le_antisymm (map_fixedSubgroup_le_quotient_center a)
  intro y hy
  obtain ⟨x, hx⟩ := fixedSubgroupMap_surjective_of_sylow_fixed
    a ((center G).quotientAut a) (QuotientGroup.mk' (center G))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    (fun x => (Subgroup.quotientAut_apply_mk _ a x).symm) ha P hP ⟨y, hy⟩
  exact ⟨x, x.property, congrArg Subtype.val hx⟩

omit [Finite G] in
/-- The fixed-point map inherits centrality of the original kernel. -/
theorem fixedSubgroupMap_ker_le_center (a : MulAut G) (b : MulAut H)
    (f : G →* H) (heq : ∀ x, f (a x) = b (f x)) (hc : f.ker ≤ center G) :
    (fixedSubgroupMap a b f heq).ker ≤ center a.fixedSubgroup := by
  intro x hx
  have hx' : f (x : G) = 1 := congrArg Subtype.val hx
  rw [mem_center_iff]
  intro y
  apply Subtype.ext
  exact mem_center_iff.mp (hc hx') (y : G)

end MulAut

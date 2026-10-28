module

public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Recognizing a universal cover by its kernel size

A finite quasisimple covering is universal if its kernel is at least as
large as the kernel of the constructed universal cover. The universal map
onto the proposed cover is then bijective, by the order formula for a
surjection. Transporting the universal lifts through that actual isomorphism
proves universality, including compatibility and uniqueness.

This is the upper-bound/lower-bound argument used in the Schur multiplier
calculations of Aschbacher–Smith I.1.3–I.1.4, printed pp.407–408.
-/

namespace Theory.GroupTheory.Covering

universe u w

variable {L G : Type u} [Group L] [Finite L] [IsQuasisimple L]
variable [Group G] [Finite G] [IsQuasisimple G]

private theorem card_eq_kernel_mul (f : Covering L G) :
    Nat.card L = Nat.card f.toMonoidHom.ker * Nat.card G := by
  have h := f.toMonoidHom.ker.card_mul_index
  rw [Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      f.toMonoidHom f.surjective).toEquiv] at h
  exact h.symm

/-- A kernel upper bound for the constructed universal cover certifies an
explicit covering as universal. Universality holds in every target universe. -/
public theorem isUniversal_of_kernel_card_le (f : Covering L G)
    (hcard : Nat.card (PerfectCentralCovering.universalProjection G).ker ≤
      Nat.card f.toMonoidHom.ker) : IsUniversal.{u, u, w} f := by
  let c := PerfectCentralCovering.universalQuasisimpleCover G
  have hc : IsUniversal.{u, u, u} c :=
    PerfectCentralCovering.universalQuasisimpleCover_isUniversal G
  let a := hc.lift f
  have ha : f.comp a = c := hc.lift_fac f
  have hle : Nat.card (PerfectCentralCovering.UniversalGroup G) ≤ Nat.card L := by
    rw [card_eq_kernel_mul c, card_eq_kernel_mul f]
    exact Nat.mul_le_mul_right _ hcard
  let e := MulEquiv.ofBijective a.toMonoidHom (a.surjective.bijective_of_nat_card_le hle)
  have he (x : L) : c (e.symm x) = f x := by
    rw [← ha]
    change f (e (e.symm x)) = f x
    rw [e.apply_symm_apply]
  intro M _ _ _ g
  have hc' : IsUniversal.{u, u, w} c :=
    PerfectCentralCovering.universalQuasisimpleCover_isUniversal G
  let b := hc'.lift g
  refine ⟨b.comp (ofMulEquiv e.symm), ?_, ?_⟩
  · ext x
    change g (b (e.symm x)) = f x
    have hb := congrArg (fun k : Covering _ G => k (e.symm x)) (hc'.lift_fac g)
    exact hb.trans (he x)
  · intro d hd
    have hda : g.comp (d.comp a) = c := by rw [← comp_assoc, hd, ha]
    have hdb : d.comp a = b := hc'.hom_ext g hda (hc'.lift_fac g)
    ext x
    have h := congrArg (fun k : Covering _ M => k (e.symm x)) hdb
    change d (e (e.symm x)) = b (e.symm x) at h
    simpa only [comp_apply, ofMulEquiv_apply, e.apply_symm_apply] using h

end Theory.GroupTheory.Covering

namespace Theory.GroupTheory.Covering

universe u v w z

/-- Changing the base through an actual group isomorphism preserves the
universal property, with no restriction on the base or target universes. -/
public theorem IsUniversal.comp_ofMulEquiv
    {L : Type u} {G : Type v} {H : Type z}
    [Group L] [Finite L] [IsQuasisimple L]
    [Group G] [Finite G] [IsQuasisimple G]
    [Group H] [Finite H] [IsQuasisimple H]
    {f : Covering L G} (hf : IsUniversal.{v, u, w} f) (e : G ≃* H) :
    IsUniversal.{z, u, w} ((ofMulEquiv e).comp f) := by
  intro M _ _ _ g
  let g' := (ofMulEquiv e.symm).comp g
  obtain ⟨h, hh, hu⟩ := hf M g'
  refine ⟨h, ?_, ?_⟩
  · ext x
    have hx := congrArg (fun k : Covering L G => k x) hh
    have hx' : e.symm (g (h x)) = f x := by
      simpa only [g', comp_apply, ofMulEquiv_apply] using hx
    simpa only [comp_apply, ofMulEquiv_apply, e.apply_symm_apply] using congrArg e hx'
  · intro k hk
    apply hu k
    ext x
    have hx := congrArg (fun d : Covering L H => d x) hk
    have hx' : g (k x) = e (f x) := by
      simpa only [comp_apply, ofMulEquiv_apply] using hx
    simpa only [g', comp_apply, ofMulEquiv_apply, e.symm_apply_apply] using
      congrArg e.symm hx'

end Theory.GroupTheory.Covering

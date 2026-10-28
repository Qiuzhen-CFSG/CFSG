module
public import Theory.SpecificGroups.SL3.PerfectCentralCover
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# Descent of actions with a central commutator kernel

Suppose a perfect subgroup L has a specified full SL₃ core quotient.
If an action kernel is contained in N, N meets L in O₂(L), and [N,L]
acts trivially, the actual L-image is a perfect central cover of that
same SL₃. Outside field orders two and four the ordinary scalar-cover
lift makes this projection injective. The resulting faithful action
retains the original quotient map on every representative.

This applies to the centers of nonabelian MS commutator cores, since the
whole commutator acts trivially there. It does not assume those centers
have exponent two or identify them with natural modules.
Source: Aschbacher--Smith I.1.3, printed p.407, and the central sections
in C.1.34, printed pp.136--137; the scalar lift uses the checked Steinberg
presentation through PSL3.OrdinaryCenterRecognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.SL3.CommutatorCentralCover
variable {G A F : Type*} [Group G] [Group A] [Field F]
  (L N : Subgroup G)
  (e : (L ⧸ pCore 2 L) ≃* SL(3,F)) (a : G →* A)
  (hN : N.comap L.subtype = pCore 2 L) (hk : a.ker ≤ N)
  (hc : ⁅N,L⁆ ≤ a.ker)

private abbrev restricted : L →* A := a.comp L.subtype

include hN hk
private theorem restricted_kernel_le : (restricted L a).ker ≤ pCore 2 L := by
  rw [←hN]
  intro l hl
  exact hk hl

private def projection : (restricted L a).range →* SL(3,F) :=
  (restricted L a).rangeRestrict.liftOfSurjective
    (restricted L a).rangeRestrict_surjective
    ⟨e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)), by
      intro l hl
      have hl' : l ∈ (restricted L a).ker := by
        simpa only [MonoidHom.ker_rangeRestrict] using hl
      change e (QuotientGroup.mk' (pCore 2 L) l) = 1
      rw [MulEquiv.map_eq_one_iff]
      exact (QuotientGroup.eq_one_iff l).mpr (restricted_kernel_le L N a hN hk hl')⟩

private theorem projection_apply (l : L) :
    projection L N e a hN hk ((restricted L a).rangeRestrict l) =
      e (QuotientGroup.mk' (pCore 2 L) l) := by
  simp only [projection,MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]

private theorem projection_surjective : Function.Surjective (projection L N e a hN hk) := by
  intro g
  obtain ⟨l,hl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
  exact ⟨(restricted L a).rangeRestrict l,(projection_apply L N e a hN hk l).trans hl⟩

include hc
private theorem projection_kernel_central :
    (projection L N e a hN hk).ker ≤ center (restricted L a).range := by
  have hz : ⁅N.map a,L.map a⁆ = ⊥ := by
    rw [←map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr hc
  intro b hb
  obtain ⟨l,rfl⟩ := (restricted L a).rangeRestrict_surjective b
  have hl : (l : G) ∈ N := by
    have he : projection L N e a hN hk ((restricted L a).rangeRestrict l) = 1 := hb
    rw [projection_apply,MulEquiv.map_eq_one_iff] at he
    have hp := (QuotientGroup.eq_one_iff l).mp he
    change l ∈ N.comap L.subtype
    rwa [hN]
  rw [mem_center_iff]
  intro c
  obtain ⟨k,rfl⟩ := (restricted L a).rangeRestrict_surjective c
  apply Subtype.ext
  exact (commutator_eq_bot_iff_le_centralizer.mp hz)
    (mem_map_of_mem a hl) (a k) (mem_map_of_mem a k.property)

variable [Group.IsPerfect L]

/-- A normal kernel sandwich and a trivial core commutator give the actual
perfect central cover of the full marked SL₃. -/
def cover : PerfectCentralCovering.Cover (a.comp L.subtype).range SL(3,F) where
  toMonoidHom := projection L N e a hN hk
  surjective := projection_surjective L N e a hN hk
  isPerfect := Group.IsPerfect.range _
  ker_le_center := projection_kernel_central L N e a hN hk hc

/-- The covering projection is the supplied quotient marking on every
original component representative. -/
theorem cover_apply (l : L) :
    (cover L N e a hN hk hc).toMonoidHom ((a.comp L.subtype).rangeRestrict l) =
      e (QuotientGroup.mk' (pCore 2 L) l) :=
  projection_apply L N e a hN hk l

variable [Finite G] [Finite F]

/-- Outside orders two and four, the original action descends faithfully to
SL₃, retaining its values on every element of L. -/
theorem exists_descended_action (h2 : Nat.card F ≠ 2) (h4 : Nat.card F ≠ 4) :
    ∃ b : SL(3,F) →* A, Function.Injective b ∧
      ∀ l : L, b (e (QuotientGroup.mk' (pCore 2 L) l)) = a l := by
  let f := cover L N e a hN hk hc
  let : Finite (restricted L a).range := Finite.of_surjective _
    (restricted L a).rangeRestrict_surjective
  let := f.isPerfect
  obtain ⟨k,hk',_⟩ := Matrix.PSL3.OrdinaryCenterRecognition.exists_scalar_lift h2 h4
    f.quotientCenterEquiv
  have hi : Function.Injective f.toMonoidHom :=
    (f.surjective.bijective_of_nat_card_le (Nat.card_le_card_of_surjective k hk')).1
  let q := MulEquiv.ofBijective f.toMonoidHom ⟨hi,f.surjective⟩
  refine ⟨(restricted L a).range.subtype.comp q.symm.toMonoidHom,
    (restricted L a).range.subtype_injective.comp q.symm.injective,?_⟩
  intro l
  have he : e (QuotientGroup.mk' (pCore 2 L) l) =
      q ((restricted L a).rangeRestrict l) := (projection_apply L N e a hN hk l).symm
  change (q.symm (e (QuotientGroup.mk' (pCore 2 L) l)) : A) = a l
  rw [he,q.symm_apply_apply]
  rfl

end Matrix.SL3.CommutatorCentralCover

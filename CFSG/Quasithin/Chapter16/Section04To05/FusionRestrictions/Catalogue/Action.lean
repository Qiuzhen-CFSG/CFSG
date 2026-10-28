module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.Catalogue.Models
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.TwoCentral

/-!
# The actual starred groups and elementary numerical deductions

The source star denotes N_G(L)/C_G(L), with normality relative to the
normalizer. Its component image is canonically isomorphic to L/Z(L).
We construct this isomorphism from the kernel of the restricted projection;
no unspecified model tag is used to identify the quotient.

Two elementary deductions isolate the numerical work in 16.5.8–10. A
two-subgroup has relative index at most two in a normal subgroup if the
ambient index is not divisible by four. A nontrivial two-subgroup has a
nontrivial center, so its centralizer in an overgroup has order at least two.
The model-specific upper bound and outer-automorphism calculation remain
separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Notation
16.4.1 and Lemmas 16.5.8–10, printed pp.1183 and 1198–1199.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.Catalogue
open Subgroup
variable {G : Type*} [Group G]

/-- H* = N_G(L)/C_G(L), with the kernel inside its normalizer. -/
abbrev ActionQuotient (L : Subgroup G) :=
  normalizer (L : Set G) ⧸
    (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G))

/-- The source projection from H to H*. -/
def starProjection (L : Subgroup G) : normalizer (L : Set G) →* ActionQuotient L :=
  QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))

/-- Image of a subgroup intersected with H. For T, L and R, the earlier
setup supplies containment in H, so this is exactly the source star. -/
def star (L S : Subgroup G) : Subgroup (ActionQuotient L) :=
  (S.subgroupOf (normalizer (L : Set G))).map (starProjection L)

/-- Restrict the quotient projection to the actual component. -/
def componentProjection (L : Subgroup G) : L →* ActionQuotient L :=
  (starProjection L).comp (inclusion L.le_normalizer)

/-- Restricting the ambient centralizer kernel to L gives exactly Z(L). -/
theorem componentProjection_ker (L : Subgroup G) :
    (componentProjection L).ker = center L := by
  ext x
  change starProjection L (inclusion L.le_normalizer x) = 1 ↔ x ∈ center L
  change (QuotientGroup.mk (inclusion L.le_normalizer x) : ActionQuotient L) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  change (x : G) ∈ centralizer (L : Set G) ↔ x ∈ center L
  constructor
  · intro hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_centralizer_iff.mp hx y y.property))
  · intro hx
    exact mem_centralizer_iff.mpr (fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩))

/-- The restricted homomorphism has the actual starred component as range. -/
theorem componentProjection_range (L : Subgroup G) :
    (componentProjection L).range = star L L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨inclusion L.le_normalizer y, y.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- The source L* is the central quotient, by the first isomorphism theorem. -/
noncomputable def centralQuotientStarEquiv (L : Subgroup G) :
    (L ⧸ center L) ≃* star L L :=
  ((QuotientGroup.quotientMulEquivOfEq (componentProjection_ker L).symm).trans
    (QuotientGroup.quotientKerEquivRange (componentProjection L))).trans
      (MulEquiv.subgroupCongr (componentProjection_range L))

/-- Star preserves subgroup containment. -/
theorem star_mono (L : Subgroup G) {P Q : Subgroup G} (h : P ≤ Q) :
    star L P ≤ star L Q := map_mono (comap_mono h)

/-- Star sends actual two-subgroups to two-subgroups. -/
theorem star_isPGroup (L : Subgroup G) {P : Subgroup G} (hP : IsPGroup 2 P) :
    IsPGroup 2 (star L P) :=
  (hP.comap_of_injective (normalizer (L : Set G)).subtype
    (normalizer (L : Set G)).subtype_injective).map (starProjection L)

/-- Single-class input for 16.5.8; conjugacy is inside the component. -/
def OneInvolutionClass (L : Type*) [Group L] : Prop :=
  ∀ a b : L, orderOf a = 2 → orderOf b = 2 → IsConj a b

section Numerical
variable {H : Type*} [Group H] [Finite H]

/-- The elementary outer-index step: its local model input concerns the
whole ambient index; the conclusion concerns the specified two-subgroup. -/
theorem relative_index_le_two (Q P : Subgroup H) [Q.Normal]
    (hP : IsPGroup 2 P) (houter : ¬ 4 ∣ Q.index) : Q.relIndex P ≤ 2 := by
  obtain ⟨k, hk⟩ := hP.index (Q.subgroupOf P)
  change Q.relIndex P = 2 ^ k at hk
  have hkd : 2 ^ k ∣ Q.index := hk ▸ Q.relIndex_dvd_index_of_normal P
  have hk2 : k < 2 := by
    by_contra hh
    have hd : 4 ∣ 2 ^ k := by
      change 2 ^ 2 ∣ 2 ^ k
      exact pow_dvd_pow 2 (by omega)
    exact houter (hd.trans hkd)
  rw [hk]
  interval_cases k <;> norm_num

/-- A nontrivial two-subgroup contributes its center to its centralizer. -/
theorem two_le_card_centralizer (P Q : Subgroup H) (hQP : Q ≤ P)
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) :
    2 ≤ Nat.card ↥(P ⊓ centralizer (Q : Set H)) := by
  let _ : Nontrivial Q := (nontrivial_iff_ne_bot Q).mpr hne
  let _ : Nontrivial (center Q) := hQ.center_nontrivial
  let f : center Q → ↥(P ⊓ centralizer (Q : Set H)) := fun x =>
    ⟨x, hQP x.val.property, mem_centralizer_iff.mpr (fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp x.property ⟨y, hy⟩))⟩
  have hinj : Function.Injective f := by
    intro x y he
    have hh : ((x : Q) : H) = ((y : Q) : H) :=
      congrArg (fun z : ↥(P ⊓ centralizer (Q : Set H)) => (z : H)) he
    exact Subtype.ext (Subtype.ext hh)
  have hlo : 1 < Nat.card (center Q) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  exact (by omega : 2 ≤ Nat.card (center Q)).trans (Nat.card_le_card_of_injective f hinj)

/-- The upper bound in 16.5.10(4) gives the equality required by 16.5.7;
this step must not be skipped when applying that earlier lemma. -/
theorem card_centralizer_eq_two (P Q : Subgroup H) (hQP : Q ≤ P)
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hupper : Nat.card ↥(P ⊓ centralizer (Q : Set H)) ≤ 2) :
    Nat.card ↥(P ⊓ centralizer (Q : Set H)) = 2 :=
  le_antisymm hupper (two_le_card_centralizer P Q hQP hQ hne)

end Numerical
end CFSG.Quasithin.Chapter16.Intersections.Catalogue

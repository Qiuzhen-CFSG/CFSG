module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.FoldedCellGeometry

/-!
# The concrete binary triality Tits system

The actual folded root words give a section of the normalizer quotient.
The quotient is dihedral of order twelve. Folded exchange and the explicit
negative-root nontriviality witness give the remaining Tits axioms. Thus the
Borel and cells here are those of the original graph-field fixed elementary
central quotient, including at q = 2.

Sources: GLS3 2.3.4–5 and §2.4 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section
open scoped Pointwise
namespace Triality.Standard.ConcreteBruhat
open Parabolics Theory.AlgebraicGroup

private theorem representative_product_eq {G : Type*} [Group G] (B N : Subgroup G)
    [((B ⊓ N).subgroupOf N).Normal]
    (v w : N ⧸ (B ⊓ N).subgroupOf N) (nv nw : N)
    (hv : QuotientGroup.mk' ((B ⊓ N).subgroupOf N) nv = v)
    (hw : QuotientGroup.mk' ((B ⊓ N).subgroupOf N) nw = w) :
    TitsSystem.representativeSet B N v * (B : Set G) *
        TitsSystem.representativeSet B N w =
      ({nv.val} : Set G) * (B : Set G) * ({nw.val} : Set G) := by
  rw [TitsSystem.representativeSet_mul_B B N v nv hv, mul_assoc,
    TitsSystem.B_mul_representativeSet B N w nw hw, ← mul_assoc]

private theorem forall_range_equiv {I A B : Type*} (e : A ≃ B) (f : I → A)
    (R : B → B → Prop) (h : ∀ i w, R (e (f i)) (e w)) :
    ∀ s ∈ Set.range (e ∘ f), ∀ w, R s w := by
  rintro _ ⟨i, rfl⟩ q
  obtain ⟨w, rfl⟩ := e.surjective q
  exact h i w

section Binary
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn
local instance : ((borel P ⊓ normalizerCandidate P rfl).subgroupOf
    (normalizerCandidate P rfl)).Normal :=
  RelativeNormalizer.normalizer_intersection_normal n hn

private theorem quotient_exchange (a : Node) (w : DihedralGroup 6) :
    TitsSystem.representativeSet (borel P) (normalizerCandidate P rfl)
        (RelativeNormalizer.quotientEquiv n hn (relativeReflection a)) *
      (borel P : Set (Carrier P)) *
      TitsSystem.representativeSet (borel P) (normalizerCandidate P rfl)
        (RelativeNormalizer.quotientEquiv n hn w) ⊆
      cell P rfl (relativeReflection a * w) ∪ cell P rfl w := by
  rw [representative_product_eq (borel P) (normalizerCandidate P rfl)
    (RelativeNormalizer.quotientEquiv n hn (relativeReflection a))
    (RelativeNormalizer.quotientEquiv n hn w)
    (RelativeNormalizer.normalizerLift P rfl (relativeReflection a))
    (RelativeNormalizer.normalizerLift P rfl w) rfl rfl]
  rintro g ⟨x, ⟨s, hs, b, hb, rfl⟩, v, hv, rfl⟩
  rcases hs with rfl
  rcases hv with rfl
  change weylRepresentative P rfl (relativeReflection a) * b *
    weylRepresentative P rfl w ∈ _
  rw [weylRepresentative_simple P rfl a]
  exact FoldedCellGeometry.simple_reflection_exchange n hn a w hb

private theorem quotient_nontrivial (a : Node) :
    TitsSystem.representativeSet (borel P) (normalizerCandidate P rfl)
        (RelativeNormalizer.quotientEquiv n hn (relativeReflection a)) *
      (borel P : Set (Carrier P)) *
      TitsSystem.representativeSet (borel P) (normalizerCandidate P rfl)
        (RelativeNormalizer.quotientEquiv n hn (relativeReflection a)) ≠
      (borel P : Set (Carrier P)) := by
  rw [representative_product_eq (borel P) (normalizerCandidate P rfl)
    (RelativeNormalizer.quotientEquiv n hn (relativeReflection a))
    (RelativeNormalizer.quotientEquiv n hn (relativeReflection a))
    (RelativeNormalizer.normalizerLift P rfl (relativeReflection a))
    (RelativeNormalizer.normalizerLift P rfl (relativeReflection a)) rfl rfl]
  change ({weylRepresentative P rfl (relativeReflection a)} : Set (Carrier P)) *
    (borel P : Set (Carrier P)) * {weylRepresentative P rfl (relativeReflection a)} ≠ _
  rw [weylRepresentative_simple P rfl a]
  intro heq
  obtain ⟨b, hb, hnot⟩ := FoldedCellGeometry.exists_borel_conjugate_not_borel n hn a
  apply hnot
  exact heq.le ⟨_, ⟨_, rfl, _, hb, rfl⟩, _, rfl, rfl⟩

private theorem quotient_full_exchange :
    ∀ s ∈ Set.range (RelativeNormalizer.simpleReflection n hn), ∀ w,
      TitsSystem.representativeSet (borel P) (normalizerCandidate P rfl) s *
          (borel P : Set (Carrier P)) *
          TitsSystem.representativeSet (borel P) (normalizerCandidate P rfl) w ⊆
        ((borel P : Set (Carrier P)) *
          TitsSystem.representativeSet (borel P) (normalizerCandidate P rfl) (s * w) *
          (borel P : Set (Carrier P))) ∪
        ((borel P : Set (Carrier P)) *
          TitsSystem.representativeSet (borel P) (normalizerCandidate P rfl) w *
          (borel P : Set (Carrier P))) := by
  apply forall_range_equiv (RelativeNormalizer.quotientEquiv n hn).toEquiv relativeReflection
  intro a w
  let e := RelativeNormalizer.quotientEquiv n hn
  let R := fun q => (borel P : Set (Carrier P)) *
    TitsSystem.representativeSet (borel P) (normalizerCandidate P rfl) q *
    (borel P : Set (Carrier P))
  have hsw : cell P rfl (relativeReflection a * w) =
      R (e (relativeReflection a) * e w) :=
    (RelativeNormalizer.cell_eq_quotient_cell n hn (relativeReflection a * w)).trans
      (congrArg R (map_mul e _ _))
  have heq := congrArg₂ (fun A B : Set (Carrier P) => A ∪ B)
    hsw (RelativeNormalizer.cell_eq_quotient_cell n hn w)
  exact fun g hg => heq.le (quotient_exchange n hn a w hg)

/-- The Tits system on the original binary triality carrier and Borel. -/
@[expose] def titsSystem : TitsSystem (X := Carrier P) where
  B := borel P
  N := normalizerCandidate P rfl
  generate := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    exact RelativeNormalizer.borel_sup_normalizer n hn
  S := Set.range (RelativeNormalizer.simpleReflection n hn)
  finite_S := by
    apply ((Set.finite_singleton (RelativeNormalizer.simpleReflection n hn .central)).insert
      (RelativeNormalizer.simpleReflection n hn .arms)).subset
    intro w hw
    rcases (RelativeNormalizer.mem_simpleReflection_range n hn w).mp hw with h | h
    · exact h.symm ▸ Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (by simp [h])
  involutions := by
    rintro _ ⟨a, rfl⟩
    exact RelativeNormalizer.simpleReflection_involution n hn a
  quotient_generate := RelativeNormalizer.simpleReflection_generate n hn
  exchange := by exact quotient_full_exchange n hn
  nontrivial := by
    rintro _ ⟨a, rfl⟩
    exact quotient_nontrivial n hn a

@[simp] theorem titsSystem_B : (titsSystem n hn).B = borel P := rfl

@[simp] theorem titsSystem_N : (titsSystem n hn).N = normalizerCandidate P rfl := rfl

/-- The relative Weyl group of the constructed Tits system is the actual
normalizer quotient, identified with the twelve-element dihedral group. -/
def weylEquiv : DihedralGroup 6 ≃*
    (titsSystem n hn).N ⧸ ((titsSystem n hn).B ⊓ (titsSystem n hn).N).subgroupOf
      (titsSystem n hn).N := RelativeNormalizer.quotientEquiv n hn

/-- The arm-orbit and central-orbit generators in the actual Weyl quotient. -/
@[expose] def simpleReflection (a : Node) :
    (titsSystem n hn).N ⧸ ((titsSystem n hn).B ⊓ (titsSystem n hn).N).subgroupOf
      (titsSystem n hn).N := weylEquiv n hn (relativeReflection a)

@[simp] theorem titsSystem_S :
    (titsSystem n hn).S = Set.range (simpleReflection n hn) := by rfl

theorem simpleReflection_ne (a b : Node) (hab : a ≠ b) :
    simpleReflection n hn a ≠ simpleReflection n hn b :=
  RelativeNormalizer.simpleReflection_ne n hn a b hab

theorem simpleReflection_involution (a : Node) :
    simpleReflection n hn a ≠ 1 ∧ simpleReflection n hn a ^ 2 = 1 :=
  RelativeNormalizer.simpleReflection_involution n hn a

theorem mem_titsSystem_S_iff (w) : w ∈ (titsSystem n hn).S ↔
    w = simpleReflection n hn .arms ∨ w = simpleReflection n hn .central :=
  RelativeNormalizer.mem_simpleReflection_range n hn w

theorem weyl_card : Nat.card ((titsSystem n hn).N ⧸
    ((titsSystem n hn).B ⊓ (titsSystem n hn).N).subgroupOf (titsSystem n hn).N) = 12 :=
  RelativeNormalizer.quotient_card n hn

theorem orderOf_simpleReflection_product :
    orderOf (simpleReflection n hn .arms * simpleReflection n hn .central) = 6 := by
  change orderOf (weylEquiv n hn (relativeReflection .arms) *
    weylEquiv n hn (relativeReflection .central)) = 6
  rw [← map_mul]
  exact (orderOf_injective (weylEquiv n hn).toMonoidHom (weylEquiv n hn).injective _).trans (by
    simpa only [relativeReflection, DihedralGroup.sr_mul_sr, sub_zero] using
      (DihedralGroup.orderOf_r_one (n := 6)))

/-- The Tits-system cells are the original double cosets of the actual folded
Geck representatives, with the same fixed-point normal forms. -/
theorem cell_eq_bruhatCell (w : DihedralGroup 6) :
    cell P rfl w = (titsSystem n hn).bruhatCell (weylEquiv n hn w) :=
  RelativeNormalizer.cell_eq_quotient_cell n hn w

/-- The marked simple quotient element is represented by the original folded
root word, not by an unrelated abstract involution. -/
theorem simpleReflection_eq_mk (a : Node) :
    simpleReflection n hn a =
      QuotientGroup.mk' (((titsSystem n hn).B ⊓ (titsSystem n hn).N).subgroupOf
        (titsSystem n hn).N)
        ⟨simpleRepresentative P rfl a, simpleRepresentative_mem_normalizer P rfl a⟩ := by
  change QuotientGroup.mk' _ (RelativeNormalizer.normalizerLift P rfl (relativeReflection a)) = _
  apply congrArg (QuotientGroup.mk' _)
  exact Subtype.ext (weylRepresentative_simple P rfl a)

end Binary
end Triality.Standard.ConcreteBruhat
end

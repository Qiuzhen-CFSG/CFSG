module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.EarlierGeometry
/-!
# Reduction of the complement intersection to the two finite modules

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.4.10, first proof paragraph, printed p.1010; 14.4.2(5), p.1006;
and the canonical commutator form of 12.8.8(2), p.851.

The canonical form is alternating, nondegenerate and invariant under the
actual actor quotient. These properties follow from its values on lifts,
not from choosing an unrelated coordinate form. The actual elementary
order-eight image and Sylow subgroup give data for a finite tensor calculation.
Relative normality is retained in the full point centralizer; the actor's
containment there is proved separately so that subgroupOf loses no elements.

The first moved plane meets the chosen cubic-translate complement in exactly
the line on the cubic translate of the point. Thus a finite calculation on
that one vector gives the literal source intersection bound, and then X₁ ∈ Y.
ComplementIntersectionCalculation is the remaining mathematical obligation,
not an asserted theorem. The natural and deleted constituent calculations
must both be supplied before the source intersection result is complete.
-/

@[expose] public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The tensor space with the source order of the two factors. -/
abbrev IntersectionSpace (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :=
  BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V

/-- Coordinate data for the finite calculation. Every field is constructed
from EarlierGeometry, CanonicalForm and the chosen SelectedConstituent below.
No position for the component intersection is imposed. -/
structure ComplementIntersectionData (σ : Representation (ZMod 2) D V) where
  sylow : Sylow 2 (Three × D)
  actor : Subgroup (Three × D)
  actor_le_sylow : actor ≤ sylow
  actor_elementary : IsElementaryAbelian 2 actor
  actor_card : Nat.card actor = 8
  point : IntersectionSpace V
  point_ne_zero : point ≠ 0
  point_fixed : ∀ a ∈ sylow, sourceTensorAction σ a point = point
  actor_normal : (actor.subgroupOf (subspaceKernel (sourceTensorAction σ)
    (Submodule.span (ZMod 2) {point}) ⊤)).Normal
  form : LinearMap.BilinForm (ZMod 2) (IntersectionSpace V)
  form_alt : form.IsAlt
  form_nondegenerate : form.Nondegenerate
  form_invariant : ∀ a u v,
    form (sourceTensorAction σ a u) (sourceTensorAction σ a v) = form u v
  element : Three × D
  element_mem : element ∈ actor
  element_ne_one : element ≠ 1
  element_centralizes : element ∈ centralizer
    (((⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) : Set (Three × D))
  firstSpace : Submodule (ZMod 2) (IntersectionSpace V)
  secondSpace : Submodule (ZMod 2) (IntersectionSpace V)
  first_eq_range : firstSpace = LinearMap.range
    (sourceTensorAction σ element - LinearMap.id)
  second_eq_translate : secondSpace = firstSpace.map (sourceTensorAction σ (cubicActor D))
  isCompl : IsCompl firstSpace secondSpace
  point_mem_first : point ∈ firstSpace

/-- The one-vector calculation to be proved separately for each genuine
constituent model. This definition does not assert its truth. -/
def ComplementIntersectionCalculation (σ : Representation (ZMod 2) D V) : Prop :=
  ∀ d : ComplementIntersectionData σ,
    sourceTensorAction σ (cubicActor D) d.point ∈
      subspaceCommutator (sourceTensorAction σ)
        ((Submodule.span (ZMod 2) {d.point}).orthogonalBilin d.form ⊓ d.secondSpace)
        (d.actor ⊓ (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))

/-- Relative normality in the data concerns the entire actor, since its
Sylow containment already implies that it fixes the point. -/
theorem ComplementIntersectionData.actor_le_pointCentralizer
    {σ : Representation (ZMod 2) D V} (d : ComplementIntersectionData σ) :
    d.actor ≤ subspaceKernel (sourceTensorAction σ)
      (Submodule.span (ZMod 2) {d.point}) ⊤ := by
  intro a ha
  refine ⟨Subgroup.mem_top _, ?_⟩
  intro w hw
  obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_smul, d.point_fixed a (d.actor_le_sylow ha)]

namespace CaseFiveCoordinates
variable {G : Type*} [Group G] {H U : Subgroup G}
  (c : CaseFiveCoordinates hAD (V := V) H U)

private theorem binary_eq_of_zero_iff {a b : ZMod 2} (h : a = 0 ↔ b = 0) : a = b := by
  have hb : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hb a with rfl | rfl <;> rcases hb b with rfl | rfl <;> simp_all

/-- Self-commutation makes the canonical form alternating. -/
theorem CanonicalForm.alternating (B : c.CanonicalForm) : B.form.IsAlt := by
  intro v
  obtain ⟨u, rfl⟩ := c.quotientMap_surjective (Multiplicative.ofAdd v)
  exact (B.commutes_iff u u).mpr (Commute.refl u)

/-- Commutation is symmetric, and the binary zero test determines each value. -/
theorem CanonicalForm.symmetric (B : c.CanonicalForm) (v w : IntersectionSpace V) :
    B.form v w = B.form w v := by
  obtain ⟨u, hu⟩ := c.quotientMap_surjective (Multiplicative.ofAdd v)
  obtain ⟨z, hz⟩ := c.quotientMap_surjective (Multiplicative.ofAdd w)
  have huv : (c.quotientMap u).toAdd = v := congrArg Multiplicative.toAdd hu
  have hzw : (c.quotientMap z).toAdd = w := congrArg Multiplicative.toAdd hz
  rw [← huv, ← hzw]
  exact binary_eq_of_zero_iff ((B.commutes_iff u z).trans
    (commute_iff_eq u z |>.trans (eq_comm.trans (commute_iff_eq z u).symm)) |>.trans
      (B.commutes_iff z u).symm)

/-- A lift orthogonal to every lift is central and hence zero in U/Z(U). -/
theorem CanonicalForm.nondegenerate (B : c.CanonicalForm) : B.form.Nondegenerate := by
  have hl : ∀ v, (∀ w, B.form v w = 0) → v = 0 := by
    intro v hv
    obtain ⟨u, hu⟩ := c.quotientMap_surjective (Multiplicative.ofAdd v)
    have huv : (c.quotientMap u).toAdd = v := congrArg Multiplicative.toAdd hu
    have hz : u ∈ center U := by
      rw [mem_center_iff]
      intro w
      have hh := hv (c.quotientMap w).toAdd
      rw [← huv] at hh
      exact ((B.commutes_iff u w).mp hh).symm.eq
    have hk : c.quotientMap u = 1 := by
      change u ∈ c.quotientMap.ker
      rw [c.quotientMap_ker]
      exact hz
    rw [hk] at huv
    exact huv.symm
  exact ⟨hl, fun w hw => hl w (fun v => (B.symmetric c w v).trans (hw v))⟩

/-- Actual conjugation preserves commutation, hence preserves the canonical
form under every element of the published actor quotient. -/
theorem CanonicalForm.invariant (B : c.CanonicalForm) (a : Three × D)
    (v w : IntersectionSpace V) :
    B.form (sourceTensorAction c.constituent a v)
      (sourceTensorAction c.constituent a w) = B.form v w := by
  obtain ⟨aH, ha⟩ := (QuotientGroup.mk'_surjective (pCore 2 H)) (c.actor.symm a)
  have hea : c.actor (QuotientGroup.mk' (pCore 2 H) aH) = a := by
    rw [ha, c.actor.apply_symm_apply]
  obtain ⟨u, hu⟩ := c.quotientMap_surjective (Multiplicative.ofAdd v)
  obtain ⟨z, hz⟩ := c.quotientMap_surjective (Multiplicative.ofAdd w)
  have huv : (c.quotientMap u).toAdd = v := congrArg Multiplicative.toAdd hu
  have hzw : (c.quotientMap z).toAdd = w := congrArg Multiplicative.toAdd hz
  let u' : U := ⟨(aH : G) * u * (aH : G)⁻¹,
    le_normalizer_iff.mp c.H_normalizes_U aH aH.property u u.property⟩
  let z' : U := ⟨(aH : G) * z * (aH : G)⁻¹,
    le_normalizer_iff.mp c.H_normalizes_U aH aH.property z z.property⟩
  have he (t : U) : (c.quotientMap ⟨(aH : G) * t * (aH : G)⁻¹,
      le_normalizer_iff.mp c.H_normalizes_U aH aH.property t t.property⟩).toAdd =
      sourceTensorAction c.constituent a (c.quotientMap t).toAdd := by
    have hh := congrArg Multiplicative.toAdd (c.equivariant aH t)
    rwa [hea] at hh
  rw [← huv, ← hzw, ← he u, ← he z]
  apply binary_eq_of_zero_iff
  rw [B.commutes_iff, B.commutes_iff]
  change Commute u' z' ↔ Commute u z
  simp only [commute_iff_eq, Subtype.ext_iff]
  change (aH : G) * u * (aH : G)⁻¹ * ((aH : G) * z * (aH : G)⁻¹) =
    (aH : G) * z * (aH : G)⁻¹ * ((aH : G) * u * (aH : G)⁻¹) ↔ _
  change (MulAut.conj (aH : G)) (u : G) * (MulAut.conj (aH : G)) (z : G) =
    (MulAut.conj (aH : G)) (z : G) * (MulAut.conj (aH : G)) (u : G) ↔
      (u : G) * (z : G) = (z : G) * (u : G)
  rw [← map_mul, ← map_mul]
  exact (MulAut.conj (aH : G)).injective.eq_iff

/-- The literal quotient image of the supplied Sylow subgroup is Sylow. -/
theorem EarlierGeometry.actor_sylow [Finite G] {T P : Subgroup G} {g : G}
    (h : c.EarlierGeometry T P g) :
    ∃ S : Sylow 2 (Three × D), (S : Subgroup (Three × D)) = c.actorImage T := by
  obtain ⟨S, hS⟩ := h.sylow
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  refine ⟨Q.mapSurjective (f := c.actor.toMonoidHom) c.actor.surjective, ?_⟩
  change ((S : Subgroup H).map (QuotientGroup.mk' (pCore 2 H))).map c.actor.toMonoidHom = _
  change _ = ((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).map c.actor.toMonoidHom
  rw [← hS, ← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective]

/-- Elementary abelianness passes through the actual actor equivalence. -/
theorem EarlierGeometry.actor_elementary {T P : Subgroup G} {g : G}
    (h : c.EarlierGeometry T P g) :
    IsElementaryAbelian 2 (c.actorImage (conjugateLayer U P g)) := by
  let := h.conjugate_elementary
  exact IsElementaryAbelian.map c.actor.toMonoidHom

/-- The actor equivalence preserves the literal order-eight star image. -/
theorem EarlierGeometry.actor_card {T P : Subgroup G} {g : G}
    (h : c.EarlierGeometry T P g) : Nat.card (c.actorImage (conjugateLayer U P g)) = 8 := by
  rw [actorImage, card_map_of_injective c.actor.injective, h.conjugate_card]

/-- Complementarity identifies the intersection with the cubic-translate line. -/
theorem SelectedConstituent.cubicPlane_intersection {T P : Subgroup G} {g : G}
    (s : c.SelectedConstituent T P g) (v : IntersectionSpace V) (hv : v ∈ s.firstSpace) :
    cubicPlane c.constituent v ⊓ s.secondSpace =
      Submodule.span (ZMod 2) {sourceTensorAction c.constituent (cubicActor D) v} := by
  let r := sourceTensorAction c.constituent (cubicActor D)
  have hr : r v ∈ s.secondSpace := by
    rw [s.second_eq_translate]
    exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  apply le_antisymm
  · intro w hw
    obtain ⟨a, b, he⟩ := Submodule.mem_span_pair.mp hw.1
    have hfirst : a • v ∈ s.firstSpace := s.firstSpace.smul_mem a hv
    have hsecond : a • v ∈ s.secondSpace := by
      have hh := s.secondSpace.sub_mem hw.2 (s.secondSpace.smul_mem b hr)
      rw [← he] at hh
      simpa only [r, add_sub_cancel_right] using hh
    have hz : a • v = 0 := by
      have hh : a • v ∈ s.firstSpace ⊓ s.secondSpace := ⟨hfirst, hsecond⟩
      rwa [s.isCompl.inf_eq_bot, Submodule.mem_bot] at hh
    rw [← he, hz, zero_add]
    exact Submodule.smul_mem _ b (Submodule.mem_span_singleton_self _)
  · apply Submodule.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    exact ⟨Submodule.subset_span (Or.inr rfl), hr⟩

/-- Application to the actual first moved subgroup and source quotient point. -/
theorem SelectedConstituent.first_intersection_line [Finite G]
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (s : c.SelectedConstituent T P g) (v : IntersectionSpace V)
    (hv : v ∈ c.image P) (hspan : c.image P = Submodule.span (ZMod 2) {v}) :
    c.image (movedSpace P (first H)) ⊓ s.secondSpace =
      Submodule.span (ZMod 2) {sourceTensorAction c.constituent (cubicActor D) v} := by
  rw [c.first_image_eq_cubicPlane h.point_le_U v hspan]
  exact s.cubicPlane_intersection c v (s.fixed_le_first (s.point_le_fixed hv))

/-- All abstract finite-calculation premises are discharged from the literal
source data. The component marking is the independent finite-image input. -/
noncomputable def EarlierGeometry.intersectionData [Finite G]
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (B : c.CanonicalForm) (s : c.SelectedConstituent T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))
    (v : IntersectionSpace V) (hv : v ∈ c.image P) (hv0 : v ≠ 0)
    (hspan : c.image P = Submodule.span (ZMod 2) {v}) :
    ComplementIntersectionData c.constituent where
  sylow := Classical.choose (h.actor_sylow c)
  actor := c.actorImage (conjugateLayer U P g)
  actor_le_sylow := by
    rw [Classical.choose_spec (h.actor_sylow c)]
    exact c.actorImage_mono h.conjugate_le_T
  actor_elementary := h.actor_elementary c
  actor_card := h.actor_card c
  point := v
  point_ne_zero := hv0
  point_fixed := by
    intro a ha
    change a ∈ ((Classical.choose (h.actor_sylow c) : Sylow 2 (Three × D)) : Subgroup (Three × D)) at ha
    rw [Classical.choose_spec (h.actor_sylow c)] at ha
    exact h.point_fixed c hv ⟨a, ha⟩
  actor_normal := by
    have hh := h.conjugate_normal
    change ((c.actorImage (conjugateLayer U P g)).subgroupOf
      (subspaceKernel (sourceTensorAction c.constituent) (c.image P) ⊤)).Normal at hh
    rwa [hspan] at hh
  form := B.form
  form_alt := B.alternating c
  form_nondegenerate := B.nondegenerate c
  form_invariant := B.invariant c
  element := c.actor s.element
  element_mem := mem_map.mpr ⟨s.element, s.element_mem, rfl⟩
  element_ne_one := by
    intro he
    exact s.element_ne_one (c.actor.injective (he.trans c.actor.map_one.symm))
  element_centralizes := by
    rw [← hK]
    apply mem_centralizer_iff.mpr
    rintro _ ⟨k, hk, rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg c.actor (mem_centralizer_iff.mp s.element_centralizes k hk)
  firstSpace := s.firstSpace
  secondSpace := s.secondSpace
  first_eq_range := s.first_eq_range
  second_eq_translate := s.second_eq_translate
  isCompl := s.isCompl
  point_mem_first := s.fixed_le_first (s.point_le_fixed hv)

/-- Conditional source assembly: the one-vector model calculation gives
the exact displayed intersection inequality in 14.4.10. -/
theorem EarlierGeometry.intersection_of_calculation [Finite G]
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (B : c.CanonicalForm) (s : c.SelectedConstituent T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))
    (hcalc : ComplementIntersectionCalculation c.constituent) :
    c.image (movedSpace P (first H)) ⊓ s.secondSpace ≤
      subspaceCommutator (sourceTensorAction c.constituent)
        (c.image (centralLayer U P) ⊓ s.secondSpace)
        (c.actorImage (conjugateLayer U P g) ⊓ c.actorImage (component H)) := by
  have hne : c.image P ≠ ⊥ := by
    intro he
    have hh := h.point_rank
    rw [he, finrank_bot] at hh
    omega
  obtain ⟨v, hv, hv0⟩ := (c.image P).ne_bot_iff.mp hne
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one h.point_rank hv hv0
  rw [s.first_intersection_line c h v hv hspan]
  apply Submodule.span_le.mpr
  apply Set.singleton_subset_iff.mpr
  have hh := hcalc (h.intersectionData c B s hK v hv hv0 hspan)
  change sourceTensorAction c.constituent (cubicActor D) v ∈
    subspaceCommutator (sourceTensorAction c.constituent)
      ((Submodule.span (ZMod 2) {v}).orthogonalBilin B.form ⊓ s.secondSpace)
      (c.actorImage (conjugateLayer U P g) ⊓
        (⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) at hh
  rwa [h.centralLayer_image c B, hK, hspan]

/-- Consumer of the same finite calculation, through the proved quotient
intersection and extraspecial central-kernel lift. -/
theorem EarlierGeometry.first_mem_Y_of_calculation [Finite G] [IsExtraspecial 2 U]
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (B : c.CanonicalForm) (s : c.SelectedConstituent T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))
    (hcalc : ComplementIntersectionCalculation c.constituent) :
    first H ∈ YFamily H T P (intersectionLayer U P g) :=
  h.first_mem_Y_of_intersection c s (h.intersection_of_calculation c B s hK hcalc)

end CaseFiveCoordinates
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end

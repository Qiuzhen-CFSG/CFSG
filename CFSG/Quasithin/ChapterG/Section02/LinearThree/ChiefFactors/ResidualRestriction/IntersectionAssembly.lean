module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.Sections
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.BinaryConstituents
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
public import Theory.GroupTheory.NormalizedIntersectionImage
public import Theory.Representation.PSL3.PointParabolicCoinvariants

/-!
# Which source constituents survive intersection with L₁

Commutators lie in intersections because the source core normalizes L₁.
The explicit model coinvariants therefore show that the whole natural V
and every upper natural layer survive. In the binary dual layer all
annihilator planes survive, with only central scalar quotients possibly lost.
Over larger fields both marked layers survive in their entirety, including
all noncentral scalar constituents. Every map is the original quotient map.

Source: Aschbacher–Smith, G.2.5(4–8), printed pp.335–336.
The earlier U≤T, I=LU and marked layer conclusions remain explicit.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.IntersectionAssembly
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
  {d : Hypothesis D F n g h}

omit [Finite G] in
private theorem local_le_L : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left

omit [Finite G] in
private theorem surjective_restriction_le {A J : Subgroup G} {M : Type*} [AddCommGroup M]
    (e : A ≃* Multiplicative M)
    (he : Function.Surjective (NormalizedIntersection.restriction J A e.toMonoidHom)) :
    A ≤ J := by
  intro v hv
  obtain ⟨w, hw⟩ := he (e ⟨v,hv⟩)
  have hh : (w : G) = v := congrArg Subtype.val (e.injective hw)
  exact hh ▸ w.property.1

include d in
private theorem core_normalizes (hUT : D.U ≤ D.T) (hILU : I D g h = D.L ⊔ D.U)
    {A : Subgroup G} (hA : A ≤ S D g h) : A ≤ normalizer (D.L₁ : Set G) :=
  hA.trans (core_normalizes_residual d hUT hILU)

include d in
private theorem V_normalizes (hUT : D.U ≤ D.T) (hILU : I D g h = D.L ⊔ D.U) :
    D.V ≤ normalizer (D.L₁ : Set G) :=
  core_normalizes (d := d) hUT hILU ((d.central_first hUT (hILU ▸ le_sup_left)).trans inf_le_left)

/-- The literal section maps to the whole source layer when its intersection
projection is surjective. -/
noncomputable def fullIntersectionEquiv (J A B : Subgroup G) [(B.subgroupOf A).Normal]
    (hf : Function.Surjective (intersectionProjection J A B)) :
    ((J ⊓ A : Subgroup G) ⧸ B.subgroupOf (J ⊓ A)) ≃* (A ⧸ B.subgroupOf A) :=
  (QuotientGroup.quotientMulEquivOfEq (intersectionProjection_kernel J A B).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hf)

omit [Finite G] in
@[simp] theorem fullIntersectionEquiv_mk (J A B : Subgroup G) [(B.subgroupOf A).Normal]
    (hf : Function.Surjective (intersectionProjection J A B)) (x : (J ⊓ A : Subgroup G)) :
    fullIntersectionEquiv J A B hf (QuotientGroup.mk' (B.subgroupOf (J ⊓ A)) x) =
      intersectionProjection J A B x := rfl

/-- Literal ambient conjugation preserves the intersection. -/
def intersectionConjugate (J A : Subgroup G) (hJA : J ≤ normalizer (A : Set G))
    (l : J) (x : (J ⊓ A : Subgroup G)) : (J ⊓ A : Subgroup G) :=
  ⟨(l : G) * x * (l : G)⁻¹,
    J.mul_mem (J.mul_mem l.property x.property.1) (J.inv_mem l.property),
    (mem_normalizer_iff.mp (hJA l.property) x).mp x.property.2⟩

namespace Binary
open BinaryConstituents Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents
variable {d : Hypothesis D (ZMod 2) 1 g h} (a : PointAlignment d)

include a in
/-- No part of the original natural module is lost on intersection with L₁. -/
theorem V_le_residual (hUT : D.U ≤ D.T) (hILU : I D g h = D.L ⊔ D.U) : D.V ≤ D.L₁ := by
  apply surjective_restriction_le (sourceCoordinates a)
  apply NormalizedIntersection.surjective_of_differences D.L₁ D.V
    (local_le_L.trans (normalizes_of_span D d.span_eq)) (V_normalizes (d := d) hUT hILU)
    (sourceCoordinates a).toMonoidHom (sourceCoordinates a).surjective
    (fun l => natural (ResidualRestriction.Binary.localProjection a l)) (source_equivariant a)
  intro C hc
  apply Matrix.PSL3.PointParabolicCoinvariants.binary_natural_full C
  intro x v
  obtain ⟨l,rfl⟩ := ResidualRestriction.Binary.localProjection_surjective a x
  exact hc l v

variable [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal]
  {hLI : D.L ≤ I D g h} {r s : ℕ} (c : MarkedLayers d hLI r s)

include a c in
/-- The upper natural layer is entirely present in the actual intersection. -/
theorem upper_projection_surjective (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) :
    Function.Surjective (intersectionProjection D.L₁ (S D g h) (S₃ D g h)) := by
  let e := upperCoordinates a c
  have he : Function.Surjective (e.toMonoidHom.comp
      (intersectionProjection D.L₁ (S D g h) (S₃ D g h))) := by
    apply NormalizedIntersection.surjective_of_differences D.L₁ (S D g h)
      (local_le_L.trans (hLI.trans (I_normalizes_core D g h)))
      (core_normalizes (d := d) hUT hILU le_rfl)
      (e.toMonoidHom.comp (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
      (fun l v i => natural (ResidualRestriction.Binary.localProjection a l) (v i))
      (fun l v => funext (upper_equivariant a c l v))
    intro C hc
    apply Matrix.PSL3.PointParabolicCoinvariants.binary_natural_copies_full C
    intro x v
    obtain ⟨l,rfl⟩ := ResidualRestriction.Binary.localProjection_surjective a x
    exact hc l v
  intro q
  obtain ⟨v,hv⟩ := he (e q)
  exact ⟨v,e.injective hv⟩

/-- All annihilator planes survive. Only central scalar quotients can be omitted. -/
theorem lower_planes_survive (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) (hS₃ : S₃ D g h ≤ S D g h) :
    (lowerProjection a c).ker ≤
      (intersectionProjection D.L₁ (S₃ D g h) (S₂ D g h)).range := by
  intro q hq
  let e := lowerCoordinates a c
  let f := e.toMonoidHom.comp (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)))
  have hd := NormalizedIntersection.difference_mem D.L₁ (S₃ D g h)
    (local_le_L.trans c.lower_normalizes) (core_normalizes (d := d) hUT hILU hS₃)
    f (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (fun l v i => dual (ResidualRestriction.Binary.localProjection a l) (v i))
    (fun l v => funext (lower_equivariant a c l v))
  have hm : (e q).toAdd ∈ (NormalizedIntersection.restriction D.L₁ (S₃ D g h) f).range.toAddSubgroup' := by
    apply Matrix.PSL3.PointParabolicCoinvariants.binary_dual_planes_mem
    · intro x v
      obtain ⟨l,rfl⟩ := ResidualRestriction.Binary.localProjection_surjective a x
      exact hd l v
    · intro i
      exact congrFun hq i
  obtain ⟨v,hv⟩ := hm
  exact ⟨v,e.injective hv⟩

/-- The retained plane subspace has precisely the previously computed cubic action
coordinates; its inclusion uses the literal intersection quotient image. -/
def lowerPlaneEquiv (hUT : D.U ≤ D.T) (hILU : I D g h = D.L ⊔ D.U)
    (hS₃ : S₃ D g h ≤ S D g h) :
    (lowerProjection a c).ker.subgroupOf
      (intersectionProjection D.L₁ (S₃ D g h) (S₂ D g h)).range ≃*
      Multiplicative (Fin s → Two) :=
  (subgroupOfEquivOfLe (lower_planes_survive a c hUT hILU hS₃)).trans (lowerKernelEquiv a c)
/-- The original upper intersection section inherits the full natural coordinates. -/
noncomputable def upperSectionCoordinates (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) :
    ((D.L₁ ⊓ S D g h : Subgroup G) ⧸ (S₃ D g h).subgroupOf (D.L₁ ⊓ S D g h)) ≃*
      Multiplicative (Fin r → Three) :=
  (fullIntersectionEquiv _ _ _ (upper_projection_surjective a c hUT hILU)).trans
    (upperCoordinates a c)

/-- These are coordinates for actual ambient conjugation, on the original quotient. -/
theorem upperSectionCoordinates_conjugate (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) (l : D.L₁) (x : (D.L₁ ⊓ S D g h : Subgroup G)) (i : Fin r) :
    (upperSectionCoordinates a c hUT hILU (QuotientGroup.mk'
      ((S₃ D g h).subgroupOf (D.L₁ ⊓ S D g h))
      (intersectionConjugate D.L₁ (S D g h)
        ((show D.L₁ ≤ D.L from (map_subtype_le _).trans inf_le_left).trans
          (hLI.trans (I_normalizes_core D g h))) l x))).toAdd i =
      natural (ResidualRestriction.Binary.localProjection a l)
        ((upperSectionCoordinates a c hUT hILU (QuotientGroup.mk'
          ((S₃ D g h).subgroupOf (D.L₁ ⊓ S D g h)) x)).toAdd i) :=
  upper_equivariant a c l (inclusion inf_le_right x) i

end Binary

namespace Larger
open ScalarConstituents ScalarConstituents.Irreducibility
variable (a : PointAlignment d)

include d in
private theorem scalar_unit (hn : 1 < n) : ∃ u : Fˣ, (u : F) ≠ 1 := by
  have hc : 4 ≤ Nat.card F := by
    rw [d.field_card]
    have hh : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega : 2 ≤ n)
    exact hh
  have hu : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨u,hu⟩ := exists_ne (1 : Fˣ)
  exact ⟨u,fun h => hu (Units.ext h)⟩

include a in
/-- Both the scalar line and the natural quotient survive in L₁. -/
theorem V_le_residual (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) : D.V ≤ D.L₁ := by
  obtain ⟨u,hu⟩ := scalar_unit (d := d) hn
  apply surjective_restriction_le (alignedCoordinates a)
  apply NormalizedIntersection.surjective_of_differences D.L₁ D.V
    (local_le_L.trans (normalizes_of_span D d.span_eq)) (V_normalizes (d := d) hUT hILU)
    (alignedCoordinates a).toMonoidHom (alignedCoordinates a).surjective
    (fun l v => (localProjection a hn l).val.val *ᵥ v) (aligned_natural_action a hn)
  intro C hc
  apply Matrix.PSL3.PointParabolicCoinvariants.natural_full u hu C
  intro x v
  obtain ⟨l,rfl⟩ := localProjection_surjective a hn x
  exact hc l v

variable [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal]
  {hLI : D.L ≤ I D g h} {r s : ℕ} (c : MarkedLayers d hLI r s)

include a c in
/-- No upper natural constituent, including the scalar line, is lost. -/
theorem upper_projection_surjective (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) :
    Function.Surjective (intersectionProjection D.L₁ (S D g h) (S₃ D g h)) := by
  obtain ⟨u,hu⟩ := scalar_unit (d := d) hn
  let e := upperCoordinates a c
  have he : Function.Surjective (e.toMonoidHom.comp
      (intersectionProjection D.L₁ (S D g h) (S₃ D g h))) := by
    apply NormalizedIntersection.surjective_of_differences D.L₁ (S D g h)
      (local_le_L.trans (hLI.trans (I_normalizes_core D g h)))
      (core_normalizes (d := d) hUT hILU le_rfl)
      (e.toMonoidHom.comp (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h))))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
      (fun l v i => (localProjection a hn l).val.val *ᵥ v i)
      (fun l v => funext (upper_action a c hn l v))
    intro C hc
    apply Matrix.PSL3.PointParabolicCoinvariants.natural_copies_full u hu C
    intro x v
    obtain ⟨l,rfl⟩ := localProjection_surjective a hn x
    exact hc l v
  intro q
  obtain ⟨v,hv⟩ := he (e q)
  exact ⟨v,e.injective hv⟩

include a c in
/-- No dual constituent, including its scalar quotient, is lost. -/
theorem lower_projection_surjective (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) (hS₃ : S₃ D g h ≤ S D g h) :
    Function.Surjective (intersectionProjection D.L₁ (S₃ D g h) (S₂ D g h)) := by
  obtain ⟨u,hu⟩ := scalar_unit (d := d) hn
  let e := lowerCoordinates a c
  have he : Function.Surjective (e.toMonoidHom.comp
      (intersectionProjection D.L₁ (S₃ D g h) (S₂ D g h))) := by
    apply NormalizedIntersection.surjective_of_differences D.L₁ (S₃ D g h)
      (local_le_L.trans c.lower_normalizes) (core_normalizes (d := d) hUT hILU hS₃)
      (e.toMonoidHom.comp (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h))))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
      (fun l v i => (localProjection a hn l).val⁻¹.val.transpose *ᵥ v i)
      (fun l v => funext (lower_action a c hn l v))
    intro C hc
    apply Matrix.PSL3.PointParabolicCoinvariants.dual_copies_full u hu C
    intro x v
    obtain ⟨l,rfl⟩ := localProjection_surjective a hn x
    exact hc l v
  intro q
  obtain ⟨v,hv⟩ := he (e q)
  exact ⟨v,e.injective hv⟩
/-- All upper scalar and plane coordinates on the actual intersection section. -/
noncomputable def upperSectionCoordinates (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) :
    ((D.L₁ ⊓ S D g h : Subgroup G) ⧸ (S₃ D g h).subgroupOf (D.L₁ ⊓ S D g h)) ≃*
      Multiplicative (Fin r → Fin 3 → F) :=
  (fullIntersectionEquiv _ _ _ (upper_projection_surjective a c hn hUT hILU)).trans
    (upperCoordinates a c)

/-- All dual plane and scalar coordinates on the actual intersection section. -/
noncomputable def lowerSectionCoordinates (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) (hS₃ : S₃ D g h ≤ S D g h) :
    ((D.L₁ ⊓ S₃ D g h : Subgroup G) ⧸ (S₂ D g h).subgroupOf (D.L₁ ⊓ S₃ D g h)) ≃*
      Multiplicative (Fin s → Fin 3 → F) :=
  (fullIntersectionEquiv _ _ _ (lower_projection_surjective a c hn hUT hILU hS₃)).trans
    (lowerCoordinates a c)

/-- Upper intersection coordinates intertwine literal conjugation with the full parabolic action. -/
theorem upperSectionCoordinates_conjugate (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) (l : D.L₁) (x : (D.L₁ ⊓ S D g h : Subgroup G)) (i : Fin r) :
    (upperSectionCoordinates a c hn hUT hILU (QuotientGroup.mk'
      ((S₃ D g h).subgroupOf (D.L₁ ⊓ S D g h))
      (intersectionConjugate D.L₁ (S D g h)
        ((show D.L₁ ≤ D.L from (map_subtype_le _).trans inf_le_left).trans
          (hLI.trans (I_normalizes_core D g h))) l x))).toAdd i =
      (localProjection a hn l).val.val *ᵥ
        ((upperSectionCoordinates a c hn hUT hILU (QuotientGroup.mk'
          ((S₃ D g h).subgroupOf (D.L₁ ⊓ S D g h)) x)).toAdd i) :=
  upper_action a c hn l (inclusion inf_le_right x) i

/-- Lower intersection coordinates intertwine literal conjugation with the full dual action. -/
theorem lowerSectionCoordinates_conjugate (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) (hS₃ : S₃ D g h ≤ S D g h)
    (l : D.L₁) (x : (D.L₁ ⊓ S₃ D g h : Subgroup G)) (i : Fin s) :
    (lowerSectionCoordinates a c hn hUT hILU hS₃ (QuotientGroup.mk'
      ((S₂ D g h).subgroupOf (D.L₁ ⊓ S₃ D g h))
      (intersectionConjugate D.L₁ (S₃ D g h) ((show D.L₁ ≤ D.L from (map_subtype_le _).trans inf_le_left).trans c.lower_normalizes) l x))).toAdd i =
      (localProjection a hn l).val⁻¹.val.transpose *ᵥ
        ((lowerSectionCoordinates a c hn hUT hILU hS₃ (QuotientGroup.mk'
          ((S₂ D g h).subgroupOf (D.L₁ ⊓ S₃ D g h)) x)).toAdd i) :=
  lower_action a c hn l (inclusion inf_le_right x) i

end Larger
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.IntersectionAssembly

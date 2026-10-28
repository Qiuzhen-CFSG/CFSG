module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.HomogeneousFibres.Projection


/-!
# Binary scalar rigidity on coherently marked natural planes

A binary-linear endomorphism of the natural SL₂(F)-plane commuting with
both transvection families is scalar over F. This remains true over F₄.
Transport through actual additive and linear coordinates therefore realizes
every Levi-equivariant axis-group map as displacement by a fixed natural
line vector. Only the original natural submodule carries such line vectors;
no F-linear structure on the extension is used.

`NaturalPlaneCoordinates` records the isomorphisms, direct conjugation,
action equations and displacement formula needed for this transport. Its
construction from the same-orientation marking remains a separate obligation.
The scalar proof is adapted from the parent task's preserved
Scratch/LargeFieldComplements/Scalars.lean.
Source: Aschbacher–Smith B.4.9(1), printed pp.93–94, the homogeneous case.
-/

@[expose] public section

open Representation Matrix
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.Homogeneous
open QuasisimpleSource

private theorem upper_action (F : BinaryField) (a : F.Carrier) (v : Fin 2 → F.Carrier) :
    linearNatural F 2 (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
      zero_ne_one a) v = ![v 0 + a * v 1, v 1] := by
  change (Matrix.transvection (0 : Fin 2) 1 a).mulVec v = _
  ext i
  fin_cases i <;>
    simp [Matrix.transvection, mulVec, dotProduct, Fin.sum_univ_two]

private theorem lower_action (F : BinaryField) (a : F.Carrier) (v : Fin 2 → F.Carrier) :
    linearNatural F 2 (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0)
      one_ne_zero a) v = ![v 0, v 1 + a * v 0] := by
  change (Matrix.transvection (1 : Fin 2) 0 a).mulVec v = _
  ext i
  fin_cases i <;>
    simp [Matrix.transvection, mulVec, dotProduct, Fin.sum_univ_two]
  ac_rfl

/-- The binary commutant of the natural SL₂ action is exactly the defining
field of scalars; linearity over that field is a conclusion. -/
theorem natural_binary_endomorphism_scalar (F : BinaryField)
    (f : (Fin 2 → F.Carrier) →ₗ[ZMod 2] (Fin 2 → F.Carrier))
    (hf : ∀ g v, f (linearNatural F 2 g v) = linearNatural F 2 g (f v)) :
    ∃ c : F.Carrier, ∀ v, f v = c • v := by
  have hu (a : F.Carrier) :
      f ![a, 0] = ![a * (f ![0, 1]) 1, 0] := by
    have hh := hf (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
      zero_ne_one a) ![0, 1]
    rw [upper_action, upper_action] at hh
    simp only [cons_val_zero, cons_val_one, mul_one, zero_add] at hh
    have hs : (![a, 1] : Fin 2 → F.Carrier) = ![a, 0] + ![0, 1] := by
      ext i
      fin_cases i <;> simp
    rw [hs, map_add] at hh
    ext i
    fin_cases i
    · have hi := congrFun hh 0
      simp at hi ⊢
      linear_combination hi
    · have hi := congrFun hh 1
      simp at hi ⊢
      linear_combination hi
  have hl (a : F.Carrier) :
      f ![0, a] = ![0, a * (f ![1, 0]) 0] := by
    have hh := hf (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0)
      one_ne_zero a) ![1, 0]
    rw [lower_action, lower_action] at hh
    simp only [cons_val_zero, cons_val_one, mul_one, zero_add] at hh
    have hs : (![1, a] : Fin 2 → F.Carrier) = ![0, a] + ![1, 0] := by
      ext i
      fin_cases i <;> simp
    rw [hs, map_add] at hh
    ext i
    fin_cases i
    · have hi := congrFun hh 0
      simp at hi ⊢
      linear_combination hi
    · have hi := congrFun hh 1
      simp at hi ⊢
      linear_combination hi
  have hc : (f ![0, 1]) 1 = (f ![1, 0]) 0 := by
    simpa using congrFun (hl 1) 1
  refine ⟨(f ![1, 0]) 0, fun v => ?_⟩
  have hv : v = ![v 0, 0] + ![0, v 1] := by
    ext i
    fin_cases i <;> simp
  calc
    f v = f ![v 0, 0] + f ![0, v 1] := by rw [← map_add, ← hv]
    _ = (f ![1, 0]) 0 • v := by
      rw [hu (v 0), hl (v 1), hc]
      ext i
      fin_cases i <;> simp [mul_comm]


open Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Actual coordinates on the axis group and on the original fixed natural
plane. The same embedded SL₂ acts on both. Scalar line vectors lie only in
U; the extension V is not equipped with an F-module structure. -/
structure NaturalPlaneCoordinates
    (ρ : Representation (ZMod 2) G V) (K Q : Subgroup G)
    (N : Subrepresentation ρ) (F : BinaryField) where
  parameters : (Fin 2 → F.Carrier) ≃+ Additive Q
  plane : ↥(N.toSubmodule ⊓ fixedSpace ρ Q) ≃ₗ[ZMod 2] (Fin 2 → F.Carrier)
  actor : Matrix.SpecialLinearGroup (Fin 2) F.Carrier → G
  actor_mem : ∀ g, actor g ∈ K
  conjugate : ∀ g t,
    ((parameters (linearNatural F 2 g t)).toMul : G) =
      actor g * (parameters t).toMul * (actor g)⁻¹
  intertwines : ∀ g (w w' : ↥(N.toSubmodule ⊓ fixedSpace ρ Q)),
    (w' : V) = ρ (actor g) w → plane w' = linearNatural F 2 g (plane w)
  lineLift : F.Carrier → V
  lineLift_mem : ∀ c, lineLift c ∈ N.toSubmodule
  lineLift_fixed : ∀ c, lineLift c ∈ fixedSpace ρ K
  displacement : ∀ c t, ρ (parameters t).toMul (lineLift c) - lineLift c =
    (plane.symm (c • t) : V)

/-- Scalar rigidity realizes every equivariant map on the actual axis group
as displacement by the corresponding fixed vector of the original natural
submodule. All coordinate and action identifications remain explicit. -/
theorem realization_of_marked_planes
    {ρ : Representation (ZMod 2) G V} {K Q : Subgroup G}
    {N : Subrepresentation ρ} {F : BinaryField}
    (c : NaturalPlaneCoordinates ρ K Q N F) :
    NaturalDisplacementRealization ρ K Q N := by
  intro f hf
  let t : (Fin 2 → F.Carrier) →ₗ[ZMod 2] (Fin 2 → F.Carrier) :=
    (c.plane.toAddEquiv.toAddMonoidHom.comp
      (f.comp c.parameters.toAddMonoidHom)).toZModLinearMap 2
  have ht (g : Matrix.SpecialLinearGroup (Fin 2) F.Carrier) (w : Fin 2 → F.Carrier) :
      t (linearNatural F 2 g w) = linearNatural F 2 g (t w) := by
    change c.plane (f (c.parameters (linearNatural F 2 g w))) =
      linearNatural F 2 g (c.plane (f (c.parameters w)))
    apply c.intertwines
    exact hf (c.actor g) (c.actor_mem g) (c.parameters w).toMul
      (c.parameters (linearNatural F 2 g w)).toMul (c.conjugate g w)
  obtain ⟨b, hb⟩ := natural_binary_endomorphism_scalar F t ht
  refine ⟨c.lineLift b, c.lineLift_mem b, c.lineLift_fixed b, fun x => ?_⟩
  obtain ⟨w, hw⟩ := c.parameters.surjective (Additive.ofMul x)
  have he : f (Additive.ofMul x) = c.plane.symm (b • w) := by
    apply c.plane.injective
    rw [c.plane.apply_symm_apply]
    have hb' : c.plane (f (c.parameters w)) = b • w := hb w
    rwa [hw] at hb'
  have hx : (c.parameters w).toMul = x := congrArg Additive.toMul hw
  rw [he, ← c.displacement b w, hx]

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.Homogeneous

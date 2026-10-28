module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanActions

/-!
# Source root images detected by reflection-fixed Cartan factors

If a source reflection centralizes an actual conjugated root, its Cartan
inverted factor acts trivially on that root. The odd reflection product
therefore makes the fixed factor surject onto the entire root-action image.
The exact joint panel kernel then embeds one panel kernel in the opposite
panel image. Combining these maps yields the source field-unit divisibility;
LinearActions discharges the centralization premise on the octagonal row.

Source: Fong--Seitz I (1973), proof of (6H)(a), p.51. The maps use the same
finite marked quotient, full Cartan, and original ordered panel projections.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Conjugation on the actual root agrees with conjugation of its Cartan actor. -/
theorem rootAction_reflection (i j : Fin 2) (w : Weyl Q)
    (s : RootReflection Q split j)
    (hs : (s.val : X ⧸ Q.D) ∈ normalizer (rootAt Q split i w : Set (X ⧸ Q.D)))
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    rootAction Q split i w (simpleCartanAction Q split j h) =
      ((rootAt Q split i w).normalizerMonoidHom ⟨s.val,hs⟩)⁻¹ *
        rootAction Q split i w h * (rootAt Q split i w).normalizerMonoidHom ⟨s.val,hs⟩ := by
  let A := rootAt Q split i w
  let t : normalizer (A : Set (X ⧸ Q.D)) := ⟨s.val,hs⟩
  let f := inclusion (rootAt_torus_normalizes Q split i w)
  have he : f (simpleCartanAction Q split j h) = t⁻¹*f h*t := by
    apply Subtype.ext
    exact simpleCartanAction_apply Q split j s.val s.class_eq h
  change A.normalizerMonoidHom (f (simpleCartanAction Q split j h)) = _
  rw [he,map_mul,map_mul,map_inv]
  rfl

/-- The fixed-factor divisibility needs only equality of the induced actions;
this also applies when the reflection is nontrivial on a root's Frattini subgroup. -/
theorem rootAction_card_dvd_fixed_of_compatible (i j : Fin 2) (w : Weyl Q)
    (hcompat : ∀ h, rootAction Q split i w (simpleCartanAction Q split j h) =
      rootAction Q split i w h) :
    Nat.card (cartanPanelMap Q i).range ∣ Nat.card (reflectionFixed Q split j) := by
  have hinv (b : reflectionInverted Q split j) : rootAction Q split i w b.val = 1 := by
    obtain ⟨a,ha⟩ := (reflectionDisplacement_range Q split j).ge b.property
    rw [← ha]
    change rootAction Q split i w (a⁻¹*simpleCartanAction Q split j a) = 1
    rw [map_mul,map_inv,hcompat,inv_mul_cancel]
  have hf : Function.Surjective ((rootAction Q split i w).rangeRestrict.comp
      (reflectionFixed Q split j).subtype) := by
    rintro ⟨x,h,rfl⟩
    obtain ⟨⟨a,b⟩,hab⟩ := (cartanReflectionEquiv Q split j).surjective h
    refine ⟨a,?_⟩
    apply Subtype.ext
    change rootAction Q split i w a.val = rootAction Q split i w h
    change a.val*b.val = h at hab
    rw [← hab,map_mul,hinv,mul_one]
  rw [← Nat.card_congr (rootActionImageEquiv Q split i w).toEquiv]
  exact card_dvd_of_surjective _ hf

theorem rootAction_reflection_eq (i j : Fin 2) (w : Weyl Q)
    (s : RootReflection Q split j)
    (hs : (s.val : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)))
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    rootAction Q split i w (simpleCartanAction Q split j h) = rootAction Q split i w h := by
  let A := rootAt Q split i w
  let t : normalizer (A : Set (X ⧸ Q.D)) := ⟨s.val, Subgroup.centralizer_le_normalizer _ hs⟩
  let f := inclusion (rootAt_torus_normalizes Q split i w)
  have ht : A.normalizerMonoidHom t = 1 := by
    change t ∈ A.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hs
  have he : f (simpleCartanAction Q split j h) = t⁻¹*f h*t := by
    apply Subtype.ext
    exact simpleCartanAction_apply Q split j s.val s.class_eq h
  change A.normalizerMonoidHom (f (simpleCartanAction Q split j h)) = A.normalizerMonoidHom (f h)
  rw [he,map_mul,map_mul,map_inv,ht,inv_one,one_mul,mul_one]

theorem rootAction_displacement_eq_one (i j : Fin 2) (w : Weyl Q)
    (s : RootReflection Q split j)
    (hs : (s.val : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)))
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    rootAction Q split i w (reflectionDisplacement Q split j h) = 1 := by
  change rootAction Q split i w (h⁻¹*simpleCartanAction Q split j h) = 1
  rw [map_mul,map_inv,rootAction_reflection_eq Q split i j w s hs,inv_mul_cancel]

theorem rootAction_inverted_eq_one (i j : Fin 2) (w : Weyl Q)
    (s : RootReflection Q split j)
    (hs : (s.val : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)))
    (h : reflectionInverted Q split j) : rootAction Q split i w h.val = 1 := by
  have hh := (reflectionDisplacement_range Q split j).ge h.property
  obtain ⟨a,ha⟩ := hh
  rw [← ha]
  exact rootAction_displacement_eq_one Q split i j w s hs a

/-- Centralization by the actual reflection makes the fixed factor map
onto the entire root-action image, not merely a model subgroup. -/
theorem rootAction_fixed_surjective (i j : Fin 2) (w : Weyl Q)
    (s : RootReflection Q split j)
    (hs : (s.val : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D))) :
    Function.Surjective ((rootAction Q split i w).rangeRestrict.comp
      (reflectionFixed Q split j).subtype) := by
  rintro ⟨x,h,rfl⟩
  obtain ⟨⟨a,b⟩,hab⟩ := (cartanReflectionEquiv Q split j).surjective h
  refine ⟨a,?_⟩
  apply Subtype.ext
  change rootAction Q split i w a.val = rootAction Q split i w h
  change a.val*b.val = h at hab
  rw [← hab,map_mul,rootAction_inverted_eq_one Q split i j w s hs,mul_one]

theorem rootAction_card_dvd_fixed (i j : Fin 2) (w : Weyl Q)
    (s : RootReflection Q split j)
    (hs : (s.val : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D))) :
    Nat.card (cartanPanelMap Q i).range ∣ Nat.card (reflectionFixed Q split j) := by
  rw [← Nat.card_congr (rootActionImageEquiv Q split i w).toEquiv]
  exact card_dvd_of_surjective _ (rootAction_fixed_surjective Q split i j w s hs)

/-- The opposite actual panel is faithful on the first panel kernel. -/
theorem panelKernel_card_dvd_other (i j : Fin 2) (hij : i ≠ j)
    (s : ∀ k, RootReflection Q split k) (hcore : Q.tits.B.normalCore = ⊥) :
    Nat.card (cartanPanelMap Q i).ker ∣ Nat.card (cartanPanelMap Q j).range := by
  let f := (cartanPanelMap Q j).rangeRestrict.comp (cartanPanelMap Q i).ker.subtype
  apply card_dvd_of_injective f
  intro a b hab
  apply Subtype.ext
  apply cartanPanelPair_injective Q split s hcore
  have hi : cartanPanelMap Q i a.val = cartanPanelMap Q i b.val :=
    a.property.trans b.property.symm
  have hj : cartanPanelMap Q j a.val = cartanPanelMap Q j b.val := congrArg Subtype.val hab
  have hi' : i = 0 ∨ i = 1 := by omega
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
  · exact (hij rfl).elim
  · exact Prod.ext hi hj
  · exact Prod.ext hj hi
  · exact (hij rfl).elim

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

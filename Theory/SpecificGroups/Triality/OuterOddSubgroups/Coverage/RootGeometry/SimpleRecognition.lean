module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition.ParabolicIntersections

/-!
# Simple-root recognition from the preserved opposite pair

An automorphism fixing U fixes B = N(U), so it permutes the two actual
proper strict Borel overgroups. Intersecting these parabolics with the fixed
U⁻ identifies its images of the literal negative simple-root groups. The
published opposition involution transports the argument to positive roots.
Finally the root orders q³ and q distinguish the nodes for every q ≥ 2.

The main theorem supplies exactly the recognition premise of
`RootGeometry.exists_unipotent_rootFrame_of_opposition`. It assumes only the
two subgroup-invariance equations; opposition alignment is independent.

Source: Steinberg Theorem 30(1) and the twisted-group extension in Theorem 36,
`refs/KGroup/GLS3/Chapter2St1.tex`; GLS3 §§2.3–2.5,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace Triality.Standard.OuterOdd.Coverage.RootGeometry
open Parabolics ConcreteBruhat SimpleRecognition
noncomputable section

private theorem negative_root_images (f : ℕ) (hf : 0 < f)
    (a : MulAut (Carrier (binaryParameters f hf)))
    (hU : (unipotent (binaryParameters f hf)).map a.toMonoidHom = unipotent (binaryParameters f hf))
    (hV : (oppositeUnipotent (binaryParameters f hf) rfl).map a.toMonoidHom =
      oppositeUnipotent (binaryParameters f hf) rfl)
    (i : Node) : ∃ j : Node,
      a '' Set.range (rootElement (binaryParameters f hf) rfl false i) =
        Set.range (rootElement (binaryParameters f hf) rfl false j) := by
  let P := binaryParameters f hf
  obtain ⟨j, hj⟩ := map_parabolic_eq_of_borel_invariant f hf a
    (map_borel_eq_of_unipotent_invariant P rfl a hU) i
  refine ⟨j, ?_⟩
  calc
    a '' Set.range (rootElement P rfl false i) =
        a '' (parabolic P i ⊓ oppositeUnipotent P rfl : Subgroup _) :=
      congrArg (fun S : Set (Carrier P) => a '' S) (negative_range_eq_intersection f hf i)
    _ = ((parabolic P i ⊓ oppositeUnipotent P rfl).map a.toMonoidHom : Set (Carrier P)) := rfl
    _ = (parabolic P j ⊓ oppositeUnipotent P rfl : Subgroup _) :=
      congrArg (fun H : Subgroup (Carrier P) => (H : Set (Carrier P)))
        ((Subgroup.map_inf (parabolic P i) (oppositeUnipotent P rfl)
          a.toMonoidHom a.injective).trans (congrArg₂ (· ⊓ ·) hj hV))
    _ = Set.range (rootElement P rfl false j) := (negative_range_eq_intersection f hf j).symm

private theorem map_mul_aut {G : Type*} [Group G]
    (H : Subgroup G) (a b : MulAut G) :
    H.map (a * b).toMonoidHom = (H.map b.toMonoidHom).map a.toMonoidHom :=
  (Subgroup.map_map H a.toMonoidHom b.toMonoidHom).symm

private theorem image_conjugate_involutive {G : Type*} [Group G]
    (c a : MulAut G) (hc : Function.Involutive c) (S : Set G) :
    c '' ((c * a * c) '' S) = a '' (c '' S) := by
  rw [Set.image_image, Set.image_image]
  apply congrArg (fun f : G → G => f '' S)
  funext x
  exact hc (a (c x))

private theorem opposition_root_image (f : ℕ) (hf : 0 < f) (s : Bool) (i : Node) :
    (MulAut.conj (weylRepresentative (binaryParameters f hf) rfl (.r 3))) ''
      Set.range (rootElement (binaryParameters f hf) rfl s i) =
      Set.range (rootElement (binaryParameters f hf) rfl (!s) i) := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext (opposition_conj_root f hf s i))

/-- An automorphism preserving the actual opposite pair permutes the simple
root groups of each sign. This is the recognition premise in the parent's
opposition-normalization assembly, including at f = 1. -/
theorem root_images_of_opposite_invariant (f : ℕ) (hf : 0 < f)
    (a : MulAut (Carrier (binaryParameters f hf)))
    (hU : (unipotent (binaryParameters f hf)).map a.toMonoidHom = unipotent (binaryParameters f hf))
    (hV : (oppositeUnipotent (binaryParameters f hf) rfl).map a.toMonoidHom =
      oppositeUnipotent (binaryParameters f hf) rfl) :
    ∀ s : Bool, ∀ i : Node, ∃ j : Node,
      a '' Set.range (rootElement (binaryParameters f hf) rfl s i) =
        Set.range (rootElement (binaryParameters f hf) rfl s j) := by
  let P := binaryParameters f hf
  let c := MulAut.conj (weylRepresentative P rfl (.r 3))
  have hUc : (unipotent P).map c.toMonoidHom = oppositeUnipotent P rfl := rfl
  have hVc : (oppositeUnipotent P rfl).map c.toMonoidHom = unipotent P :=
    map_oppositeUnipotent_opposition P rfl
  have hUb : (unipotent P).map (c * a * c).toMonoidHom = unipotent P := by
    rw [map_mul_aut, map_mul_aut, hUc, hV, hVc]
  have hVb : (oppositeUnipotent P rfl).map (c * a * c).toMonoidHom =
      oppositeUnipotent P rfl := by
    rw [map_mul_aut, map_mul_aut, hVc, hU, hUc]
  intro s i
  cases s with
  | false => exact negative_root_images f hf a hU hV i
  | true =>
    obtain ⟨j, hj⟩ := negative_root_images f hf (c * a * c) hUb hVb i
    refine ⟨j, ?_⟩
    calc
      a '' Set.range (rootElement P rfl true i) =
          a '' (c '' Set.range (rootElement P rfl false i)) :=
        congrArg (fun S : Set (Carrier P) => a '' S) (opposition_root_image f hf false i).symm
      _ = c '' ((c * a * c) '' Set.range (rootElement P rfl false i)) :=
        (image_conjugate_involutive c a (opposition_conj_involutive P rfl) _).symm
      _ = c '' Set.range (rootElement P rfl false j) := congrArg (fun S => c '' S) hj
      _ = Set.range (rootElement P rfl true j) := opposition_root_image f hf false j

/-- The proved geometric recognition and the unequal root-group orders give
the literal root frame required by automorphism coverage. -/
theorem preservesRootFrame_of_opposite_invariant (f : ℕ) (hf : 0 < f)
    (a : MulAut (Carrier (binaryParameters f hf)))
    (hU : (unipotent (binaryParameters f hf)).map a.toMonoidHom = unipotent (binaryParameters f hf))
    (hV : (oppositeUnipotent (binaryParameters f hf) rfl).map a.toMonoidHom =
      oppositeUnipotent (binaryParameters f hf) rfl) :
    PreservesRootFrame (binaryParameters f hf) rfl a :=
  preservesRootFrame_of_root_images _ rfl a (root_images_of_opposite_invariant f hf a hU hV)

end
end Triality.Standard.OuterOdd.Coverage.RootGeometry

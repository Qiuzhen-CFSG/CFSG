module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.BinaryBorel
public import Theory.GroupTheory.PResidual.NormalSubgroup.SimpleQuotient

/-!
# Full projected images of normal marked subgroups at field order four

A nontrivial subgroup invariant under factor exchange cannot have trivial
first projection. For a normal two-perfect marking, that projected subgroup
is the entire factor Borel: its quotient by the two-core is simple of order
three. Thus two such markings have equal full projected images, retaining
their two-cores. These are conditional intrinsic deductions; the source
assembly must construct the actual marked subgroups and conjugation action.

Source: Aschbacher–Smith, proof of 13.8.16(1), printed p.952/PDF p.969.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.BorelProjections
variable {Q : Type*} [Group Q] [Finite Q]

noncomputable def firstProjection (S : Sylow 2 (Q × Q)) :
    BinaryBorel.borel S →* BinaryBorel.borel (BinaryBorel.firstSylow S) :=
  (MonoidHom.fst _ _).comp (BinaryBorel.coordinates S).toMonoidHom

theorem firstProjection_apply (S : Sylow 2 (Q × Q)) (x : BinaryBorel.borel S) :
    (firstProjection S x : Q) = (x : Q × Q).1 := rfl

theorem firstProjection_surjective (S : Sylow 2 (Q × Q)) :
    Function.Surjective (firstProjection S) := by
  intro x
  exact ⟨(BinaryBorel.coordinates S).symm (x, 1), by simp [firstProjection]⟩

theorem firstProjection_ker (S : Sylow 2 (Q × Q)) :
    (firstProjection S).ker = BinaryBorel.secondAxis S := by
  ext x
  change (BinaryBorel.coordinates S x).1 = 1 ↔ (x : Q × Q).1 = 1
  exact Subtype.ext_iff

/-- Swapping the factors prevents a nontrivial invariant subgroup from
having trivial projection. This is about the whole subgroup, not its torus image. -/
theorem first_image_ne_bot (S : Sylow 2 (Q × Q)) (τ : MulAut (BinaryBorel.borel S))
    (hτ : (BinaryBorel.secondAxis S).map τ.toMonoidHom = BinaryBorel.firstAxis S)
    (D : Subgroup (BinaryBorel.borel S)) (hD : D.map τ.toMonoidHom = D) (hne : D ≠ ⊥) :
    D.map (firstProjection S) ≠ ⊥ := by
  intro hz
  have hright : D ≤ BinaryBorel.secondAxis S := by
    rw [← firstProjection_ker S]
    exact (map_eq_bot_iff D).mp hz
  have hleft : D ≤ BinaryBorel.firstAxis S := by
    have h := map_mono (f := τ.toMonoidHom) hright
    rwa [hτ, hD] at h
  apply hne
  apply eq_bot_iff.mpr
  intro x hx
  apply Subtype.ext
  exact Prod.ext (hright hx) (hleft hx)

/-- At q = 4 a normal, two-perfect, nontrivial swapped marking fills
each factor on which it projects. The simple quotient is the actual C₃ torus. -/
theorem first_image_eq_top (hmodel : ClassicalGroup.IsPSL Q 2 4)
    (S : Sylow 2 (Q × Q)) (τ : MulAut (BinaryBorel.borel S))
    (hτ : (BinaryBorel.secondAxis S).map τ.toMonoidHom = BinaryBorel.firstAxis S)
    (D : Subgroup (BinaryBorel.borel S)) [D.Normal]
    (hD : D.map τ.toMonoidHom = D) (hne : D ≠ ⊥) (hp : IsPPerfect 2 D) :
    D.map (firstProjection S) = ⊤ := by
  let f := firstProjection S
  let F := BinaryBorel.borel (BinaryBorel.firstSylow S)
  let _ : (D.map f).Normal := (inferInstance : D.Normal).map f (firstProjection_surjective S)
  let _ : IsSimpleGroup (F ⧸ pCore 2 F) := BinaryBorel.torus_four_simple hmodel _
  exact eq_top_of_normal_isPPerfect_of_simple_quotient (pCore 2 F) pCore_isPGroup
    (BinaryBorel.factor_twoPerfect (n := 2) (by decide) hmodel _) _
    (hp.of_surjective (f.subgroupMap D) (f.subgroupMap_surjective D))
    (first_image_ne_bot S τ hτ D hD hne)

/-- The image equality uses the ambient first projection of Q × Q. -/
theorem ambient_first_image (hmodel : ClassicalGroup.IsPSL Q 2 4)
    (S : Sylow 2 (Q × Q)) (τ : MulAut (BinaryBorel.borel S))
    (hτ : (BinaryBorel.secondAxis S).map τ.toMonoidHom = BinaryBorel.firstAxis S)
    (D : Subgroup (BinaryBorel.borel S)) [D.Normal]
    (hD : D.map τ.toMonoidHom = D) (hne : D ≠ ⊥) (hp : IsPPerfect 2 D) :
    (D.map (BinaryBorel.borel S).subtype).map (MonoidHom.fst Q Q) =
      BinaryBorel.borel (BinaryBorel.firstSylow S) := by
  have he := first_image_eq_top hmodel S τ hτ D hD hne hp
  calc
    (D.map (BinaryBorel.borel S).subtype).map (MonoidHom.fst Q Q) =
        (D.map (firstProjection S)).map (BinaryBorel.borel (BinaryBorel.firstSylow S)).subtype := by
      rw [map_map, map_map]
      rfl
    _ = _ := by rw [he, ← MonoidHom.range_eq_map, range_subtype]

/-- Two genuine marked subgroups have equal full projected images; their
two-cores have not been thrown away. This is the input for the seed projection. -/
theorem marked_ambient_images_eq (hmodel : ClassicalGroup.IsPSL Q 2 4)
    (S : Sylow 2 (Q × Q)) (τ : MulAut (BinaryBorel.borel S))
    (hτ : (BinaryBorel.secondAxis S).map τ.toMonoidHom = BinaryBorel.firstAxis S)
    (D₀ Dplus : Subgroup (BinaryBorel.borel S)) [D₀.Normal] [Dplus.Normal]
    (h₀ : D₀.map τ.toMonoidHom = D₀) (hplus : Dplus.map τ.toMonoidHom = Dplus)
    (hne₀ : D₀ ≠ ⊥) (hneplus : Dplus ≠ ⊥)
    (hp₀ : IsPPerfect 2 D₀) (hpplus : IsPPerfect 2 Dplus) :
    (D₀.map (BinaryBorel.borel S).subtype).map (MonoidHom.fst Q Q) =
      (Dplus.map (BinaryBorel.borel S).subtype).map (MonoidHom.fst Q Q) :=
  (ambient_first_image hmodel S τ hτ D₀ h₀ hne₀ hp₀).trans
    (ambient_first_image hmodel S τ hτ Dplus hplus hneplus hpplus).symm

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.BorelProjections

end

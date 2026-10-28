module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.Contrary.ComponentBranch
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.Held.FFSource

/-!
# Full Held exclusion on the original contrary source pair

The actual module input constructs the contrary context. Full known-simple
1.1.5 rules out the ordinary Fitting branch, and the proved local omega FF
application rules out characteristic two. Both use the same retained Held
quotient and all original subgroup maps. No C.2.7, FF classification or A/B/C
callback remains in this complete Held branch.

Source: Aschbacher--Smith 1.1.5, B.5.1 and 15.4.20, with the Held alternative
retained by the adequate intrinsic embedding theorem.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary
open FamilySource FamilySource.ModuleStructure EmbeddingReduction CoreElimination
open BlockSieve.ExchangedCases.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

/-- The extra Held branch of the adequate intrinsic embedding is impossible
for the original source pair, with both Fitting branches discharged. -/
theorem source_held_contradiction_from_ff
    (hX : Input KnownSimple.IsKnownSimple T M₁ X 2) (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁)
    (unique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      X ⊔ (T : Subgroup G) ≤ N → N = M₁)
    (hZcard : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4)
    {i j : Bool} {H U K : Subgroup G}
    (h : PlacedX (geometry pX pY) i j H U)
    (hgen : K ⊔ U = H)
    (hclosure : K = normalClosureIn (geometry pX pY).wholeX H)
    (hres : K = (primeToResidual 3 H).map H.subtype)
    (hK : (K.subgroupOf H).IsCComponent)
    (hq : IsQuasisimple (Chapter1.XiQuotient K))
    (e : Chapter1.XiQuotient K ≃* Held.He) : False := by
  let d := geometry pX pY
  let s : ComponentElimination.OrdinaryReduction.SourceContext d i j H K U := {
    placed := h
    closure := hclosure
    residual := hres
    generation := hgen.symm
    omega := rfl
    four := hZcard
    local115 := placed_local115 hX.ambient h rfl }
  have hchar := ComponentElimination.source_held_characteristicTwo hX.ambient
    (fun A _ _ => ChapterA.Section02.theoremsABC_knownSimple (G := A)) s hK e
  let b := contraryInput hX pX pY hZcard h hgen hclosure hres hchar
  have hx : d.wholeX = X := pX.quotient.factor_generate hX
  have hm : d.M₁ = M₁ := by
    change normalizer (d.wholeX : Set G) = M₁
    rw [hx, hM₁]
  have hu : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁ := by
    rw [hx, hm]
    exact unique
  exact not_held_single_component_from_ff hX.ambient b hu hK hq e

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary


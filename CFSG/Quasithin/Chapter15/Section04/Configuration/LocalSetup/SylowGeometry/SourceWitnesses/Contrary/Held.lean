module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.Contrary.ComponentBranch
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.Held

/-!
# The retained Held alternative from the original source pair

The actual placed overgroup and its residual normal closure construct the
ordinary source context. The complete 1.1.5 excludes the ordinary Held
branch, yielding characteristic two. The same source pair then constructs
all block-sieve data, and the complete C.2.7 on the single component excludes
Held in characteristic two.

This application assumes no Fitting branch, contrary record, module model,
local radical or star-kernel identity. It retains the genuine ambient source
hypotheses, actual residual identifications and full earlier A/B/C and C.2.7.
The adequate intrinsic reduction must produce this retained alternative;
the original Held-excluding LocalEmbeddingTheorem is not used.
Source: Aschbacher--Smith, 1.1.5, C.2.7 and 15.4.20, pp.501--503,
145--147,1164, with Held retained in the intrinsic embedding reduction.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary
open FamilySource FamilySource.ModuleStructure EmbeddingReduction CoreElimination
open BlockSieve.ExchangedCases.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

/-- The extra Held branch of the adequate intrinsic embedding is impossible
for the original source pair, with both Fitting branches discharged. -/
theorem source_held_contradiction
    (hX : Input κ T M₁ X 2) (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁)
    (unique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      X ⊔ (T : Subgroup G) ≤ N → N = M₁)
    (hZcard : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hABC : ∀ (A : Type u) [Group A] [Finite A], ChapterA.Section02.TheoremsABC κ A)
    (c27 : UniversalC27.{u})
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
  have hchar := ComponentElimination.source_held_characteristicTwo hX.ambient hABC s hK e
  let b := contraryInput hX pX pY hZcard h hgen hclosure hres hchar
  have hx : d.wholeX = X := pX.quotient.factor_generate hX
  have hm : d.M₁ = M₁ := by
    change normalizer (d.wholeX : Set G) = M₁
    rw [hx, hM₁]
  have hu : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁ := by
    rw [hx, hm]
    exact unique
  exact not_held_single_component c27 hX.ambient b hu hK hq e

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary

module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.ChiefKernelCover
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.EssentialCartan
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.SpanImageReduction

/-!
# The original Cartan cover on the faithful whole-span action

Retain the original overlap preimage and its exact projection to the split
Cartan. The proved chief-action reduction restricts to its whole-span image,
where the covering kernel is exactly the intersection with the whole-action
two-core. Thus this cover has a two-group kernel and preserves the original
action homomorphisms. The kernel in the original group is retained separately.

The source constructor supplies the alternative and the essential actor;
no small-natural classification or centralization premise is introduced.
The actual M22-code application is in M22CodeCartan. Field reduction,
odd-element lifting upstairs, and the cubic contradiction remain subsequent
parts of the original sieve.
Source: Aschbacher--Smith, 3.1.9(6), printed pp.577--578, used in 8.2.2(1), p.715.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterD NoncentralChiefRefinement
variable {G D W : Type*} [Group G] [Group D]
  [AddCommGroup W] [Module (ZMod 2) W]
  {M H : Subgroup G} {q : H →* D} {ρ : Representation (ZMod 2) D W} {v : W}

/-- The source alternative with the complete original Cartan covering map.
Naming this proposition keeps the large essential-action instances out of
repeated elaboration of the same covering clauses. -/
@[expose] def OriginalCartanAlternatives (V : Subgroup G)
    (q : H →* D) (ρ : Representation (ZMod 2) D W) (v : W) : Prop :=
  ChapterB.ChiefSmallNaturalAlternatives ρ ∨
    ∃ c : SeedCartan (M := M) q ρ v,
      ∃ p : c.originalPreimage →* c.field.Carrierˣ,
        Function.Surjective p ∧
        c.embedding.comp p = q.comp c.originalPreimage.subtype ∧
        p.ker = q.ker.subgroupOf c.originalPreimage ∧
        ∀ x : c.originalPreimage,
          ((x : H) : G) ∈ centralizer (V : Set G) → p x = 1

/-- The full original preimage maps onto the constructed Cartan. -/
theorem SeedCartan.originalPreimage_map (c : SeedCartan (M := M) q ρ v) :
    c.originalPreimage.map q = c.embedding.range := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hx.2
  · intro x hx
    obtain ⟨y,hy,hyx⟩ := c.in_overlap hx
    exact ⟨y,⟨hy,show q y ∈ c.embedding.range from hyx.symm ▸ hx⟩,hyx⟩

variable {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z]

/-- The full cover on the original whole-span image, including its exact
kernel and the original action map. -/
@[expose] def SeedCartan.HasSpanCover (c : SeedCartan (M := M) q ρ v)
    (τ : Representation (ZMod 2) H Z) : Prop :=
  let P := actionSubgroup τ c.originalPreimage
  ∃ f : P →* c.field.Carrierˣ,
    Function.Surjective f ∧
    (∀ b : c.originalPreimage,
      c.embedding (f ⟨actionHom τ b,mem_map_of_mem _ b.property⟩) = q b) ∧
    f.ker = (pCore 2 (actionImage τ)).comap P.subtype ∧
    IsPGroup 2 f.ker

/-- The proved reduction constructs the cover, with a two-group kernel. -/
theorem SeedCartan.span_cover
    (σ : Representation (ZMod 2) H W) (w : W)
    (c : SeedCartan (M := M) (actionHom σ) (imageRepresentation σ) w)
    (τ : Representation (ZMod 2) H Z)
    (d : MathieuCode.NormalizedShadowRows.ActionImageReduction τ σ) :
    c.HasSpanCover τ := by
  obtain ⟨f,hf,he,hk⟩ := d.cover_subgroup c.originalPreimage c.embedding c.injective
    c.originalPreimage_map
  refine ⟨f,hf,he,hk,?_⟩
  rw [hk]
  exact pCore_isPGroup.comap_of_injective _ (actionSubgroup _ _).subtype_injective

variable [Finite G] {V : Subgroup G}
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
  {S : Sylow 2 H} {hVH : V ≤ H}

set_option backward.isDefEq.respectTransparency false in
/-- Apply the constructed original cover to the same essential source action. -/
theorem essential_original_cartan_alternatives
    {T : Sylow 2 G} {M₀ : Subgroup G}
    (h : QrcHypotheses T M M₀ H V)
    (hD : IsSQTK KnownSimple.IsKnownSimple H)
    (hns : ¬ Group.IsSolvable H)
    (a : EssentialSeedAction H V (T.subtype h.right_mem.1.1.2) hVH)
    (hff : IsFFModule a.imageRepresentation) :
    OriginalCartanAlternatives (M := M) V a.projection a.imageRepresentation a.vector :=
  essential_small_or_seed_cartan_cover h hD hns a hff

set_option backward.isDefEq.respectTransparency false in
/-- The same essential actor constructs the Cartan cover on the whole span. -/
theorem essential_cartan_span_cover
    (a : EssentialSeedAction H V S hVH)
    (A : Subgroup H) (ha : EssentialChiefActor a A)
    (c : SeedCartan (M := M) a.projection a.imageRepresentation a.vector)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin s.series.length) (hi : ¬ s.Central i) :
    c.HasSpanCover (normalRepresentation ((conjugateSpan H V).subgroupOf H)) := by
  obtain ⟨d⟩ := essential_span_image_reduction a A ha s i hi
  exact c.span_cover a.representation a.vector _ d

end CFSG.Quasithin.Chapter8.MathieuShadowRows

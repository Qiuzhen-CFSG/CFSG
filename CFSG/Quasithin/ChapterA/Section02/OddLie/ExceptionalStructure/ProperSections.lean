module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Sections
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems
public import CFSG.KnownSimple.ExceptionalModels

/-!
# Proper exceptional sections

Aschbacher--Smith A.2.17 uses proper sections, so an embedding into an
exceptional carrier must retain both its literal range and its strict
properness.  The records here turn an injective map with a proper range into
the exact `IsProperSectionOf` witness used by the induction statement.

The records deliberately keep the cross-family map as data.  The concrete
root-datum realization of `F₄ < ²E₆` and of the `F₄ < E₆ < E₇ < E₈` chain is
not present in the existing finite matrix carriers; an order equality or a
family tag cannot supply it.  Once the GLS3 root-map certificate is provided,
the theorems below discharge the section and central-version bookkeeping.

Source: Aschbacher--Smith, Lemma A.2.17, printed p.39 of
`refs/quasithin.pdf`; GLS3, §§2.2--2.6.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterA.Section02

open ExceptionalSplit

universe u v

variable {S : Type u} {G : Type v} [Group S] [Group G]

/-! ## Generic proper embeddings -/

/-- A literal proper copy of `S` in `G`. -/
structure ProperEmbeddingData (S : Type u) (G : Type v)
    [Group S] [Group G] where
  embedding : S →* G
  injective : Function.Injective embedding
  proper : embedding.range ≠ ⊤

theorem ProperEmbeddingData.range_proper (d : ProperEmbeddingData S G) :
    d.embedding.range ≠ ⊤ := d.proper

/-- A proper embedding supplies a section of the ambient group.

The numerator is the literal range.  Its map back to `S` is the inverse of
the induced equivalence, so the returned map is genuinely surjective. -/
theorem ProperEmbeddingData.isProperSectionOf [Finite G]
    (d : ProperEmbeddingData S G) : IsProperSectionOf S G := by
  let e : S ≃* d.embedding.range := MonoidHom.ofInjective d.injective
  refine ⟨?_, ?_⟩
  · exact ⟨d.embedding.range, e.symm.toMonoidHom, e.symm.surjective⟩
  · exact (Nat.card_congr e.toEquiv).trans_lt
      (IsProperSectionOf.subgroup d.embedding.range d.proper).2

/-- The same construction with the strictness proof separated out. -/
theorem ProperEmbeddingData.isSectionOf [Finite G]
    (d : ProperEmbeddingData S G) : IsSectionOf S G :=
  (d.isProperSectionOf).1

/-! ## The four split-family contracts -/

structure F4ProperSection (F : Type*) [Field F] [Finite F]
    (G : Type v) [Group G] where
  data : ProperEmbeddingData (ExceptionalSplit.F4 F) G

theorem F4ProperSection.isProperSectionOf (F : Type*) [Field F] [Finite F]
    {G : Type v} [Group G] [Finite G]
    (d : F4ProperSection F G) :
    IsProperSectionOf (ExceptionalSplit.F4 F) G :=
  d.data.isProperSectionOf

structure E6ProperSection (F : Type*) [Field F] [Finite F]
    (G : Type v) [Group G] where
  data : ProperEmbeddingData (ExceptionalSplit.E6 F) G

theorem E6ProperSection.isProperSectionOf (F : Type*) [Field F] [Finite F]
    {G : Type v} [Group G] [Finite G]
    (d : E6ProperSection F G) :
    IsProperSectionOf (ExceptionalSplit.E6 F) G :=
  d.data.isProperSectionOf

structure E7ProperSection (F : Type*) [Field F] [Finite F]
    (G : Type v) [Group G] where
  data : ProperEmbeddingData (ExceptionalSplit.E7 F) G

theorem E7ProperSection.isProperSectionOf (F : Type*) [Field F] [Finite F]
    {G : Type v} [Group G] [Finite G]
    (d : E7ProperSection F G) :
    IsProperSectionOf (ExceptionalSplit.E7 F) G :=
  d.data.isProperSectionOf

structure E8ProperSection (F : Type*) [Field F] [Finite F]
    (G : Type v) [Group G] where
  data : ProperEmbeddingData (ExceptionalSplit.E8 F) G

theorem E8ProperSection.isProperSectionOf (F : Type*) [Field F] [Finite F]
    {G : Type v} [Group G] [Finite G]
    (d : E8ProperSection F G) :
    IsProperSectionOf (ExceptionalSplit.E8 F) G :=
  d.data.isProperSectionOf

/-! ## Chain edges and central versions -/

/-- An edge in a finite exceptional-family chain, retaining the central
cover/quotient distinction in the map supplied by the root construction. -/
structure ChainEdge (S : Type u) (T : Type v) [Group S] [Group T] where
  map : S →* T
  injective : Function.Injective map
  proper : map.range ≠ ⊤

theorem ChainEdge.isProperSectionOf {S : Type u} {T : Type v}
    [Group S] [Group T] [Finite T]
    (d : ChainEdge S T) : IsProperSectionOf S T := by
  exact ProperEmbeddingData.isProperSectionOf
    ⟨d.map, d.injective, d.proper⟩

/- A root-generated cover map together with the induced quotient map.  The
source and target projections are explicit, so a simply-connected subgroup is
never silently identified with its central quotient.  The quotient map itself
is the edge used for the proper-section conclusion; compatibility is retained
for later central-cover arguments. -/
structure CentralChainEdge
    (S Sbar : Type u) (T Tbar : Type v)
    [Group S] [Group Sbar] [Group T] [Group Tbar] where
  coverMap : S →* T
  quotientMap : Sbar →* Tbar
  sourceProjection : S →* Sbar
  targetProjection : T →* Tbar
  commute : targetProjection.comp coverMap = quotientMap.comp sourceProjection
  injective : Function.Injective quotientMap
  proper : quotientMap.range ≠ ⊤

def CentralChainEdge.toChainEdge {S Sbar : Type u} {T Tbar : Type v}
    [Group S] [Group Sbar] [Group T] [Group Tbar]
    (d : CentralChainEdge S Sbar T Tbar) : ChainEdge Sbar Tbar :=
  ⟨d.quotientMap, d.injective, d.proper⟩

theorem CentralChainEdge.isProperSectionOf
    {S Sbar : Type u} {T Tbar : Type v}
    [Group S] [Group Sbar] [Group T] [Group Tbar] [Finite Tbar]
    (d : CentralChainEdge S Sbar T Tbar) : IsProperSectionOf Sbar Tbar :=
  d.toChainEdge.isProperSectionOf

/-! ## Named A.2.17 chain contracts -/

structure F4InTwistedE6 (p m : ℕ) [Fact p.Prime] where
  oddPrime : Odd p
  exponent_positive : 0 < m + 1
  edge : ChainEdge (ExceptionalSplit.F4 (GaloisField p (m + 1))) (TwistedE6.Model p m)

structure F4InE6 (F : Type*) [Field F] [Finite F] where
  edge : ChainEdge (ExceptionalSplit.F4 F) (ExceptionalSplit.E6 F)

structure F4InE7 (F : Type*) [Field F] [Finite F] where
  edge : ChainEdge (ExceptionalSplit.F4 F) (ExceptionalSplit.E7 F)

structure F4InE8 (F : Type*) [Field F] [Finite F] where
  edge : ChainEdge (ExceptionalSplit.F4 F) (ExceptionalSplit.E8 F)

structure E6InE7 (F : Type*) [Field F] [Finite F] where
  edge : ChainEdge (ExceptionalSplit.E6 F) (ExceptionalSplit.E7 F)

structure E7InE8 (F : Type*) [Field F] [Finite F] where
  edge : ChainEdge (ExceptionalSplit.E7 F) (ExceptionalSplit.E8 F)

end CFSG.Quasithin.ChapterA.Section02

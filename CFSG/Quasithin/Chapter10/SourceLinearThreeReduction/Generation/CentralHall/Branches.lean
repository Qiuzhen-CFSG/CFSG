module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Action
public import Theory.FieldTheory.BinaryNormOne

/-!
# The two remaining central Hall image calculations

The context below is exactly the context of `SourceNonnormalCentralHallAt`.
Its fields are source hypotheses, not module alternatives or conclusions.
The first outstanding calculation concerns the actual SL₃(2) quotient.
The second must identify the surviving orthogonal quotient and embed the
literal Hall action image in the two norm-one factors. In particular it
includes the exclusion of the natural and Suzuki rows and of a nontrivial
field-automorphism factor.

These predicates record unproved source obligations. Their consumer is
`source_nonnormalCentralHall_of_image_branches`; that conditional assembly
does not establish the source contract until both obligations are proved.
Source: Aschbacher--Smith, 10.1.1--2 and 10.2.3, pp.741--742,745.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.CentralHall
open Chapter3.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal hypotheses of the centralizing branch, with no model input. -/
structure Context (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H) : Prop where
  many : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  minimal : D.IsMinimalFullModule
  nonnormal : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)
  not_a5 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  hstar : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal
  large : 1 < ChapterE.generationParameter H
  central : ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G), H⁆ = ⊥
  hall_le : B ≤ D.maximalLocal.subgroupOf H
  hall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H))
  abelian : IsMulCommutative B
  permutes : (B.map H.subtype : Set G) * (T : Set G) =
    (T : Set G) * (B.map H.subtype : Set G)
  faithful : B.map H.subtype ⊓ Chapter4.sectionCentralizer (localOrbit T L) = ⊥

/-- The SL₃(2) calculation, retaining the original action on L₀/O₂(L₀). -/
def LinearThreeImageAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H) (c : Context D H B),
    Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      IsPGroup 3 (action D B c.hall_le).range

/-- The other rows must yield an actual orthogonal quotient and a faithful
map of the original Hall action image into the concrete norm-one torus pair.
The source module analysis and field-factor elimination belong to its producer. -/
def NonlinearTorusAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H) (c : Context D H B),
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      ∃ n : ℕ, 1 < n ∧
        Nonempty ((L ⧸ pCore 2 L) ≃*
          Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * n))) ∧
        ∃ f : (action D B c.hall_le).range →*
          FiniteField.BinaryNormOne.torus n × FiniteField.BinaryNormOne.torus n,
          Function.Injective f

end CFSG.Quasithin.Chapter10.CentralHall

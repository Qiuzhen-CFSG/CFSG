module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.Coordinates

/-!
# The complete natural cases in their actual MS-group

The one-layer case retains its block clause and the two-layer case retains
its radical inequality. The MS-pair, intrinsic Sylow subgroup and radical
containment are all recorded in LR. Faithful inclusion transports the actual
commutator core and its full layer model into the original ambient group.

Source: Aschbacher–Smith, C.1.31 and C.1.34(1),(2), printed pp.135–137,
as used in 15.3.23, printed pp.1128–1129.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Exactly the complete one- and two-natural-layer alternatives. -/
inductive NaturalCase (L R : Subgroup G) (S : Sylow 2 G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Prop
  | one (block : ChapterC.IsSL3EvenBlock L 1)
      (natural : Nonempty (LayerModel L (sourceQ L) ⊥ e (NaturalCopies (ZMod 2) 1)))
  | two (natural : Nonempty (LayerModel L (sourceQ L) ⊥ e (NaturalCopies (ZMod 2) 2)))
      (radical : RadicalInequality R S)

omit [Finite G] in
/-- The retained case is an actual C.1.34 alternative, with every clause. -/
theorem NaturalCase.alternatives {L R : Subgroup G} {S : Sylow 2 G}
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (h : NaturalCase L R S e) : Alternatives (ZMod 2) 1 L R S e := by
  cases h with
  | one hb hm => exact .one hb hm
  | two hm hr => exact .two hm hr

/-- Compatible C.1.34 data in the actual MS-group LR. Neither the layer
nor the MS ambient group is replaced by an abstract family label. -/
structure SourceData (κ : GroupClass.{u}) (L R : Subgroup G) where
  ms : MSPair κ (L ⊔ R : Subgroup G) (L.subgroupOf (L ⊔ R : Subgroup G)) (R.subgroupOf (L ⊔ R : Subgroup G))
  sylow : Sylow 2 (L ⊔ R : Subgroup G)
  radical_le : R.subgroupOf (L ⊔ R : Subgroup G) ≤ (sylow : Subgroup (L ⊔ R : Subgroup G))
  quotient : ((L.subgroupOf (L ⊔ R : Subgroup G)) ⧸ pCore 2 (L.subgroupOf (L ⊔ R : Subgroup G))) ≃*
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  alternative : NaturalCase (L.subgroupOf (L ⊔ R : Subgroup G)) (R.subgroupOf (L ⊔ R : Subgroup G)) sylow quotient

/-- Faithful transport gives the actual ambient core, retaining one common
quotient marking on all copies. -/
theorem SourceData.ambient_layer {κ : GroupClass.{u}} {L R : Subgroup G}
    (s : SourceData κ L R) :
    ∃ a : ℕ, (a = 1 ∨ a = 2) ∧
      ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        Nonempty (LayerModel L (commutatorCore L) ⊥ e (NaturalCopies (ZMod 2) a)) := by
  have transport (a : ℕ)
      (m : LayerModel (L.subgroupOf (L ⊔ R : Subgroup G)) (sourceQ (L.subgroupOf (L ⊔ R : Subgroup G))) ⊥
        s.quotient (NaturalCopies (ZMod 2) a)) :
      ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        Nonempty (LayerModel L (commutatorCore L) ⊥ e (NaturalCopies (ZMod 2) a)) := by
    have h : ∃ e : (((L.subgroupOf (L ⊔ R : Subgroup G)).map (L ⊔ R : Subgroup G).subtype) ⧸
        pCore 2 ((L.subgroupOf (L ⊔ R : Subgroup G)).map (L ⊔ R : Subgroup G).subtype)) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        Nonempty (LayerModel ((L.subgroupOf (L ⊔ R : Subgroup G)).map (L ⊔ R : Subgroup G).subtype)
          ((sourceQ (L.subgroupOf (L ⊔ R : Subgroup G))).map (L ⊔ R : Subgroup G).subtype)
          ((⊥ : Subgroup (L ⊔ R : Subgroup G)).map (L ⊔ R : Subgroup G).subtype) e (NaturalCopies (ZMod 2) a)) :=
      ⟨embeddedQuotient (L ⊔ R : Subgroup G).subtype (L ⊔ R : Subgroup G).subtype_injective _ s.quotient,
        ⟨embedLayer (L ⊔ R : Subgroup G).subtype (L ⊔ R : Subgroup G).subtype_injective m⟩⟩
    rw [sourceQ_map_subtype (show L ≤ L ⊔ R from le_sup_left) s.ms.component,
      map_subgroupOf_eq_of_le (show L ≤ L ⊔ R from le_sup_left), Subgroup.map_bot] at h
    exact h
  cases s.alternative with
  | one hb hm => exact ⟨1, Or.inl rfl, transport 1 hm.some⟩
  | two hm hr => exact ⟨2, Or.inr rfl, transport 2 hm.some⟩
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions

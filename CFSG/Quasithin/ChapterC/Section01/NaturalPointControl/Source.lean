module

public import CFSG.Quasithin.ChapterC.Section01.NaturalPointControl.Preimages

/-!
# The marked natural-point source application of B.2.19

Start with the actual quotient G/O₂(G), its natural coordinates on V, and
the full preimage P of the point stabilizer in those same coordinates.
The source two-core is exactly O₂(P), embedded by P's subtype map.
The three generating groups are the full preimages of the displayed cyclic
roots under that original quotient map. The preceding construction now
supplies the characteristic alternative or every Baumann-family clause,
and gives all four B.2.19 conclusions in the nontrivial-image branch.

This discharges the natural L₃(2) preimage and equal-weight step in C.1.37,
printed p.143. It does not assert the later MS classification or the
chief-factor alternative in 14.7.10; those require their source producers.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.NaturalPointControl
open ChapterB ChapterB.BaumannArgument
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
variable {G : Type*} [Group G] (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]

noncomputable def ofQuotient (e : (G ⧸ pCore 2 G) ≃* SL)
    (c : V ≃* Multiplicative Geometry.Vector)
    (h : ∀ g v, (c (MulAut.conjNormal g v)).toAdd =
      e (QuotientGroup.mk' (pCore 2 G) g) • (c v).toAdd) : NaturalAction V where
  q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  onto := e.surjective.comp (QuotientGroup.mk'_surjective _)
  kernel := by
    ext g
    change e (QuotientGroup.mk' (pCore 2 G) g) = 1 ↔ g ∈ pCore 2 G
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff g
  coordinates := c
  action := h

variable [Finite G]

/-- The actual parabolic two-core has a characteristic obstruction or the
complete B.2.18 family; its cyclic preimages use the original quotient map. -/
theorem point_preimage_source (e : (G ⧸ pCore 2 G) ≃* SL)
    (c : V ≃* Multiplicative Geometry.Vector)
    (ha : ∀ g v, (c (MulAut.conjNormal g v)).toAdd =
      e (QuotientGroup.mk' (pCore 2 G) g) • (c v).toAdd)
    (P : Subgroup G)
    (hP : pointParabolicSL.comap
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))) = P) :
    (∃ C : Subgroup (baumann (P.pCoreIn 2)), C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map (baumann (P.pCoreIn 2)).subtype).Normal) ∨
    (HypothesesAD V (P.pCoreIn 2)
      (fun i : Fin 3 => elementaryAbelianMaxJ
        ((zpowers (PointOffenders.root i)).comap
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))))) ∧
      elementaryAbelianMaxJ (P.pCoreIn 2) ≤
        ⨆ i : Fin 3, elementaryAbelianMaxJ
          ((zpowers (PointOffenders.root i)).comap
            (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))))) := by
  let d := ofQuotient V e c ha
  have he : d.P = P := hP
  have hR : d.R = P.pCoreIn 2 := d.R_eq_parabolic_core.trans (congrArg (fun P => P.pCoreIn 2) he)
  have hh := d.characteristic_or_family
  rw [hR] at hh
  simpa only [NaturalAction.D, d, ofQuotient] using hh

/-- B.2.19 on the literal point-stabilizer core: the nontrivial-image branch
supplies its four conclusions, without any preimage-family premise. -/
theorem point_baumann_source (e : (G ⧸ pCore 2 G) ≃* SL)
    (c : V ≃* Multiplicative Geometry.Vector)
    (ha : ∀ g v, (c (MulAut.conjNormal g v)).toAdd =
      e (QuotientGroup.mk' (pCore 2 G) g) • (c v).toAdd)
    (P : Subgroup G)
    (hP : pointParabolicSL.comap
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))) = P)
    (hne : (elementaryAbelianMaxJ (P.pCoreIn 2)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))) ≠ ⊥) :
    (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ baumann (P.pCoreIn 2) ∧
      thompsonAlpha (P.pCoreIn 2) =
        (thompsonAlpha (P.pCoreIn 2) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (V ⊓ centralizer (elementaryAbelianMaxJ (P.pCoreIn 2) : Set G)) ∧
      IsSylowSubgroupIn (baumann (P.pCoreIn 2) ⊓ centralizer (V : Set G))
        ((pResidual 2 G ⊔ baumann (P.pCoreIn 2)) ⊓ centralizer (V : Set G)) ∧
      (IsSylowSubgroupIn ((baumann (P.pCoreIn 2)).map (actionMap V))
          ((pResidual 2 G).map (actionMap V) ⊔ (baumann (P.pCoreIn 2)).map (actionMap V)) →
        IsSylowSubgroupIn (baumann (P.pCoreIn 2))
          (pResidual 2 G ⊔ baumann (P.pCoreIn 2))) := by
  let d := ofQuotient V e c ha
  have he : d.P = P := hP
  have hR : d.R = P.pCoreIn 2 := d.R_eq_parabolic_core.trans (congrArg (fun P => P.pCoreIn 2) he)
  have hn : (elementaryAbelianMaxJ d.R).map d.q ≠ ⊥ := by
    change (elementaryAbelianMaxJ d.R).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))) ≠ ⊥
    rwa [hR]
  simpa only [hR] using d.baumann_conclusions hn

end CFSG.Quasithin.ChapterC.NaturalPointControl

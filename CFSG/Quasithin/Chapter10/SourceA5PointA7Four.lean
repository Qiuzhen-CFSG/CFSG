module
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion
public import CFSG.Quasithin.Chapter10.SourceA5PointActionModels
/-!
# The four-dimensional A₇ point orbit

The original A₅ moved factor has at least sixteen elements. Once the full
point orbit is identified with its four-dimensional quotient, the fixed-span
containment makes these subgroups equal. The containing component normalizes
that orbit, so the earlier original normalizer bound excludes the escaped row.
Source: Aschbacher–Smith 10.2.9, printed pp.751–752.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The four-dimensional original orbit is the entire original moved factor. -/
theorem source_a5_point_four_span_eq
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {v : G} (I : Subgroup G) (hLI : L ≤ I)
    (hspan : ⁅D.fullModule,L⁆ ≤ conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)))))
    (hd : let H := I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf H
      letI := hr.elementary
      Module.finrank (ZMod 2) (Additive U) = 4) :
    conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
      ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I = ⁅D.fullModule,L⁆ := by
  let H := I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
  let V := conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
    ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I
  let U := V.subgroupOf H
  let := hr.elementary
  have hVH : V ≤ H := (conjugateSpanBy_le_self
    (inf_le_left.trans ((source_full_moved_le_component D).trans hLI))).trans le_sup_left
  have hu : Nat.card U = 16 := by
    change Nat.card (Additive U) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    decide
  have hV : Nat.card V = 16 := (Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv).symm.trans hu
  exact (eq_of_le_of_card_ge hspan (by rw [hV]; exact source_a5_full_moved_card D e)).symm
/-- The four-dimensional A₇ row gives the source exceptional orbit alternative. -/
theorem source_a5_point_four_alternative
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t v : G} (I : Subgroup G) (hLI : L ≤ I)
    (hspan : ⁅D.fullModule,L⁆ ≤ conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)))))
    (hd : let H := I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf H
      letI := hr.elementary
      Module.finrank (ZMod 2) (Additive U) = 4) :
    SourceA5PointComponentAlternative D e t I :=
  .exceptional _ (source_a5_point_four_span_eq D e I hLI hspan hr hd)

end CFSG.Quasithin.Chapter10

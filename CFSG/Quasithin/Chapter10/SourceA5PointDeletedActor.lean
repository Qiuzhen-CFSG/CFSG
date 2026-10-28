module
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter3.Section02.Setup
public import CFSG.Quasithin.ChapterB.InternalThompsonSevenAction
public import Theory.GroupTheory.Commutator.ConjugateSpan

/-!
# The full deleted-seven actor at an original point

The normal original point component acts on its reduced fixed-vector orbit.
The marked deleted-seven section, with full movement and vanishing fixed
space, identifies the full centralizer quotient with S7. This specialization
keeps the original subgroup, quotient kernel and conjugation coordinates
required by the C.1.24 reconstruction in Aschbacher–Smith 10.2.9,
printed pp.751–753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The literal point quotient and its original module have the full S7 coordinates. -/
theorem source_a5_point_deleted_actor
    {v : G} (I : Subgroup G)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := I ⊔ P
    let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I).subgroupOf H
    letI := hr.normal; letI := hr.elementary
    let A := (I.subgroupOf H).map (actionMk U)
    let N := offenderSubgroup (action U)
    let C := A.subgroupOf N
    ∀ _hAN : A ≤ N,
    ∀ s : MovedSection ((action U).comp N.subtype) C,
    moved ((action U).comp N.subtype) C = ⊤ →
    fixedSpace ((action U).comp N.subtype) C = ⊥ →
    MarkedActionEquiv s.central.quotientRepresentation (offenderSubgroup s.central.quotientRepresentation)
      C (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7)) →
    ∃ q : H →* Equiv.Perm (Fin 7), ∃ hq : Function.Surjective q,
    ∃ hk : q.ker = centralizer (U : Set H),
      (I.subgroupOf H).map q = alternatingGroup (Fin 7) ∧
      ∃ eV : Additive U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7),
      ∀ g w, eV (NormalElementaryQuotient.representation U q hq hk g w) =
        BinaryPermutation.naturalRepresentation (Fin 7) g (eV w) := by
  dsimp only
  let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ P
  let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I).subgroupOf H
  let := hr.normal
  let := hr.elementary
  let K := I.subgroupOf H
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans hNI))
  intro hAN s hm hc m
  exact deleted_seven_quotient_coordinates U K hAN s hm hc m
end CFSG.Quasithin.Chapter10

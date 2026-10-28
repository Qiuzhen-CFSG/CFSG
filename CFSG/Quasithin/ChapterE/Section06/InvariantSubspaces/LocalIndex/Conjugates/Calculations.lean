module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Assembly

/-!
# The two calculations in the conjugate-block argument

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.6,
printed pp.156–158, and C.5.7, printed p.160.

The factorization calculation precedes the Frattini argument. The elementary
family calculation can be developed independently with those factorizations
as explicit hypotheses. The natural and alternating-five modules have different
families: two members in the first case, four in the second. The latter contract
also records that the two extra members are moved by the Sylow group.

These are unproved input contracts, not assertions of the source results.
`Conjugates.Reduction` proves their consequences; the owner of `Conjugates`
must construct all three inputs before discharging `ConjugateInput`.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates

open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The second elementary subgroup appearing before its identification with `Qˣ`. -/
noncomputable def opposite (R L : Subgroup G) (x : G) : Subgroup G :=
  (U L).map (MulAut.conj x).toMonoidHom ⊔ D R L

/-- The product assertions needed from C.5.6(1),(2). No Frattini invariance
or elementary-family assertion is included. -/
structure Factorization (R L : Subgroup G) (x : G) : Prop where
  core : Q R L = U L ⊔ D R L
  centralizes : D R L ≤ centralizer ((U L).map (MulAut.conj x).toMonoidHom : Set G)
  span : S R = (U L).map (MulAut.conj x).toMonoidHom ⊔ Q R L

/-- The localized C.5.6 product calculation, conditional on the published
Baumann input, and independent of both family calculations. -/
def FactorizationInput (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    ∀ x ∈ A, ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G) →
      Factorization R L x

/-- The B.2.21 calculation for the natural `L₂(2ⁿ)` and `A₃` modules.
It describes all maximum elementary subgroups, before the conjugation argument
identifies the second member. -/
def NaturalFamilyInput (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    ((∃ n, ChapterC.IsL2EvenBlock L n) ∨ ChapterC.IsAlternatingBlock L 3) →
    ∀ x ∈ A, ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G) →
      Factorization R L x → F R L = ⊥ →
        Stellmacher.elementaryAbelianMaxSubgroups (S R) = {Q R L, opposite R L x}

/-- The alternating-five module has two further maximum elementary subgroups.
They are interchanged by an element of `R ∩ L` outside `S`, and neither is
`R`-invariant. These assertions concern the permutation module, not the
different natural module for `L₂(4)`. -/
def AlternatingFamilyInput (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    ChapterC.IsAlternatingBlock L 5 →
    ∀ x ∈ A, ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G) →
      Factorization R L x → F R L = ⊥ →
        ∃ (E : Subgroup G) (r : G), r ∈ R ⊓ L ∧ r ∉ S R ∧
          E ≠ E.map (MulAut.conj r).toMonoidHom ∧
          Stellmacher.elementaryAbelianMaxSubgroups (S R) =
            {Q R L, opposite R L x, E, E.map (MulAut.conj r).toMonoidHom} ∧
          ¬ R ≤ normalizer (E : Set G) ∧
          ¬ R ≤ normalizer (E.map (MulAut.conj r).toMonoidHom : Set G)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates

end

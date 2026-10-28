module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration.Transport
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# The rank-one quotient needed in C.5.6

The remaining natural-model input specifies a surjective homomorphism from
LS onto an actual even-characteristic SL₂, with kernel exactly O₂(LS),
and identifies the image of S as a Sylow subgroup. It includes the SL₂(2)
case of an A₃-block. It contains no two-conjugate generation premise.

Its construction remains an independent source obligation. All hypotheses
of the consumer, including the already supplied span S = UˣQ, are retained.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(2)
and its proof, printed p.155 (PDF p.166); C.5.6, pp.156–157.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration
open Subgroup Matrix
universe u
variable {G : Type u} [Group G]

/-- A genuine rank-one quotient map, with the actual two-core as its kernel
and the actual Baumann image a Sylow subgroup. This includes SL₂(2) for A₃. -/
structure RankOneQuotient (R L : Subgroup G) (F : Type) [Field F] [Finite F] [CharP F 2] where
  quotient : (L ⊔ S R : Subgroup G) →* SpecialLinearGroup (Fin 2) F
  surjective : Function.Surjective quotient
  kernel : quotient.ker = (Q R L).subgroupOf (L ⊔ S R)
  sylow : Sylow 2 (SpecialLinearGroup (Fin 2) F)
  image : ((S R).subgroupOf (L ⊔ S R)).map quotient = sylow

/-- The missing source C.5.4(2) quotient identification and Sylow assertion.
This is a model obligation, not an assumption of two-conjugate generation. -/
@[expose] def RankOneQuotientInput [Finite G] (K : GroupClass.{u}) : Prop :=
  ∀ A H R L : Subgroup G, Configuration K A H R L → BaumannStructure H R L →
    ((∃ n, ChapterC.IsL2EvenBlock L n) ∨ ChapterC.IsAlternatingBlock L 3) →
    ∀ x ∈ A, ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G) →
      S R = (U L).map (MulAut.conj x).toMonoidHom ⊔ Q R L →
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
          Nonempty (RankOneQuotient R L F)
end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration

end

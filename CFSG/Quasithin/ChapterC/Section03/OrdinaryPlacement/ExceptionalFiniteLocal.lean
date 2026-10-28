module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceA5ReeLocal
public import Theory.SpecificGroups.Tits.TwoLocalFifteenFree

/-!
# Exceptional finite ordinary components in the original A₅ local source

The original A₅ seed forces a factor of fifteen in the normalizer of the
literal noncentral radical intersection in the component's central quotient.
The Tits two-local order obstruction excludes that quotient directly, using
the actual source subgroup maps and no additional normalizer hypothesis.

Source: Aschbacher--Smith C.3.5 and C.4.8, printed pp.150--153, specialized
to the genuine A₅ covering configuration of 4.2.12--13.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- The original A₅ local source has no ordinary Tits central quotient. -/
theorem no_ordinary_a5_tits
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Tits.ParrottGroup) : False :=
  h.no_ordinary_a5_of_fifteen_free_two_normalizers a K hK e
    Tits.normalizer_fifteen_free

/-- The Tits row supplies the normality conclusion needed by C.4.8. -/
theorem normalizes_a5_of_ordinary_tits
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Tits.ParrottGroup) :
    M ≤ normalizer (L : Set G) :=
  (h.no_ordinary_a5_tits a K hK e).elim

end CFSG.Quasithin.ChapterC.HypothesisC28

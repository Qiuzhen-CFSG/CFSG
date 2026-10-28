module

public import CFSG.Quasithin.ChapterG.Section03.Recognition.Reduced.Irreducible
public import CFSG.Quasithin.ChapterG.Section03.Recognition.Reduced.QuotientLifting

/-!
# Recognition of root-generated actions with trivial two-core

A spanning orbit of large binary root groups makes the quotient by the common
fixed space irreducible. Triviality of the intrinsic two-core makes this quotient
action faithful and preserves the large root groups. Irreducible recognition
therefore makes the quotient action surjective, and the fixed-space lifting
theorem identifies the original group with the full linear group.

This discharges both premises of quotient lifting from the root-orbit inputs
and the intrinsic two-core guard. No irreducibility or splitting of the original
action is assumed.

Source motivation: Aschbacher--Smith, G.3.1, printed pp.337--338, with the
separate trivial-two-core hypothesis supplied by its source applications.
-/

public section

open BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03.Reduced
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Subgroup (BinaryLinear.GL V)} {Δ : Set V}

/-- A root-generated spanning orbit with large roots and trivial intrinsic
two-core gives the full linear group on the original space. -/
theorem RootGeneratedOrbit.eq_top_of_twoCore_eq_bot [Finite G]
    (r : RootGeneratedOrbit G Δ) (hcore : pCore 2 G = ⊥) : G = ⊤ := by
  let ρ := fixedQuotientAction G
  let : Finite ρ.range := Finite.of_surjective ρ.rangeRestrict
    ρ.rangeRestrict_surjective
  have hquot : ρ.range = ⊤ := eq_top_of_irreducible_rootGeneratedOrbit
    (r.fixedQuotient hcore) r.fixedQuotient_irreducible
  exact eq_top_of_full_fixedQuotient r (fixedQuotientAction_injective hcore)
    (MonoidHom.range_eq_top.mp hquot)

end CFSG.Quasithin.ChapterG.Section03.Reduced

module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.Embeddings
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.OddExtensions

/-!
# The literal radical supplement in the nilpotent SL₂(5) row

The actual nontrivial perfect point component fills the SL₂(5) quotient
by the two-Fitting preimage. Since that preimage lies in the solvable
radical, it supplies the literal radical supplement in the source
nilpotent embedding row. Its containing two-core quotient is
nonquasisimple: a quasisimple group with trivial two-core cannot surject
onto odd-characteristic SL₂. The proved maximal-local radical theorem
therefore makes the containing group fix the original point, a contradiction.

The actual chosen-flag application discharges radical centralization from
the completed nonquasisimple producer. No embedding shortlist, splitting,
or exponent bound is assumed. Earlier geometry retains final discharge
by qt-d-1222-shadow-components; comparison assembly remains with
qt-d-1222-shadow-component-comparison.
Source: Aschbacher--Smith A.3.12(21), pp.47--48, and 11.4.2, p.776.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The actual point subgroup supplements the solvable radical; no splitting is used. -/
theorem nilpotent_five_radical_supplement {B J : Subgroup G}
    (hBJ : B ≤ J) [Group.IsPerfect B] [Nontrivial B]
    (hm : NilpotentFiveExtension (J ⧸ pCore 2 J)) :
    J = B ⊔ radicalIn J := by
  let C := B.subgroupOf J
  let e := subgroupOfEquivOfLe hBJ
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : Nontrivial C := e.surjective.nontrivial
  have hs := Frattini.fitting_seed_split_of_sl2_five C
    (Frattini.twoFitting_sl2_of_nilpotent_extension (by decide : 3 < 5) (by decide) hm)
  have hF : twoFittingCore J ≤ solvableRadical J :=
    le_solvableRadical _ inferInstance twoFittingCore_solvable
  have hr : C ⊔ solvableRadical J = ⊤ := by
    apply top_unique
    rw [← hs]
    exact sup_le (hF.trans le_sup_right) le_sup_left
  have hh := congrArg (map J.subtype) hr
  simpa only [C,Subgroup.map_sup,map_subgroupOf_eq_of_le hBJ,
    ← MonoidHom.range_eq_map,range_subtype,radicalIn] using hh.symm

/-- The containing quotient cannot be quasisimple in this odd extension row. -/
theorem nilpotent_five_not_quasisimple {J : Subgroup G}
    (hm : NilpotentFiveExtension (J ⧸ pCore 2 J)) :
    ¬ IsQuasisimple (J ⧸ pCore 2 J) := by
  intro hq
  let := hq
  exact Quasisimple.Classification.not_odd_sl2_extension
    (pCore_quotient_pCore_eq_bot 2) _ (by decide : Odd 5) hm

variable {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}
    {E : Closure.Geometry D}

/-- Radical centralization excludes the literal proper maximal container. -/
theorem not_nilpotent_five_overcomponent (h : EarlierGeometry E)
    (hrad : MaximalRadicalCentralization T) {J : Subgroup G}
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hlt : E.Kz < J) :
    ¬ NilpotentFiveExtension (J ⧸ pCore 2 J) := by
  intro hm
  let e := subgroupOfEquivOfLe (show E.Kz ≤ E.Kz ⊔ (T : Subgroup G) from le_sup_left)
  let := h.point_mem_local_family.1.perfect
  let : Group.IsPerfect E.Kz := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let : Nontrivial (E.Kz.subgroupOf (E.Kz ⊔ (T : Subgroup G))) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr h.point_mem_local_family.1.ne_bot
  let : Nontrivial E.Kz := e.injective.nontrivial
  exact not_radical_supplement h hrad hJ hlt (nilpotent_five_not_quasisimple hm)
    (nilpotent_five_radical_supplement hlt.le hm)

/-- On the chosen flag, the completed radical theorem supplies centralization. -/
theorem ofFlag_not_nilpotent_five_overcomponent
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    ¬ NilpotentFiveExtension (J ⧸ pCore 2 J) := by
  apply not_nilpotent_five_overcomponent h _ hJ hlt
  intro I hI hn
  exact ofFlag_maximal_radical_centralizes S hI hn

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof

module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Contracts
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Overgroups
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Automizer

/-!
# Compatible local actions from an odd family of J₄ overgroups

Pull a two-subgroup D of the pair automizer back to the actual ambient pair
stabilizer, then take a Sylow two-subgroup of this inverse image. Its image
is all of D. It acts on the family of max4-type subgroups containing S and R;
if that family has odd cardinality, a fixed subgroup M exists. Restricting
the chosen ambient lifts to M gives the requested automorphisms, with their
agreement on R proved through the subgroup inclusions.

This argument allows M to depend on D. It uses neither innerness of ambient
automorphisms nor an assumed invariant subgroup of the Frattini quotient.
The stronger universal placement assembly below remains conditional on
coverage and parity. The separate `Adequate` module gives an actor-wise
reducibility-or-placement reduction from its explicit local model inputs;
it does not require these two universal placement contracts.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher's *Overgroups of Sylow
subgroups in sporadic groups* (1986). The sufficient incidence contracts
are documented in `PairActions.Overgroups`.
-/

public section

open Subgroup
open Janko4.LocalStructure.SymmetricLinear
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
open EvenRankTwo

private def mapOvergroup {S R : Subgroup Janko4.Model}
    (b : pairStabilizer S R) (M : PairOvergroups S R) : PairOvergroups S R :=
  ⟨M.val.map b.val.toMonoidHom, (by
    intro x hx
    refine ⟨b.val.symm x, M.property.1 ?_, b.val.apply_symm_apply x⟩
    exact (b.property.1 (b.val.symm x)).mp (by simpa using hx)), (by
    intro x hx
    refine ⟨b.val.symm x, M.property.2.1 ?_, b.val.apply_symm_apply x⟩
    exact (b.property.2 (b.val.symm x)).mp (by simpa using hx)),
    M.property.2.2.map (fun e => (b.val.subgroupMap M.val).symm.trans e)⟩

private instance overgroupAction (S R : Subgroup Janko4.Model) :
    MulAction (pairStabilizer S R) (PairOvergroups S R) where
  smul := mapOvergroup
  one_smul M := by
    apply Subtype.ext
    change M.val.map (MonoidHom.id _) = M.val
    exact map_id _
  mul_smul b c M := by
    apply Subtype.ext
    change M.val.map (b.val * c.val).toMonoidHom =
      (M.val.map c.val.toMonoidHom).map b.val.toMonoidHom
    rw [map_map]
    rfl

private theorem restriction_surjective {S R : Subgroup Janko4.Model}
    (D : Subgroup (MulAut R)) (hD : D ≤ pairAutomizer S R) :
    let f : pairStabilizer S R →* MulAut R :=
      (pairAutomizer S R).subtype.comp (pairRestriction S R)
    Function.Surjective (f.subgroupComap D) := by
  intro f a
  obtain ⟨b, hb⟩ := pairRestriction_surjective S R ⟨a.val, hD a.property⟩
  have he : f b = a.val := congrArg Subtype.val hb
  refine ⟨⟨b, ?_⟩, Subtype.ext he⟩
  change f b ∈ D
  rw [he]
  exact a.property

/-- An odd number of actual local overgroups gives compatible lifts of every
acting two-group. The overgroup is selected by the action's fixed-point theorem. -/
theorem compatibleActions_of_odd_overgroups {S R : Subgroup Janko4.Model}
    (hodd : ¬ 2 ∣ Nat.card (PairOvergroups S R))
    (D : Subgroup (MulAut R)) (hD : D ≤ pairAutomizer S R) (htwo : IsPGroup 2 D) :
    ∃ (M : Subgroup Janko4.Model) (hRM : R ≤ M),
      S ≤ M ∧ Nonempty (M ≃* max4Subgroup) ∧
        ∀ a ∈ D, ∃ c : MulAut M,
          ∀ r : R, inclusion hRM (a r) = c (inclusion hRM r) := by
  let f : pairStabilizer S R →* MulAut R :=
    (pairAutomizer S R).subtype.comp (pairRestriction S R)
  let E := D.comap f
  let q : E →* D := f.subgroupComap D
  have hq : Function.Surjective q := restriction_surjective D hD
  let P : Sylow 2 E := Sylow.nonempty.some
  have hPmap : (P : Subgroup E).map q = ⊤ := by
    exact ((P.mapSurjective hq).is_maximal' (htwo.to_subgroup ⊤) le_top).symm
  let j : P →* pairStabilizer S R := E.subtype.comp (P : Subgroup E).subtype
  let : MulAction P (PairOvergroups S R) :=
    MulAction.compHom (PairOvergroups S R) j
  obtain ⟨M, hM⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card
    (PairOvergroups S R) hodd
  refine ⟨M.val, M.property.2.1, M.property.1, M.property.2.2, ?_⟩
  intro a ha
  have ha' : (⟨a, ha⟩ : D) ∈ (P : Subgroup E).map q := by rw [hPmap]; trivial
  obtain ⟨b, hb, he⟩ := ha'
  let p : P := ⟨b, hb⟩
  have hstable : M.val.map (j p).val.toMonoidHom = M.val :=
    congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hM) p)
  refine ⟨((j p).val.subgroupMap M.val).trans (MulEquiv.subgroupCongr hstable), ?_⟩
  intro r
  apply Subtype.ext
  change (a r : Janko4.Model) = (j p).val r
  have he' : f (j p) = a := congrArg Subtype.val he
  change (a r : Janko4.Model) = (f (j p) r : Janko4.Model)
  rw [he']


/-- Coverage and the independent incidence calculation discharge the two
premises of the fixed-point argument. Neither model input is asserted here. -/
theorem maximalFourPairActions_of_coverage_parity
    (hcover : MaximalFourPairCoverage) (hparity : MaximalFourPairParity) :
    MaximalFourPairActions := by
  intro _ _ _ S R h D hD htwo
  exact compatibleActions_of_odd_overgroups
    (hparity S R h (hcover S R h)) D hD htwo

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

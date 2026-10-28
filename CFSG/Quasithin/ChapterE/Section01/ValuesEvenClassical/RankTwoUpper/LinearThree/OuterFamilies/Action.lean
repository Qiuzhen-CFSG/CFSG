module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The faithful PSL₃ action of the ambient group

The given equivalence from the simple generalized Fitting subgroup transports
conjugation to the actual projective matrix group. Perfectness of that model
supplies nonabelianness, and the simple-socle theorem supplies faithfulness
and trivial two-core. The inverse image of the inner automorphisms is exactly
the socle, so an outer elementary actor remains outer under this embedding.

The binary case has rank at most two by the actual PGL₂(7) comparison.
For larger fields the sharp outer-actor rank estimate is a separate model
calculation; the transport theorem below retains that premise explicitly.

Source: Aschbacher--Smith E.1.14(1), printed p.214; standard-automorphism
coverage is GLS3, Theorem 2.5.12(a) and §2.7.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- Actual conjugation on the marked projective matrix socle. -/
@[expose] noncomputable def modelAction
    (e : generalizedFitting G ≃* PSL(3,F)) : G →* MulAut PSL(3,F) :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

variable [IsSimpleGroup (generalizedFitting G)]

omit [Finite G] [Finite F] in
/-- The genuine projective model discharges the nonabelianness premise of
the simple-socle structure theorem, including over the binary field. -/
theorem socle_nonabelian (e : generalizedFitting G ≃* PSL(3,F)) :
    ¬ IsMulCommutative (generalizedFitting G) := by
  let := Atlas.psl_perfect (F := F) 3 (by decide)
  let : Group.IsPerfect (generalizedFitting G) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.IsPerfect.not_isMulCommutative (generalizedFitting G)

omit [Finite F] in
/-- Faithfulness uses the actual generalized Fitting subgroup. -/
theorem modelAction_injective (e : generalizedFitting G ≃* PSL(3,F)) :
    Function.Injective (modelAction e) :=
  (MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot _
      (SimpleSocle.centralizer_eq_bot (socle_nonabelian e)))

omit [Finite F] in
/-- The preimage of the actual inner automorphisms is exactly the socle. -/
theorem modelAction_comap_inner (e : generalizedFitting G ≃* PSL(3,F)) :
    (MulAut.innerSubgroup PSL(3,F)).comap (modelAction e) = generalizedFitting G := by
  change ((MulAut.innerSubgroup PSL(3,F)).comap (MulAut.congr e).toMonoidHom).comap
    (MulAut.conjNormal : G →* MulAut (generalizedFitting G)) = _
  rw [← MulAut.map_innerSubgroup_congr e,
    Subgroup.comap_map_eq_self_of_injective (MulAut.congr e).injective,
    MulAut.conjNormal_comap_innerSubgroup,
    SimpleSocle.centralizer_eq_bot (socle_nonabelian e), sup_bot_eq]

omit [Finite F] in
/-- The model supplies the exact ambient two-core identity used by E0. -/
theorem twoCore_eq_bot (e : generalizedFitting G ≃* PSL(3,F))
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    pCore 2 G = ⊥ :=
  (SimpleSocle.structure_of_sylow_supplement (socle_nonabelian e) T hLT).2.2.1

omit [IsSimpleGroup (generalizedFitting G)] in
/-- The ambient action is covered by the genuine linear, field and graph
automorphisms, with no exception for the fields of orders two or four. -/
theorem modelAction_range_le_standard (e : generalizedFitting G ≃* PSL(3,F))
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f) :
    (modelAction e).range ≤ Matrix.PSL3.OuterSolvable.standard F := by
  rw [Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F hf hF]
  exact le_top

/-- Transport a sharp bound on outer elementary subgroups of the actual
automorphism group to the source ambient group. -/
theorem outer_rank_le_of_model_bound (e : generalizedFitting G ≃* PSL(3,F)) {f : ℕ}
    (hbound : ∀ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 2 E →
      ¬ E ≤ MulAut.innerSubgroup PSL(3,F) → Group.rank E ≤ f + 1)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (houter : ¬ A ≤ generalizedFitting G) : Group.rank A ≤ f + 1 := by
  let := hA
  let E := A.map (modelAction e)
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.map (modelAction e)
  have hEO : ¬ E ≤ MulAut.innerSubgroup PSL(3,F) := by
    intro h
    apply houter
    have hc := map_le_iff_le_comap.mp h
    rwa [modelAction_comap_inner e] at hc
  exact (Group.rank_congr (A.equivMapOfInjective _ (modelAction_injective e))).le.trans
    (hbound E hE hEO)

/-- The smallest field needs rank two, rather than the false outer bound one. -/
theorem rank_le_two_of_card_two (e : generalizedFitting G ≃* PSL(3,F))
    (hF : Nat.card F = 2) (A : Subgroup G) (hA : IsElementaryAbelian 2 A) :
    Group.rank A ≤ 2 := by
  let := hA
  let E := A.map (modelAction e)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (modelAction e)
  have h := E.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 E)
  rw [Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two F hF] at h
  exact (Group.rank_congr (A.equivMapOfInjective _ (modelAction_injective e))).le.trans h

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies

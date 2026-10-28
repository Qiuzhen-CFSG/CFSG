module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.GlobalSplitting.BestOffenderSplitting
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.GlobalSplitting.FittingComplement
public import Theory.GroupTheory.CenterlessProduct
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Inclusion-compatible global products and support sum

The actual source groups Gᵢ are centerless and commute at distinct indices,
so they form an independent family. Multiplying their original inclusions
identifies their product with E. The checked best-offender splitting then
adjoins the disjoint commuting residual J_P(C_G(F)) to obtain J(G,V).
The simultaneous Fitting complement gives a multiplication equivalence
F × C_F(G)(J*) ≃ F(G). Every coordinate map is the original inclusion.

Finally [V,Gᵢ]=[V,Fᵢ] transports the checked independent plane sum to the
source supports without changing any vector inclusion. These constructions
supply the product and sum fields of the parent's Decomposition witness.

Source: Aschbacher–Smith, B.1.9(1–3), printed pp.71–72 (PDF pp.82–83).
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- Distinct enumerated source factors commute under their ambient inclusions. -/
theorem planeFactors_commute (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    Pairwise fun i j : Fin (cubicCount ρ) => ∀ x y : G,
      x ∈ planeGroup ρ (cubicFactor ρ i) → y ∈ planeGroup ρ (cubicFactor ρ j) →
      Commute x y := by
  intro i j hij x y hx hy
  exact (mem_centralizer_iff.mp (planeGroups_commute ρ hρ hlocal
    (cubicFactor_mem ρ i) (cubicFactor_mem ρ j)
    (fun he => hij (cubicFactor_injective ρ he)) hx) y hy).symm

/-- Centerlessness strengthens pairwise commutation to independence. -/
theorem planeFactors_independent (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    iSupIndep (fun i => planeGroup ρ (cubicFactor ρ i)) := by
  apply iSupIndep_of_centerless_of_pairwise_commute _ _ (planeFactors_commute ρ hρ hlocal)
  intro i
  obtain ⟨e⟩ := planeGroup_model ρ hρ hlocal (cubicFactor_mem ρ i)
  apply le_bot_iff.mp
  intro x hx
  apply e.injective
  rw [map_one]
  apply Theory.GroupTheory.NormalSymmetricThreePairRank.symmetricThree_center_trivial
  intro y
  obtain ⟨z, rfl⟩ := e.surjective y
  simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)

/-- The product of the literal subgroup inclusions, with range E. -/
noncomputable def planeProduct (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    ((i : Fin (cubicCount ρ)) → planeGroup ρ (cubicFactor ρ i)) ≃* planeGenerated ρ :=
  (MonoidHom.ofInjective (Subgroup.injective_noncommPiCoprod_of_iSupIndep
    (hcomm := planeFactors_commute ρ hρ hlocal) (planeFactors_independent ρ hρ hlocal))).trans
      (MulEquiv.subgroupCongr Subgroup.noncommPiCoprod_range)

/-- Each coordinate is included as the original subgroup of G. -/
theorem planeProduct_single (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ)
    (i : Fin (cubicCount ρ)) (g : planeGroup ρ (cubicFactor ρ i)) :
    (planeProduct ρ hρ hlocal (Pi.mulSingle i g) : G) = g :=
  Subgroup.noncommPiCoprod_mulSingle (hcomm := planeFactors_commute ρ hρ hlocal) i g

/-- The source product for J(G,V), including both inclusion formulas. -/
theorem exists_offenderProduct
    (hρ : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ) :
    ∃ e : (((i : Fin (cubicCount ρ)) → planeGroup ρ (cubicFactor ρ i)) ×
      centralizingBestGenerated ρ) ≃* offenderSubgroup ρ,
      (∀ i g, (e (Pi.mulSingle i g, 1) : G) = g) ∧
      (∀ g, (e (1, g) : G) = g) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (planeGenerated ρ) (centralizingBestGenerated ρ)
    (disjoint_iff.mpr (planeGenerated_inf_centralizingBestGenerated_eq_bot ρ hρ hlocal))
    (le_centralizer_iff.mp (centralizingBestGenerated_le_centralizer_planeGenerated ρ hρ hlocal))
  let e' := ((planeProduct ρ hρ hlocal).prodCongr (MulEquiv.refl _)).trans
    (e.trans (MulEquiv.subgroupCongr
      (offenderSubgroup_eq_planeGenerated_sup_centralizingBestGenerated ρ hρ hcore hlocal).symm))
  refine ⟨e', ?_, ?_⟩
  · intro i g
    change (e (planeProduct ρ hρ hlocal (Pi.mulSingle i g), 1) : G) = g
    rw [he, OneMemClass.coe_one, mul_one, planeProduct_single]
  · intro g
    change (e (planeProduct ρ hρ hlocal 1, g) : G) = g
    rw [he, map_one, OneMemClass.coe_one, one_mul]

/-- The Fitting product is multiplication in the original ambient group. -/
theorem exists_fittingProduct
    (hρ : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ) :
    ∃ e : (fittingMoved ρ ×
      ↥(fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G))) ≃* fittingSubgroup G,
      ∀ f c, (e (f, c) : G) = (f : G) * (c : G) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (fittingMoved ρ) (fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G))
    (fittingMoved_disjoint_fitting_centralizer ρ hρ hcore hlocal)
    ((fittingMoved_le_centralizer_fitting ρ hcore hlocal).trans (centralizer_le inf_le_left))
  exact ⟨e.trans (MulEquiv.subgroupCongr
    (fitting_eq_fittingMoved_sup_centralizer ρ hρ hcore hlocal).symm), he⟩

/-- The source support sum, preserving the original vector inclusions. -/
theorem exists_planeGroupSum (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    ∃ e : ((i : Fin (cubicCount ρ)) →
        subspaceCommutator ρ ⊤ (planeGroup ρ (cubicFactor ρ i))) ≃ₗ[ZMod 2]
      subspaceCommutator ρ ⊤ (fittingMoved ρ),
      ∀ i x, (e (Pi.single i x) : V) = x := by
  let t := fun i => LinearEquiv.ofEq _ _
    (planeGroup_support_eq ρ hlocal (cubicFactor_mem ρ i))
  let e := (LinearEquiv.piCongrRight t).trans (planeSum ρ hρ hlocal)
  refine ⟨e, ?_⟩
  intro i x
  have hs : LinearEquiv.piCongrRight t (Pi.single i x) = Pi.single i (t i x) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [LinearEquiv.piCongrRight_apply, Pi.single_eq_of_ne hji]
  change (planeSum ρ hρ hlocal (LinearEquiv.piCongrRight t (Pi.single i x)) : V) = x
  rw [hs, planeSum_single]
  rfl

end CFSG.Quasithin.ChapterB.FittingStructure

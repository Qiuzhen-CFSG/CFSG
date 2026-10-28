module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Descent
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable
public import Theory.GroupAction.AutomorphismFixedResidualTransport

/-!
# Two-residuals of descended symplectic fixed groups

Over a nonbinary finite field of characteristic two, root commutators make
Sp₄ perfect, hence two-perfect. At the binary endpoint the explicit polar
representation identifies Sp₄(2) with S₆. Its alternating subgroup is generated
by elements of order three and has index two, so it is exactly the two-residual.
Descent therefore identifies the fixed-group two-residual with Sp₄(K)′ in both
cases, retaining the ambient coefficient inclusion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 16.1.4(4), printed p.1171.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
open Subgroup

private theorem symmetric_twoResidual :
    pResidual 2 (Equiv.Perm (Fin 6)) = commutator (Equiv.Perm (Fin 6)) := by
  rw [alternatingGroup.commutator_perm_eq (by norm_num)]
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 6)).index = 2 ^ 1
    simp
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating, closure_le]
    intro g hg
    apply mem_pResidual_of_orderOf_coprime
    rw [hg.orderOf]
    decide

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The two-residual is the derived subgroup, including the binary endpoint. -/
theorem twoResidual_eq_commutator : pResidual 2 (Sp F) = commutator (Sp F) := by
  by_cases htwo : Nat.card F = 2
  · let e := (Binary.fieldEquivSp (Binary.fieldEquivZModTwo F htwo)).trans
      Binary.symmetricSixEquiv.symm
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_pResidual, symmetric_twoResidual, map_commutator_eq,
      MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  · have hq : 2 < Nat.card F := by
      let _ := Fintype.ofFinite F
      have h := Fintype.one_lt_card (α := F)
      rw [← Nat.card_eq_fintype_card] at h
      omega
    let _ := perfect_of_card_gt_two hq
    rw [Group.IsPerfect.commutator_eq_top]
    apply (pResidual_eq_top_iff 2 _).mpr
    intro N hN hp
    let _ := hN
    have : Subsingleton (Sp F ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The fixed-group residual is the exact commutator carrier over the fixed field. -/
def residualEquiv (σ : F ≃+* F) :
    pResidual 2 (fieldAutomorphism σ).fixedSubgroup ≃* commutator (Sp (fixedField σ)) :=
  ((pResidual 2 _).equivMapOfInjective (fixedEquiv σ).toMonoidHom
    (fixedEquiv σ).injective).trans
      (MulEquiv.subgroupCongr ((map_pResidual 2 (fixedEquiv σ)).trans
        twoResidual_eq_commutator))

/-- Residual descent uses the same entries as fixed-group descent. -/
@[simp] theorem residualEquiv_coe (σ : F ≃+* F)
    (g : pResidual 2 (fieldAutomorphism σ).fixedSubgroup) :
    (residualEquiv σ g : Sp (fixedField σ)) = fixedEquiv σ g.val := by rfl

/-- The residual equivalence retains the original ambient embedding. -/
@[simp] theorem residualEquiv_inclusion (σ : F ≃+* F)
    (g : pResidual 2 (fieldAutomorphism σ).fixedSubgroup) :
    coefficientInclusion (fixedField σ) (residualEquiv σ g : Sp (fixedField σ)) =
      (g.val : Sp F) := by
  rw [residualEquiv_coe, fixedEquiv_inclusion]

/-- The inverse equivalence also retains the coefficient inclusion. -/
@[simp] theorem residualEquiv_symm_coe (σ : F ≃+* F)
    (g : commutator (Sp (fixedField σ))) :
    (((residualEquiv σ).symm g).val : Sp F) =
      coefficientInclusion (fixedField σ) (g : Sp (fixedField σ)) := by
  have h := residualEquiv_inclusion σ ((residualEquiv σ).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

/-- Equality of the embedded residual and the embedded derived subfield group. -/
theorem embedded_residual_eq (σ : F ≃+* F) :
    (pResidual 2 (fieldAutomorphism σ).fixedSubgroup).map
        (fieldAutomorphism σ).fixedSubgroup.subtype =
      (commutator (Sp (fixedField σ))).map (coefficientInclusion (fixedField σ)) := by
  rw [← twoResidual_eq_commutator, ← map_pResidual 2 (fixedEquiv σ), map_map]
  congr 1
  ext g : 1
  exact (fixedEquiv_inclusion σ g).symm

/-- A supplied intertwining equivalence transports this computed residual model.
The existence of such an equivalence is not asserted here. -/
def residualEquivOfCompatible {G : Type*} [Group G]
    (e : G ≃* Sp F) (a : MulAut G) (σ : F ≃+* F)
    (he : ∀ x, e (a x) = fieldAutomorphism σ (e x)) :
    pResidual 2 a.fixedSubgroup ≃* commutator (Sp (fixedField σ)) :=
  (MulAut.fixedResidualEquivOfCompatible 2 e a (fieldAutomorphism σ) he).trans
    (residualEquiv σ)

/-- Compatible residual transport preserves the given ambient equivalence. -/
@[simp] theorem residualEquivOfCompatible_inclusion {G : Type*} [Group G]
    (e : G ≃* Sp F) (a : MulAut G) (σ : F ≃+* F)
    (he : ∀ x, e (a x) = fieldAutomorphism σ (e x))
    (g : pResidual 2 a.fixedSubgroup) :
    coefficientInclusion (fixedField σ)
        (residualEquivOfCompatible e a σ he g : Sp (fixedField σ)) =
      e (g.val : G) := by
  change coefficientInclusion (fixedField σ)
      (residualEquiv σ (MulAut.fixedResidualEquivOfCompatible 2 e a
        (fieldAutomorphism σ) he g) : Sp (fixedField σ)) = _
  rw [residualEquiv_inclusion, MulAut.fixedResidualEquivOfCompatible_apply]

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual

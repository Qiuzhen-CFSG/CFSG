module

public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover
public import Theory.SpecificGroups.PSL3.CartanActions.FullTorusFixer
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage

/-!
# Excluding the cubic center under a full Borel torus fixer

An odd-center quasisimple cover of PSL₃(4) with nontrivial center is SL₃(4),
over its prescribed projective projection. If an automorphism preserves the
Borel, fixes the full torus modulo its unipotent radical and moves the diagram,
its field factor is trivial. The lifted graph factor inverts the scalar cubic
center. Pointwise fixation of the cover's center therefore forces it to vanish.

The quotient action is retained literally. The canonical central-quotient
application and the actual odd Hall application discharge the equivariance
and full torus hypotheses used in Aschbacher–Smith 14.2.12, printed pp.983–984.
-/

public section

open scoped MatrixGroups
open Subgroup PerfectCentralCovering Theory.GroupTheory
open Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage

namespace Matrix.PSL3.BinaryOddCenterCover.FullTorusFixer
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem field_eq_one_of_graph_torus_fixer (hF : Nat.card F = 4)
    (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hB : (borel F).map
      (linearConj F m * fieldAction F σ * oppositionGraph F).toMonoidHom = borel F)
    (hfix : ∀ x ∈ torus F,
      (linearConj F m * fieldAction F σ * oppositionGraph F) x * x⁻¹ ∈ unipotent F) :
    σ = 1 := by
  have hs := CartanActions.FullTorusFixer.map_unipotent_of_map_borel
    (n := 2) (by simpa using hF) _ hB
  have hb : (unipotent F).map
      (fieldAction F σ * oppositionGraph F).toMonoidHom = unipotent F := by
    change (unipotent F).map
      ((fieldAction F σ).toMonoidHom.comp (oppositionGraph F).toMonoidHom) = _
    rw [← Subgroup.map_map, oppositionGraph_unipotent, fieldAction_unipotent]
  rw [mul_assoc] at hs
  have hm : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F := by
    change (unipotent F).map
      ((linearConj F m).toMonoidHom.comp
        (fieldAction F σ * oppositionGraph F).toMonoidHom) = _ at hs
    rwa [← Subgroup.map_map, hb] at hs
  have ht := NormalizerForm.linearConj_upperTriangular F m hm
  have hu (u : Fˣ) : Units.map σ.toMonoidHom u = u := by
    have h := ResidualLinear.parameters_eq_of_displacement m ht
      (1, (Units.map σ.toMonoidHom u)⁻¹) (u, 1) (by
        simpa only [MulAut.mul_apply, oppositionGraph_torusMap,
          field_torusMap, inv_one, map_one, map_inv] using
          hfix (torusMap F (u,1)) ⟨(u,1),rfl⟩)
    have hh := (ResidualParameters.projective_parameters_eq_iff _ _).mp h
    have hi : u⁻¹ = (Units.map σ.toMonoidHom u)⁻¹ := by simpa using hh.1
    exact inv_injective hi.symm
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · exact congrArg Units.val (hu (Units.mk0 x hx))

omit [Finite F] [CharP F 2] in
private theorem graphActor_inverts_center (g : GL (Fin 3) F)
    (x : SL(3,F)) (hx : x ∈ center SL(3,F)) :
    (linearConjSL F g * graphSL F) x = x⁻¹ := by
  have ht : SpecialLinearGroup.transpose x = x := by
    obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hx
    apply Subtype.ext
    change x.val.transpose = x.val
    rw [← hr]
    simp
  change linearConjSL F g (SpecialLinearGroup.transpose x)⁻¹ = x⁻¹
  rw [ht]
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL]
  have hc := (SpecialLinearGroup.toGL_mem_center_iff x⁻¹).mpr
    ((center SL(3,F)).inv_mem hx)
  rw [mem_center_iff.mp hc g, mul_inv_cancel_right]

omit [Finite F] [CharP F 2] in
private theorem central_cube (x : SL(3,F)) (hx : x ∈ center SL(3,F)) : x ^ 3 = 1 := by
  obtain ⟨r, hr3, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hx
  apply Subtype.ext
  change x.val ^ 3 = 1
  rw [← hr, ← map_pow, (by simpa using hr3 : r ^ 3 = 1), map_one]

theorem center_eq_bot_of_diagram_moving_torus_fixer
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hF : Nat.card F = 4) (e : Q ⧸ center Q ≃* PSL(3,F))
    (ho : Odd (Nat.card (center Q)))
    (α : MulAut Q) (β : MulAut PSL(3,F))
    (hcomm : ∀ x, β (e (QuotientGroup.mk x)) = e (QuotientGroup.mk (α x)))
    (hcenter : ∀ z ∈ center Q, α z = z)
    (hB : (borel F).map β.toMonoidHom = borel F)
    (hfix : ∀ x ∈ torus F, β x * x⁻¹ ∈ unipotent F)
    (hmove : ¬ (PreservesPointType F β ∧ PreservesLineType F β)) : center Q = ⊥ := by
  by_contra hz
  obtain ⟨_, j, hj⟩ := nontrivial_center_recognition_four hF e ho hz
  let a : MulAut SL(3,F) := MulAut.congr j.symm α
  have hp (x : SL(3,F)) : e (QuotientGroup.mk (j x)) = projection F x :=
    DFunLike.congr_fun hj x
  have ha : centerAction F a = β := by
    ext y
    obtain ⟨x,rfl⟩ := projection_surjective F y
    change projection F (j.symm (α (j x))) = β (projection F x)
    rw [← hp, j.apply_symm_apply, ← hcomm, hp]
  have hs : β ∈ standard F := by
    rw [standard_eq_top_of_two_power_card F (m := 2) (by decide) (by simpa using hF)]
    trivial
  obtain ⟨m, σ, he | he⟩ := ResidualLinear.standard_opposition_factorization β hs
  · apply hmove
    apply (mem_diagramTrivial_iff F β).mp
    apply (mem_diagramTrivial F β).mpr
    intro b
    rw [he]
    exact linearField_mapsParabolicType F _ ((ExtensionBorel.linearField F).mul_mem
      (Subgroup.mem_sup_left ⟨m,rfl⟩) (Subgroup.mem_sup_right ⟨σ,rfl⟩)) b
  · have hσ : σ = 1 := field_eq_one_of_graph_torus_fixer hF m σ
      (by rwa [← he]) (by simpa only [← he] using hfix)
    have he' : β = linearConj F (m * reversalGL F) * graph F := by
      rw [he, hσ, map_one, mul_one]
      change linearConj F m * (linearConj F (reversalGL F) * graph F) = _
      rw [← mul_assoc, ← map_mul]
    have heSL : a = linearConjSL F (m * reversalGL F) * graphSL F := by
      apply ActorCoverage.centerAction_injective F
      rw [ha, map_mul]
      exact he'
    apply hz
    apply le_antisymm _ bot_le
    intro z hz
    let x : SL(3,F) := j.symm z
    have hx : x ∈ center SL(3,F) := by
      apply mem_center_iff.mpr
      intro y
      apply j.injective
      simp only [map_mul, x, j.apply_symm_apply]
      exact mem_center_iff.mp hz (j y)
    have hax : a x = x := by
      change j.symm (α (j x)) = x
      rw [hcenter (j x) (by simpa [x] using hz), j.symm_apply_apply]
    have hi : x⁻¹ = x := (graphActor_inverts_center _ x hx).symm.trans
      (heSL ▸ hax)
    have h2 : x ^ 2 = 1 := by simpa only [pow_two, hi] using inv_mul_cancel x
    have h1 : x = 1 := by simpa only [pow_succ, h2, one_mul] using central_cube x hx
    exact mem_bot.mpr (by simpa [x] using congrArg j h1)

theorem center_eq_bot_of_centralQuotient_diagram_fixer
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hF : Nat.card F = 4) (e : Q ⧸ center Q ≃* PSL(3,F))
    (ho : Odd (Nat.card (center Q))) (α : MulAut Q)
    (hcenter : ∀ z ∈ center Q, α z = z)
    (hB : (borel F).map (MulAut.centralQuotientAction e α).toMonoidHom = borel F)
    (hfix : ∀ x ∈ torus F, MulAut.centralQuotientAction e α x * x⁻¹ ∈ unipotent F)
    (hmove : ¬ (PreservesPointType F (MulAut.centralQuotientAction e α) ∧
      PreservesLineType F (MulAut.centralQuotientAction e α))) : center Q = ⊥ := by
  apply center_eq_bot_of_diagram_moving_torus_fixer hF e ho α
    (MulAut.centralQuotientAction e α) _ hcenter hB hfix hmove
  exact fun x => MulAut.centralQuotientAction_apply e α x

theorem center_eq_bot_of_centralQuotient_hall_fixer
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hF : Nat.card F = 4) (e : Q ⧸ center Q ≃* PSL(3,F))
    (ho : Odd (Nat.card (center Q))) (α : MulAut Q)
    (hcenter : ∀ z ∈ center Q, α z = z)
    (hB : (borel F).map (MulAut.centralQuotientAction e α).toMonoidHom = borel F)
    (D : Subgroup (borel F)) (hD : IsHallSubgroup OddHall.oddPrimes D)
    (hfix : ∀ d ∈ D, MulAut.centralQuotientAction e α d.val = d.val)
    (hmove : ¬ (PreservesPointType F (MulAut.centralQuotientAction e α) ∧
      PreservesLineType F (MulAut.centralQuotientAction e α))) : center Q = ⊥ := by
  let β := MulAut.centralQuotientAction e α
  let aB : MulAut (borel F) := (β.subgroupMap (borel F)).trans
    (MulEquiv.subgroupCongr hB)
  have hh : ∀ d ∈ D, aB d = d := fun d hd => Subtype.ext (hfix d hd)
  apply center_eq_bot_of_centralQuotient_diagram_fixer hF e ho α hcenter hB _ hmove
  intro x hx
  let b : borel F := ⟨x,torus_le_borel F hx⟩
  have h := mem_map_of_mem (borel F).subtype
    (OddHall.fixed_mod_core_of_pointwise_hall
      (CartanActions.FullTorusFixer.borel_twoCore_index_odd (n := 2) (by simpa using hF))
      aB D hD hh b)
  rw [twoCore_eq F (n := 2) (by simpa using hF),
    map_subgroupOf_eq_of_le (unipotent_le_borel F)] at h
  exact h

end Matrix.PSL3.BinaryOddCenterCover.FullTorusFixer

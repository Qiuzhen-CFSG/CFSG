module
public import Theory.Representation.OrthogonalFourPlusMatrix.ElementaryNormalizerGeometry
public import Theory.Representation.OrthogonalFourPlusMatrix.RankTwoFactorSwap
public import Theory.Representation.OrthogonalFourPlusMatrix.RankTwoMovedPoint
public import Theory.GroupTheory.ExchangePrimeFixer
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# A cubic fixing the original rank-two displacement point

A rank-two involution exchanges the two SL₂(4) factors. In any subgroup
containing a full inner Sylow two-subgroup, a cubic whose displacement
under that exchange lies in the Sylow can be corrected to a fixed cubic.
The resulting inner isometry preserves the nonsingular displacement line;
determinant preservation forces it to fix the line pointwise.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
refs/quasithin.pdf. The chapter application supplies the original L₁*,
its core Sylow and the critical involution in O₂(L₁T).
-/

public noncomputable section
open Subgroup

namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Representation Representation.BinaryOffender
open InvolutionResidual Theory.GroupTheory
local instance : Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

theorem rank_two_conjugation_exchanges (t : linearNormalizer action)
    (ht2 : t^2=1) (hr : NaturalTensor.operatorFixedCodim t.val.val=2) :
    (∀ a : SL, (normalizerConjugation t (a,1)).1=1) ∧
      (∀ a : SL, (normalizerConjugation t (1,a)).2=1) := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup SL := Representation.SL2FourNatural.alternatingFiveEquiv.isSimpleGroup
  let : IsQuasisimple SL := {
    toIsPerfect := by
      let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
        ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      exact Group.IsPerfect.ofSurjective
        (f := Representation.SL2FourNatural.alternatingFiveEquiv.symm.toMonoidHom)
        Representation.SL2FourNatural.alternatingFiveEquiv.symm.surjective
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := F))).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  rcases Theory.GroupTheory.AutomorphismSquare.normal_form
    (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := F))
    (normalizerConjugation t) with ⟨a,b,he⟩ | ⟨a,b,he⟩
  · exfalso
    let e := LinearMap.GeneralLinearGroup.toLinearEquiv t.val
    have he2 : e^2=1 := by
      apply LinearEquiv.ext
      intro v
      exact congrArg (fun z : linearNormalizer action => z.val.val v) ht2
    apply rank_two_involution_not_normalize_leftFactor e (normalizer_linearEquiv_mem t) he2 hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨_,⟨g,rfl⟩,rfl⟩
      refine ⟨a g,?_⟩
      apply LinearEquiv.ext
      intro v
      have hh := normalizerConjugation_action t (g,1) (e.symm v)
      rw [he] at hh
      change action (a g,b 1) (e (e.symm v)) = e (action (g,1) (e.symm v)) at hh
      rw [map_one,e.apply_symm_apply] at hh
      exact hh
    · rw [card_map_of_injective (MulAut.conj e).injective]
  · constructor
    · intro x
      rw [he]
      exact a.map_one
    · intro x
      rw [he]
      exact b.map_one

theorem inner_fixes_rank_two_displacement (t : linearNormalizer action)
    (ht2 : t^2=1) (hr : NaturalTensor.operatorFixedCodim t.val.val=2)
    (b : G) (hb : normalizerConjugation t b=b) :
    ∀ z ∈ (t.val.val-LinearMap.id).range, action b z=z := by
  obtain ⟨v,hv,hline⟩ := rank_two_involution_moved_point t ht2 hr
  have hcomm (w : V) : action b (t.val.val w)=t.val.val (action b w) := by
    simpa only [hb] using normalizerConjugation_action t b w
  have hpres (z : V) (hz : z ∈ (t.val.val-LinearMap.id).range) :
      action b z ∈ (t.val.val-LinearMap.id).range := by
    obtain ⟨w,rfl⟩ := hz
    refine ⟨action b w,?_⟩
    change t.val.val (action b w)-action b w=action b (t.val.val w-w)
    rw [map_sub,hcomm]
  have hvMem : v ∈ (t.val.val-LinearMap.id).range := by
    rw [hline]
    exact Submodule.subset_span (Set.mem_singleton v)
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hline ▸ hpres v hvMem)
  have hdet : (c^2)*v.det=v.det := by
    have hh := matrixAction_det b v
    change (action b v).det=v.det at hh
    rw [←hc,Matrix.det_smul] at hh
    exact hh
  have hc1 : c=1 := CharTwo.sq_injective (mul_right_cancel₀ hv
    (hdet.trans (one_mul v.det).symm))
  have hfix : action b v=v := by simpa only [hc1,one_smul] using hc.symm
  intro z hz
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp (hline ▸ hz)
  change matrixAction b (c • v)=c • v
  rw [map_smul]
  exact congrArg (fun w : V => c • w) hfix

theorem exists_cubic_fixing_rank_two_displacement
    (A : Subgroup G) (S : Sylow 2 G) (hSA : (S : Subgroup G) ≤ A)
    (t : linearNormalizer action) (ht2 : t^2=1)
    (hr : NaturalTensor.operatorFixedCodim t.val.val=2)
    (a : G) (ha : a ∈ A) (ha3 : orderOf a=3)
    (hdisp : normalizerConjugation t a*a⁻¹ ∈ S) :
    ∃ b ∈ A, orderOf b=3 ∧
      ∀ z ∈ (t.val.val-LinearMap.id).range, action b z=z := by
  let S₁ := (S : Subgroup G).map (MonoidHom.fst _ _)
  let S₂ := (S : Subgroup G).map (MonoidHom.snd _ _)
  have hp : IsPGroup 2 (S₁.prod S₂) := by
    obtain ⟨n,hn⟩ := (S.isPGroup'.map (MonoidHom.fst _ _)).exists_card_eq
    obtain ⟨m,hm⟩ := (S.isPGroup'.map (MonoidHom.snd _ _)).exists_card_eq
    exact IsPGroup.of_card (n := n+m) (by
      rw [Nat.card_congr (S₁.prodEquiv S₂).toEquiv,Nat.card_prod,hn,hm,pow_add])
  have he : (S : Subgroup G)=S₁.prod S₂ :=
    (S.is_maximal' hp (fun g hg => ⟨mem_map_of_mem _ hg,mem_map_of_mem _ hg⟩)).symm
  have hproj (g : G) (hg : g ∈ S) : (1,g.2) ∈ S := by
    change g ∈ (S : Subgroup G) at hg
    change (1,g.2) ∈ (S : Subgroup G)
    rw [he] at hg ⊢
    exact ⟨one_mem _,hg.2⟩
  have ha1 : a≠1 := by intro he; rw [he,orderOf_one] at ha3; omega
  have haS : a ∉ S := by
    intro has
    have hh := S.isPGroup'.dvd_orderOf (g := ⟨a,has⟩)
      (fun he => ha1 (congrArg Subtype.val he))
    rw [←S.toSubgroup.orderOf_coe,ha3] at hh
    norm_num at hh
  obtain ⟨hl,hr'⟩ := rank_two_conjugation_exchanges t ht2 hr
  have hα (g : G) : normalizerConjugation t (normalizerConjugation t g)=g := by
    have hh := congrArg (fun z : MulAut G => z g) (congrArg normalizerConjugation ht2)
    simpa only [pow_two,map_mul,map_one,MulAut.mul_apply,MulAut.one_apply] using hh
  obtain ⟨b,hb,hb3,hfix⟩ := Theory.GroupTheory.exists_fixed_prime_element_of_exchange
    A S hproj hSA (normalizerConjugation t) hα hl hr' a ha haS 3 Nat.prime_three
    (ha3 ▸ pow_orderOf_eq_one a) hdisp
  exact ⟨b,hb,hb3,inner_fixes_rank_two_displacement t ht2 hr b hfix⟩

end ClassicalOrthogonal.FourPlusMatrix.Binary

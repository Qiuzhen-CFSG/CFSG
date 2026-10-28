module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Recognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Linear
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Coverage

/-!
# Recognition with a prescribed SL3(2) marking

A faithful, fully moving binary action with a small involution has order
eight. All automorphisms of SL3(2) are inner or inner times the diagram
automorphism. Changing coordinates therefore gives exactly the natural or
dual action for ANY prescribed marking. The geometry must still exclude
the natural branch; an independent marking is not a duality proof.

Source: Meierfrankenfeld--Stellmacher (1993), (1.4)--(1.5), applied in
(4.5.4)(iii), p.899.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition
open DistanceFour.Linear
open Escape.Initial.Natural.Splitting
open Matrix.PSL3Two.MarkedAutomorphisms

private noncomputable def changeCoordinates (g : SL) : (Multiplicative W) ≃* (Multiplicative W) :=
  (Matrix.SpecialLinearGroup.toLin' g).toAddEquiv.toMultiplicative

private theorem changeCoordinates_apply (g : SL) (v : (Multiplicative W)) :
    (changeCoordinates g v).toAdd = g.val.mulVec v.toAdd := rfl

private theorem inv_mulVec (g : SL) (v : W) :
    (g⁻¹).val.mulVec (g.val.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

private theorem conj_mulVec (g h : SL) (v : W) :
    (g⁻¹).val.mulVec ((MulAut.conj g h).val.mulVec v) =
      h.val.mulVec ((g⁻¹).val.mulVec v) := by
  have he : g⁻¹ * MulAut.conj g h = h * g⁻¹ := by
    change g⁻¹ * (g * h * g⁻¹) = h * g⁻¹
    group
  have hh := congrArg (fun a : SL => a.val.mulVec v) he
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec] using hh

private theorem inverseTranspose_action (g : SL) (v : W) :
    (inverseTranspose g).val.mulVec v = dual g v := by
  have hm (x y : SL) : Matrix.SpecialLinearGroup.transpose (x * y) =
      Matrix.SpecialLinearGroup.transpose y * Matrix.SpecialLinearGroup.transpose x := by
    apply Subtype.ext
    exact Matrix.transpose_mul _ _
  have ho : Matrix.SpecialLinearGroup.transpose (1 : SL) = 1 :=
    Subtype.ext Matrix.transpose_one
  have he : Matrix.SpecialLinearGroup.transpose (g⁻¹) =
      (Matrix.SpecialLinearGroup.transpose g)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← hm, mul_inv_cancel, ho]
  change ((Matrix.SpecialLinearGroup.transpose g)⁻¹).val.mulVec v = _
  rw [← he]
  rfl

/-- Full moving generation removes the fixed summand supplied by small
involution recognition. The resulting marking is not yet the source marking. -/
theorem small_full_coordinates {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (ρ : SL →* MulAut E)
    (hfaith : Function.Injective ρ) (hsmall : HasSmallInvolution ρ)
    (hfull : commutatorAction ρ.range E = ⊤) :
    ∃ (e : E ≃* (Multiplicative W)) (σ : SL ≃* SL),
      ∀ (g : SL) (x : E), (e (ρ g x)).toAdd = (σ g).val.mulVec (e x).toAdd := by
  obtain ⟨s⟩ := naturalActionSplitting_of_small_involution ρ hfaith hsmall
  let j : E ≃* commutatorAction ρ.range E :=
    topEquiv.symm.trans (MulEquiv.subgroupCongr hfull.symm)
  refine ⟨j.trans s.coordinates, s.marking, ?_⟩
  intro g x
  exact s.action g (j x) (j (ρ g x)) rfl

/-- An elementary eight-group with a faithful action has either orientation
relative to the SAME prescribed marking; both inner changes are absorbed in
its coordinate map. -/
theorem natural_or_dual_of_coordinates {E : Type*} [Group E]
    (ρ : SL →* MulAut E) (κ : SL ≃* SL) (e : E ≃* (Multiplicative W)) (σ : SL ≃* SL)
    (ha : ∀ g x, (e (ρ g x)).toAdd = (σ g).val.mulVec (e x).toAdd) :
    (∃ f : E ≃* (Multiplicative W), ∀ g x, (f (ρ g x)).toAdd =
      (κ g).val.mulVec (f x).toAdd) ∨
    (∃ f : E ≃* (Multiplicative W), ∀ g x, (f (ρ g x)).toAdd =
      dual (κ g) (f x).toAdd) := by
  obtain ⟨k, hk | hk⟩ := inner_or_graph (κ.symm.trans σ)
  · left
    refine ⟨e.trans (changeCoordinates k⁻¹), ?_⟩
    intro g x
    have hg : σ g = MulAut.conj k (κ g) := by
      simpa using MulEquiv.congr_fun hk (κ g)
    change (changeCoordinates k⁻¹ (e (ρ g x))).toAdd = _
    rw [changeCoordinates_apply, ha, hg, conj_mulVec]
    rfl
  · right
    let j : SL := k * Matrix.PSL3Two.Bruhat.perm 5
    have hg (g : SL) : σ g = MulAut.conj j (inverseTranspose (κ g)) := by
      have hh := MulEquiv.congr_fun hk (κ g)
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulAut.mul_apply, Matrix.PSL3Two.MarkedAutomorphisms.diagram, MulAut.conj_apply] at hh
      rw [hh]
      change k * ((Matrix.PSL3Two.Bruhat.perm 5) * inverseTranspose (κ g) *
        (Matrix.PSL3Two.Bruhat.perm 5)⁻¹) * k⁻¹ =
          (k * Matrix.PSL3Two.Bruhat.perm 5) * inverseTranspose (κ g) *
            (k * Matrix.PSL3Two.Bruhat.perm 5)⁻¹
      group
    refine ⟨e.trans (changeCoordinates j⁻¹), ?_⟩
    intro g x
    change (changeCoordinates j⁻¹ (e (ρ g x))).toAdd = _
    rw [changeCoordinates_apply, ha, hg, conj_mulVec, inverseTranspose_action]
    rfl

/-- The small-displacement theorem with its two fixed-marking alternatives.
The natural alternative must be excluded by the actual source geometry. -/
theorem natural_or_dual_of_small_full {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (ρ : SL →* MulAut E) (κ : SL ≃* SL)
    (hfaith : Function.Injective ρ) (hsmall : HasSmallInvolution ρ)
    (hfull : commutatorAction ρ.range E = ⊤) :
    (∃ f : E ≃* (Multiplicative W), ∀ g x, (f (ρ g x)).toAdd =
      (κ g).val.mulVec (f x).toAdd) ∨
    (∃ f : E ≃* (Multiplicative W), ∀ g x, (f (ρ g x)).toAdd =
      dual (κ g) (f x).toAdd) := by
  obtain ⟨e, σ, ha⟩ := small_full_coordinates ρ hfaith hsmall hfull
  exact natural_or_dual_of_coordinates ρ κ e σ ha

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition
open DistanceFour.Linear Escape.Initial.Natural.Splitting

/-- The column action under the prescribed marking. -/
@[expose] noncomputable def naturalAction (κ : SL ≃* SL) :
    SL →* MulAut (Multiplicative W) where
  toFun g := (Matrix.SpecialLinearGroup.toLin' (κ g)).toAddEquiv.toMultiplicative
  map_one' := by
    ext v : 1
    change (Matrix.SpecialLinearGroup.toLin' (κ 1)) v.toAdd = v.toAdd
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    ext v : 1
    change (Matrix.SpecialLinearGroup.toLin' (κ (g * h))) v.toAdd =
      (Matrix.SpecialLinearGroup.toLin' (κ g))
        ((Matrix.SpecialLinearGroup.toLin' (κ h)) v.toAdd)
    rw [map_mul, map_mul]
    rfl

theorem naturalAction_apply (κ : SL ≃* SL) (g : SL) (x : Multiplicative W) :
    (naturalAction κ g x).toAdd = (κ g).val.mulVec x.toAdd := rfl

/-- An actual subgroup distinguishes the two action orientations by its
movement. At the source application it is the image of hat W_(a+4), with
movement at most two on the quotient and greater than two on U_a. -/
@[expose] def DisplacementSeparation {E : Type*} [Group E] (ρ : SL →* MulAut E)
    (κ : SL ≃* SL) : Prop :=
  ∃ P : Subgroup SL,
    Nat.card (commutatorAction (P.map ρ) E) ≠
      Nat.card (commutatorAction (P.map (naturalAction κ)) (Multiplicative W))

private theorem displacement_map {E F : Type*} [Group E] [Group F]
    (ρ : SL →* MulAut E) (τ : SL →* MulAut F)
    (e : E ≃* F) (he : ∀ g x, e (ρ g x) = τ g (e x)) (P : Subgroup SL) :
    (commutatorAction (P.map ρ) E).map e.toMonoidHom =
      commutatorAction (P.map τ) F := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure, MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨⟨a, g, hg, rfl⟩, x, rfl⟩, rfl⟩
    refine ⟨⟨τ g, mem_map_of_mem τ hg⟩, e x, ?_⟩
    change e (x⁻¹ * ρ g x) = (e x)⁻¹ * τ g (e x)
    rw [map_mul, map_inv, he]
  · rintro ⟨⟨a, g, hg, rfl⟩, x, rfl⟩
    refine ⟨(e.symm x)⁻¹ * ρ g (e.symm x),
      ⟨⟨ρ g, mem_map_of_mem ρ hg⟩, e.symm x, rfl⟩, ?_⟩
    change e ((e.symm x)⁻¹ * ρ g (e.symm x)) = x⁻¹ * τ g x
    rw [map_mul, map_inv, he, e.apply_symm_apply]

/-- Cardinal comparison excludes the natural coordinates without changing
or choosing the source marking. -/
theorem not_natural_of_displacement {E : Type*} [Group E]
    (ρ : SL →* MulAut E) (κ : SL ≃* SL) (hsep : DisplacementSeparation ρ κ) :
    ¬ ∃ f : E ≃* Multiplicative W, ∀ g x,
      (f (ρ g x)).toAdd = (κ g).val.mulVec (f x).toAdd := by
  rintro ⟨f, hf⟩
  obtain ⟨P, hP⟩ := hsep
  have he : ∀ g x, f (ρ g x) = naturalAction κ g (f x) := by
    intro g x
    exact Multiplicative.toAdd.injective (hf g x)
  have hm := displacement_map ρ (naturalAction κ) f he P
  apply hP
  rw [← hm]
  exact Nat.card_congr ((commutatorAction (P.map ρ) E).equivMapOfInjective
    f.toMonoidHom f.injective).toEquiv

/-- Faithfulness, full moving generation and a small involution give the
three-dimensional model. The actual actor comparison fixes its dual orientation. -/
theorem dual_coordinates_of_dynamics {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (ρ : SL →* MulAut E) (κ : SL ≃* SL)
    (hfaith : Function.Injective ρ) (hsmall : HasSmallInvolution ρ)
    (hfull : commutatorAction ρ.range E = ⊤) (hsep : DisplacementSeparation ρ κ) :
    ∃ f : E ≃* Multiplicative W, ∀ g x,
      (f (ρ g x)).toAdd = dual (κ g) (f x).toAdd :=
  (natural_or_dual_of_small_full ρ κ hfaith hsmall hfull).resolve_left
    (not_natural_of_displacement ρ κ hsep)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition

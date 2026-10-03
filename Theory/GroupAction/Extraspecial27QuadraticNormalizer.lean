module
public import Theory.GroupAction.Extraspecial27ElementaryActor
public import Theory.GroupAction.Extraspecial27FixedLayer
public import Theory.GroupAction.QuadraticFourCentralizerReduction
public import Theory.GroupAction.SubgroupConjugation

/-!
# Small quadratic normalizers of the extraspecial order27 module

Let F be an extraspecial subgroup of order27 in the automorphism group
of a finite elementary two-group W, acting fully. Suppose a quadratic
normalizing actor A contains an involution x with [F,x]=F, displacement
of order4, and centralization of Z(F). Then A has order at most two.

Quadraticity makes A elementary and fixes the x-displacement pointwise.
The existing extraspecial center-action theorem makes Z(F) faithful on
that displacement, so the normalizing action of A fixes Z(F). Its action
on F is injective: an actor centralizing F already centralizes x and fixes
its displacement, and the existing commutator-generation rigidity theorem
makes that actor trivial. The elementary center-preserving actor bound
on F now proves the result.

This is the terminal module bound in Stellmacher (9.1), Journal of Algebra
190 (1997), p.48. Applied to Q0Z_a, it identifies its terminal action image
with the cyclic image of the distinguished initial-center involution.
-/
public theorem extraspecial27_quadratic_normalizer_card_le_two
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (F A : Subgroup (MulAut W)) (hF : IsExtraspecial 3 F) (hFcard : Nat.card F = 27)
    (hnorm : A ≤ Subgroup.normalizer (F : Set (MulAut W)))
    (hquad : commutatorAction₂ A W = ⊥)
    (x : A) (hx : IsInvolution (x : MulAut W))
    (hfull : commutatorAction F W = ⊤)
    (hgen : ⁅F,Subgroup.zpowers (x : MulAut W)⁆ = F)
    (hcenter : ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers (x : MulAut W)⁆ = ⊥)
    (hdisp : Nat.card (commutatorAction (Subgroup.zpowers (x : MulAut W)) W) = 4) :
    Nat.card A ≤ 2 := by
  let _ := hF
  let _ : IsElementaryAbelian 2 A := QuadraticFourCentralizer.elementaryAbelian_of_quadratic A hquad
  let R := Subgroup.zpowers (x : MulAut W)
  let Z := (Subgroup.center F).map F.subtype
  let displacement := commutatorAction R W
  have hRA : R ≤ A := Subgroup.zpowers_le.mpr x.property
  have hdisple : displacement ≤ commutatorAction A W := by
    change commutatorAction R W ≤ commutatorAction A W
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨r, point, rfl⟩
    exact ⟨⟨r,hRA r.property⟩,point,rfl⟩
  have hfix (a : A) (point : W) (hpoint : point ∈ displacement) : (a : MulAut W) point = point :=
    (commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hquad (hdisple hpoint)) a
  have hZR : Z ≤ Subgroup.normalizer (R : Set (MulAut W)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcenter).trans (Subgroup.centralizer_le_normalizer _)
  have hZinv : IsInvariant Z W displacement :=
    commutatorAction_isInvariant_of_normalizing_actor Z R hZR
  obtain ⟨_,hZfaith⟩ := extraspecial27_center_action F hF hFcard x hx (hnorm x.property)
    hfull hgen hcenter hdisp
  have hcentral := Extraspecial27FixedLayer.centralizes_center_of_fixes_faithful_layer
    F A displacement hZinv hnorm hfix hZfaith
  let _ : MulDistribMulAction A F := Subgroup.conjMulDistribMulActionOfLeNormalizer A F hnorm
  let action : A →* MulAut F := MulDistribMulAction.toMulAut A F
  have hinj : Function.Injective action := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    have hCF : (a : MulAut W) ∈ Subgroup.centralizer (F : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have hh := congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp ha) (⟨f,hf⟩ : F))
      change (a : MulAut W) * f * (a : MulAut W)⁻¹ = f at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hCR : (a : MulAut W) ∈ Subgroup.centralizer (R : Set (MulAut W)) := by
      intro r hr
      exact setLike_mul_comm (s := A) (hRA hr) a.property
    apply Subtype.ext
    exact QuadraticFourCentralizer.centralizer_eq_one_of_fixes_displacement F R a
      hCF hCR hgen hfull (hfix a)
  apply MulAut.elementary_two_center_preserving_card_le_two hFcard action hinj
  intro a z hz
  apply Subtype.ext
  change (a : MulAut W) * (z : MulAut W) * (a : MulAut W)⁻¹ = z
  have hc := hcentral a (⟨z,Subgroup.mem_map_of_mem F.subtype hz⟩ : Z)
  rw [hc.eq, mul_inv_cancel_right]

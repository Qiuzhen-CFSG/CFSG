module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.Coordinates
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.IntrinsicCoordinates.Frames

/-!
# The original involution frames give binary normal forms

Collecting the four supplied generators and the actual center gives a
homomorphism from the 64-word group. The two original factors generate the
ambient group, so the map is surjective; equality of orders makes it an
isomorphism. The same generation identities preserve the exact two factors.
Source: Aschbacher, *Sporadic Groups* (1994), proof of 45.3, pp.242–243.
-/

public section
noncomputable section
open Subgroup
namespace Theory.GroupTheory.HyperbolicRecognition
open Intrinsic
variable {K : Type*} [Group K] [Finite K] (F : HyperbolicFactors K)
    (P : HyperbolicFrame F.A F.z) (Q : HyperbolicFrame F.B F.u)

private def evaluation : Word (crossMatrix F P.a P.b Q.a Q.b) →* K :=
  wordHom (centerEquiv F).toMonoidHom (factorCollectionRelations F P Q)

private theorem evaluation_central (r : Central) :
    evaluation F P Q (centralWord _ r) = centralEval (centerEquiv F).toMonoidHom r := by
  simp [evaluation, wordHom, wordEval, vectorWord, pairWord, centralWord]

private theorem evaluation_surjective : Function.Surjective (evaluation F P Q) := by
  let f := evaluation F P Q
  let M := crossMatrix F P.a P.b Q.a Q.b
  have hz : center K ≤ f.range := by
    intro x hx
    obtain ⟨s, hs⟩ := (centerEquiv F).surjective ⟨x,hx⟩
    refine ⟨centralWord M s.toAdd, ?_⟩
    exact (evaluation_central F P Q s.toAdd).trans (congrArg Subtype.val hs)
  have ha : P.a ∈ f.range := by
    refine ⟨lift M va, ?_⟩
    simp [f, evaluation, wordHom, wordEval, vectorWord, pairWord, lift, va]
  have hb : P.b ∈ f.range := by
    refine ⟨lift M vb, ?_⟩
    simp [f, evaluation, wordHom, wordEval, vectorWord, pairWord, lift, vb]
  have hc : Q.a ∈ f.range := by
    refine ⟨lift M vc, ?_⟩
    simp [f, evaluation, wordHom, wordEval, vectorWord, pairWord, lift, vc]
  have hd : Q.b ∈ f.range := by
    refine ⟨lift M vd, ?_⟩
    simp [f, evaluation, wordHom, wordEval, vectorWord, pairWord, lift, vd]
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← F.sup_eq]
  exact sup_le (P.generate f.range hz ha hb) (Q.generate f.range hz hc hd)

/-- The actual hyperbolic frames determine multiplicative normal forms,
without any recognition or reflection premise. -/
theorem nonempty_markedCoordinates : Nonempty (MarkedCoordinates F P Q) := by
  let M := crossMatrix F P.a P.b Q.a Q.b
  let f := evaluation F P Q
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_surjective_and_card f).mpr
      ⟨evaluation_surjective F P Q, (card_Word M).trans F.card.symm⟩
  let e : Word M ≃* K := MulEquiv.ofBijective f hbij
  have hec (r : Central) :
      e.symm (centralEval (centerEquiv F).toMonoidHom r) = centralWord M r := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (evaluation_central F P Q r).symm
  have hcenter (x : K) (hx : x ∈ center K) : (e.symm x).vector = 0 := by
    obtain ⟨s, hs⟩ := (centerEquiv F).surjective ⟨x,hx⟩
    have hh : centralEval (centerEquiv F).toMonoidHom s.toAdd = x := congrArg Subtype.val hs
    rw [← hh, hec]
    rfl
  have hea : e.symm P.a = lift M va := by
    apply e.injective
    rw [e.apply_symm_apply]
    simp [e, f, evaluation, wordHom, wordEval, vectorWord, pairWord, lift, va]
  have heb : e.symm P.b = lift M vb := by
    apply e.injective
    rw [e.apply_symm_apply]
    simp [e, f, evaluation, wordHom, wordEval, vectorWord, pairWord, lift, vb]
  have hec' : e.symm Q.a = lift M vc := by
    apply e.injective
    rw [e.apply_symm_apply]
    simp [e, f, evaluation, wordHom, wordEval, vectorWord, pairWord, lift, vc]
  have hed : e.symm Q.b = lift M vd := by
    apply e.injective
    rw [e.apply_symm_apply]
    simp [e, f, evaluation, wordHom, wordEval, vectorWord, pairWord, lift, vd]
  refine ⟨⟨M, e.symm, ?_, ?_, hea, heb, hec', hed, ?_, ?_⟩⟩
  · have hh := hec cz
    rwa [show centralEval (centerEquiv F).toMonoidHom cz = (F.z : K) from
      congrArg Subtype.val (centerEquiv_z F)] at hh
  · have hh := hec cu
    rwa [show centralEval (centerEquiv F).toMonoidHom cu = (F.u : K) from
      congrArg Subtype.val (centerEquiv_u F)] at hh
  · intro x
    constructor
    · intro hx
      apply P.generate ((firstPlane M).comap e.symm.toMonoidHom) _ _ _ hx
      · intro y hy
        change (e.symm y).vector.2 = 0
        rw [hcenter y hy]
        rfl
      · change (e.symm P.a).vector.2 = 0
        rw [hea]
        rfl
      · change (e.symm P.b).vector.2 = 0
        rw [heb]
        rfl
    · intro hx
      have hz : center K ≤ F.A := F.inf_eq ▸ inf_le_left
      rw [← e.apply_symm_apply x]
      change (pairWord P.a P.b (e.symm x).vector.1 *
        pairWord Q.a Q.b (e.symm x).vector.2) *
        centralEval (centerEquiv F).toMonoidHom (e.symm x).central ∈ F.A
      rw [hx]
      simp only [pairWord, Prod.fst_zero, Prod.snd_zero, bitPower_zero, mul_one]
      exact F.A.mul_mem (F.A.mul_mem (F.A.pow_mem P.a_mem _) (F.A.pow_mem P.b_mem _))
        (hz ((centerEquiv F) (Multiplicative.ofAdd (e.symm x).central)).property)
  · intro x
    constructor
    · intro hx
      apply Q.generate ((secondPlane M).comap e.symm.toMonoidHom) _ _ _ hx
      · intro y hy
        change (e.symm y).vector.1 = 0
        rw [hcenter y hy]
        rfl
      · change (e.symm Q.a).vector.1 = 0
        rw [hec']
        rfl
      · change (e.symm Q.b).vector.1 = 0
        rw [hed]
        rfl
    · intro hx
      have hz : center K ≤ F.B := F.inf_eq ▸ inf_le_right
      rw [← e.apply_symm_apply x]
      change (pairWord P.a P.b (e.symm x).vector.1 *
        pairWord Q.a Q.b (e.symm x).vector.2) *
        centralEval (centerEquiv F).toMonoidHom (e.symm x).central ∈ F.B
      rw [hx]
      simp only [pairWord, Prod.fst_zero, Prod.snd_zero, bitPower_zero, one_mul]
      exact F.B.mul_mem (F.B.mul_mem (F.B.pow_mem Q.a_mem _) (F.B.pow_mem Q.b_mem _))
        (hz ((centerEquiv F) (Multiplicative.ofAdd (e.symm x).central)).property)

end Theory.GroupTheory.HyperbolicRecognition

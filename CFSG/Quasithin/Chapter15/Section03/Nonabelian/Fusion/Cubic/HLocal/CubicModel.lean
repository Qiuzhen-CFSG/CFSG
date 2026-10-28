module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.FixedPoints
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.Involution
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.CubicModel.Counts

/-!
# Intrinsic cubic counts for the recognized H-local model

The image of a source Sylow three-group still has order three modulo O₂(H).
The outer automorphism quotient has order two, so this image is inner.
Pulling it back through the faithful conjugation map gives a genuine cubic
subgroup of SL₃(2). The recognition equation identifies its natural-plus-dual
fixed space with the fixed subgroup of the literal action on U/Z.
The intrinsic model counts then give four fixed quotient points and an actor
centralizer of order six, without any additional counting assumptions.

Source: Aschbacher–Smith, the H-centralizer calculation preceding 15.3.60,
combined manuscript (1 March 2004), printed pp.1148–1150.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal
variable {G : Type*} [Group G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- Passing to the actual two-core quotient preserves the order-three Sylow group. -/
lemma cubic_actor_image_card [Finite G] (d : Recognition Z ZS)
    (P : Sylow 3 (centralizerH Z)) :
    Nat.card ((P : Subgroup (centralizerH Z)).map
      (QuotientGroup.mk' (pCore 2 (centralizerH Z)))) = 3 := by
  change Nat.card (P.mapSurjective (QuotientGroup.mk'_surjective _)) = 3
  rw [Sylow.card_eq_multiplicity, actor_card Z ZS d]
  decide +kernel

/-- The image of the source cubic in the recognized automorphism group. -/
noncomputable def cubicActor (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z)) :
    Subgroup (MulAut Matrix.PSL3Two.SL) :=
  ((P : Subgroup (centralizerH Z)).map (QuotientGroup.mk' (pCore 2 (centralizerH Z)))).map
    (linearActor Z ZS d).toMonoidHom

/-- The recognized actor image is a cubic subgroup. -/
lemma cubicActor_card [Finite G] (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z)) :
    Nat.card (cubicActor Z ZS d P) = 3 := by
  rw [cubicActor, card_map_of_injective (linearActor Z ZS d).injective,
    cubic_actor_image_card Z ZS d P]

/-- The cubic actor lies in the actual inner automorphism subgroup. -/
lemma cubicActor_le_inner [Finite G] (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z)) :
    cubicActor Z ZS d P ≤ MulAut.innerSubgroup Matrix.PSL3Two.SL := by
  intro a ha
  have h3 : a ^ 3 = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨a,ha⟩ : cubicActor Z ZS d P)))
    change a ^ Nat.card (cubicActor Z ZS d P) = 1 at h
    rwa [cubicActor_card Z ZS d P] at h
  let q := QuotientGroup.mk' (MulAut.innerSubgroup Matrix.PSL3Two.SL)
  have hq2 : q a ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := q a)
    rwa [Matrix.PSL3Two.Automorphisms.card_outer_sl] at h
  have hq3 : q a ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  apply (QuotientGroup.eq_one_iff a).mp
  change q a = 1
  calc
    q a = q a ^ 3 * (q a ^ 2)⁻¹ := by group
    _ = 1 := by rw [hq3,hq2]; simp

/-- The matrix subgroup implementing the inner action of the source cubic. -/
noncomputable def cubicLinear (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z)) :
    Subgroup Matrix.PSL3Two.SL :=
  (cubicActor Z ZS d P).comap MulAut.conj

/-- Conjugation identifies the implementing subgroup with the whole cubic actor. -/
lemma cubicLinear_image [Finite G] (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z)) :
    (cubicLinear Z ZS d P).map MulAut.conj = cubicActor Z ZS d P :=
  map_comap_eq_self (cubicActor_le_inner Z ZS d P)

/-- The implementing matrix subgroup has order three. -/
lemma cubicLinear_card [Finite G] (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z)) :
    Nat.card (cubicLinear Z ZS d P) = 3 := by
  rw [← card_map_of_injective (K := cubicLinear Z ZS d P)
    (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot),
    cubicLinear_image, cubicActor_card]

private lemma inner_action_linear (d : Recognition Z ZS) (h : centralizerH Z)
    (g : Matrix.PSL3Two.SL)
    (he : linearActor Z ZS d (QuotientGroup.mk' (pCore 2 (centralizerH Z)) h) = MulAut.conj g)
    (u : VectorQuotient Z ZS) :
    (d.coordinates (quotientAction Z ZS h u)).toAdd =
      (BinaryLinearThree.W g (d.coordinates u).toAdd.1,
       BinaryLinearThree.W.dual g (d.coordinates u).toAdd.2) := by
  apply d.inner_action h g
  apply (MulAut.congr Matrix.PSL3Two.equiv.symm).injective
  change linearActor Z ZS d _ = _
  rw [he, MulAut.congr_conj, MulEquiv.symm_apply_apply]

/-- Recognition intertwines fixed points of the literal quotient action with
the fixed space of the same implementing matrices on the natural-plus-dual module. -/
noncomputable def quotientFixedEquiv [Finite G] (d : Recognition Z ZS)
    (P : Sylow 3 (centralizerH Z)) :
    quotientFixed Z ZS P ≃ fixedSpace (BinaryLinearThree.W.prod BinaryLinearThree.W.dual)
      (cubicLinear Z ZS d P) where
  toFun u := ⟨(d.coordinates u.val).toAdd, by
    intro x
    obtain ⟨a,ha,he⟩ := x.property
    obtain ⟨p,hp,rfl⟩ := ha
    have hact := inner_action_linear Z ZS d p x.val he u.val
    rw [(quotientFixed_mem Z ZS P u.val).mp u.property ⟨p,hp⟩] at hact
    exact hact.symm⟩
  invFun v := ⟨d.coordinates.symm (Multiplicative.ofAdd v.val), by
    apply (quotientFixed_mem Z ZS P _).mpr
    intro p
    let a := linearActor Z ZS d (QuotientGroup.mk' (pCore 2 (centralizerH Z)) (p : centralizerH Z))
    have ha : a ∈ cubicActor Z ZS d P :=
      mem_map_of_mem _ (mem_map_of_mem _ p.property)
    obtain ⟨g,hg⟩ := cubicActor_le_inner Z ZS d P ha
    have hgX : g ∈ cubicLinear Z ZS d P := by
      change MulAut.conj g ∈ cubicActor Z ZS d P
      rwa [hg]
    have hact := inner_action_linear Z ZS d (p : centralizerH Z) g hg.symm
      (d.coordinates.symm (Multiplicative.ofAdd v.val))
    have hv := v.property ⟨g,hgX⟩
    apply d.coordinates.injective
    apply Multiplicative.toAdd.injective
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at hact ⊢
    exact hact.trans hv⟩
  left_inv u := by apply Subtype.ext; exact d.coordinates.symm_apply_apply u.val
  right_inv v := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (d.coordinates.apply_symm_apply _)

/-- The source cubic fixes exactly four points of the literal quotient U/Z. -/
lemma quotientFixed_card [Finite G] (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z)) :
    Nat.card (quotientFixed Z ZS P) = 4 := by
  rw [Nat.card_congr (quotientFixedEquiv Z ZS d P)]
  exact CubicModel.paired_fixed_card _ (cubicLinear_card Z ZS d P)

/-- Its centralizer in the actual actor quotient has order six. -/
lemma cubic_actor_centralizer_card [Finite G] (d : Recognition Z ZS)
    (P : Sylow 3 (centralizerH Z)) :
    Nat.card (centralizer (((P : Subgroup (centralizerH Z)).map
      (QuotientGroup.mk' (pCore 2 (centralizerH Z)))) : Set (ActorQuotient Z))) = 6 := by
  rw [← card_map_of_injective (f := (linearActor Z ZS d).toMonoidHom)
    (linearActor Z ZS d).injective, CubicModel.map_centralizer_equiv]
  exact CubicModel.aut_centralizer_card _ (cubicActor_card Z ZS d P)
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal

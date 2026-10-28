module
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.SymmetricThreeSquare
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.FactorCoordinates
public import Theory.GroupTheory.PResidual.Restriction
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.QuaternionCentralProductTransport.Factors
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# Residual factors under the full binary orthogonal square action

The factor-preserving subgroup has index two and quotient S3 × S3.
Its two-core is the original quaternion central product. Recognition in that
subgroup produces two commuting SL2(3) factors. Since it contains the ambient
two-residual, their join is the actual ambient residual, with the original
quaternion embeddings retained.

Source: Aschbacher--Smith, 2.4.29, printed p.546. This removes the residual-factor
premise in the original single alternating-five transfer argument.
-/
@[expose] public section
open Subgroup
namespace BinaryFourPlus
noncomputable def baseEquiv :
    (RegularWreathProduct.rightHom : Wreath →* C2).ker ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) where
  toFun w := (w.val.left 1, w.val.left swapIndex)
  invFun p := ⟨⟨fun i => if i = 1 then p.1 else p.2, 1⟩, rfl⟩
  left_inv w := by
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · funext i
      have hi : i = 1 ∨ i = swapIndex := by decide +revert
      rcases hi with rfl | rfl <;> simp [swapIndex]
    · exact w.property.symm
  right_inv p := by simp [swapIndex]
  map_mul' a b := by
    have ha : a.val.right = 1 := a.property
    simp [RegularWreathProduct.mul_left, ha]
end BinaryFourPlus
namespace Subgroup.QuaternionCentralProductData
variable {G : Type*} [Group G] [Finite G]
variable (f : G →* BinaryFourPlus.Wreath)

noncomputable def squarePreimage : Subgroup G :=
  ((RegularWreathProduct.rightHom : BinaryFourPlus.Wreath →* BinaryFourPlus.C2).comp f).ker

noncomputable def squareHom : squarePreimage f →*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  BinaryFourPlus.baseEquiv.toMonoidHom.comp
    { toFun := fun g => ⟨f g, g.property⟩
      map_one' := Subtype.ext f.map_one
      map_mul' := fun a b => Subtype.ext (f.map_mul a b) }

omit [Finite G] in
theorem squareHom_surjective (hf : Function.Surjective f) :
    Function.Surjective (squareHom f) := by
  intro p
  obtain ⟨g,hg⟩ := hf (BinaryFourPlus.baseEquiv.symm p).val
  have hn : g ∈ squarePreimage f := by
    change (f g).right = 1
    rw [hg]
    exact (BinaryFourPlus.baseEquiv.symm p).property
  refine ⟨⟨g,hn⟩,?_⟩
  change BinaryFourPlus.baseEquiv ⟨f g,hn⟩ = p
  rw [show (⟨f g,hn⟩ : (RegularWreathProduct.rightHom : BinaryFourPlus.Wreath →* BinaryFourPlus.C2).ker) = BinaryFourPlus.baseEquiv.symm p from Subtype.ext hg]
  exact BinaryFourPlus.baseEquiv.apply_symm_apply p

omit [Finite G] in
theorem squareHom_ker (Q : Subgroup G) (hk : f.ker = Q) :
    (squareHom f).ker = Q.subgroupOf (squarePreimage f) := by
  ext g
  change BinaryFourPlus.baseEquiv ⟨f g,g.property⟩ = 1 ↔ (g:G) ∈ Q
  rw [← BinaryFourPlus.baseEquiv.map_one, BinaryFourPlus.baseEquiv.injective.eq_iff]
  rw [Subtype.ext_iff]
  change f g = 1 ↔ (g:G) ∈ Q
  change (g:G) ∈ f.ker ↔ (g:G) ∈ Q
  rw [hk]

variable (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)

omit [Finite G] in
theorem square_preimage_core (hcore : Q = pCore 2 G) (hk : f.ker = Q) :
    Q.subgroupOf (squarePreimage f) = pCore 2 (squarePreimage f) := by
  let N := squarePreimage f
  let : N.Normal := by dsimp [N,squarePreimage]; infer_instance
  have hQN : Q ≤ N := by
    intro q hq
    change (f q).right = 1
    have hqf : f q = 1 := by
      change q ∈ f.ker
      rw [hk]
      exact hq
    rw [hqf]
    rfl
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, (hcore ▸ pCore_isPGroup).comap_subtype⟩
  · let : N.Normal := by dsimp [N,squarePreimage]; infer_instance
    have hnorm : normalizer (N : Set G) ≤ normalizer ((pCore 2 N).map N.subtype : Set G) :=
      normalizer_le_normalizer_characteristic_image N (pCore 2 N)
    rw [N.normalizer_eq_top] at hnorm
    have hmnormal : ((pCore 2 N).map N.subtype).Normal :=
      normalizer_eq_top_iff.mp (top_le_iff.mp hnorm)
    have hle : (pCore 2 N).map N.subtype ≤ Q := by
      rw [hcore]
      exact le_sSup ⟨hmnormal,pCore_isPGroup.map _⟩
    intro x hx
    exact hle (mem_map_of_mem N.subtype hx)

theorem quaternion_residual_central_product_of_wreath
    (hcore : Q = pCore 2 G) (hcent : centralizer (Q : Set G) ≤ Q)
    (hf : Function.Surjective f) (hk : f.ker = Q) :
    Nonempty (QuaternionResidualCentralProduct Q d) := by
  let N := squarePreimage f
  let : N.Normal := by dsimp [N,squarePreimage]; infer_instance
  have hQN : Q ≤ N := by
    intro q hq
    change (f q).right = 1
    have hqf : f q = 1 := by
      change q ∈ f.ker
      rw [hk]
      exact hq
    rw [hqf]
    rfl
  let QN := Q.subgroupOf N
  let eQ : QN ≃* Q := subgroupOfEquivOfLe hQN
  let dn := d.map eQ.symm
  have hQcore : QN = pCore 2 N := square_preimage_core f Q hcore hk
  have hQcent : centralizer (QN : Set N) ≤ QN := by
    intro n hn
    apply hcent
    intro q hq
    exact congrArg Subtype.val (hn ⟨q,hQN hq⟩ hq)
  let g : N →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := squareHom f
  have hgs : Function.Surjective g := squareHom_surjective f hf
  have hgk : g.ker = QN := squareHom_ker f Q hk
  let eq : (N ⧸ QN) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
    (QuotientGroup.quotientMulEquivOfEq hgk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hgs)
  obtain ⟨r⟩ := quaternion_residual_central_product_of_symmetricThree_square QN dn hQcore hQcent eq
  have hRN : pResidual 2 G ≤ N :=
    pResidual_le_ker_of_isPGroup 2 _ (IsPGroup.of_card (n:=1) (by rw [Nat.card_eq_fintype_card]; decide))
  have hres : (pResidual 2 N).map N.subtype = pResidual 2 G := by
    have htop : (pResidual 2 (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = pResidual 2 G :=
      map_pResidual 2 (topEquiv : (⊤ : Subgroup G) ≃* G)
    have hh := embedded_pResidual_eq_of_le_of_residual_le 2
      (Y:=(⊤:Subgroup G)) (show N≤⊤ from le_top)
      (by rwa [htop])
    simpa only [htop] using hh
  have hleft : (dn.left.map QN.subtype).map N.subtype = d.left.map Q.subtype := by
    rw [show dn.left = d.left.map eQ.symm.toMonoidHom from d.map_left eQ.symm]
    rw [map_map, map_map]
    rfl
  have hright : (dn.right.map QN.subtype).map N.subtype = d.right.map Q.subtype := by
    rw [show dn.right = d.right.map eQ.symm.toMonoidHom from d.map_right eQ.symm]
    rw [map_map, map_map]
    rfl
  refine ⟨{
    left := r.left.map N.subtype
    right := r.right.map N.subtype
    left_model := r.left_model.map fun e => (r.left.equivMapOfInjective N.subtype N.subtype_injective).symm.trans e
    right_model := r.right_model.map fun e => (r.right.equivMapOfInjective N.subtype N.subtype_injective).symm.trans e
    left_contains := hleft ▸ map_mono r.left_contains
    right_contains := hright ▸ map_mono r.right_contains
    left_core := ?_
    right_core := ?_
    commute := ?_
    intersection := ?_
    span := ?_ }⟩
  · have hh := map_pCoreIn_of_ker_isPGroup (p:=2) N.subtype
      (by rw [N.subtype.ker_eq_bot N.subtype_injective]; exact IsPGroup.of_bot) r.left
    change (r.left.pCoreIn 2).map N.subtype = (r.left.map N.subtype).pCoreIn 2 at hh
    change (r.left.map N.subtype).pCoreIn 2 = _
    rw [←hh]
    change ((pCore 2 r.left).map r.left.subtype).map N.subtype = _
    rw [r.left_core]
    exact hleft
  · have hh := map_pCoreIn_of_ker_isPGroup (p:=2) N.subtype
      (by rw [N.subtype.ker_eq_bot N.subtype_injective]; exact IsPGroup.of_bot) r.right
    change (r.right.pCoreIn 2).map N.subtype = (r.right.map N.subtype).pCoreIn 2 at hh
    change (r.right.map N.subtype).pCoreIn 2 = _
    rw [←hh]
    change ((pCore 2 r.right).map r.right.subtype).map N.subtype = _
    rw [r.right_core]
    exact hright
  · rintro l ⟨l,hl,rfl⟩ t ⟨t,ht,rfl⟩
    exact congrArg Subtype.val (r.commute l hl t ht)
  · rw [←map_inf _ _ N.subtype N.subtype_injective,r.intersection,map_map]
    have hc : (center QN).map eQ.toMonoidHom = center Q :=
      by
        ext q
        constructor
        · rintro ⟨a,ha,rfl⟩
          exact (Subgroup.centerCongr eQ ⟨a,ha⟩).property
        · intro hq
          exact ⟨eQ.symm q,(Subgroup.centerCongr eQ.symm ⟨q,hq⟩).property,eQ.apply_symm_apply q⟩
    have he : N.subtype.comp QN.subtype = Q.subtype.comp eQ.toMonoidHom := rfl
    rw [he,←map_map,hc]
  · rw [←map_sup,r.span]
    exact hres
end Subgroup.QuaternionCentralProductData

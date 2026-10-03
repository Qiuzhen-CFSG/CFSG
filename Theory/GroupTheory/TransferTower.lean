module

public import Mathlib.GroupTheory.Transfer

/-!
# Composition of ordinary transfer

`MonoidHom.transfer_transfer` composes the actual transfer homomorphisms along
`H ≤ K ≤ G`, for a finite group `G` and an arbitrary commutative target. The
inner transfer views `H` inside `K` through `Subgroup.subgroupOfEquivOfLe`.
This lets transfer vanishing for a maximal subgroup propagate to its subgroups.

The proof first expresses transfer as a product of the subgroup coordinates in
a left-transversal decomposition. It then combines decompositions of `G` over
`K` and of `K` over `H`: their representatives multiply, and the corresponding
double product is exactly the composite transfer.

This is ordinary transfer transitivity, as used in the proof of Proposition 2.3
of Andersen–Oliver–Ventura, *Fusion systems and amalgams*, author manuscript
p. 6. The transfer construction and transversal identities are from Mathlib.
-/

noncomputable section

open Subgroup

namespace MonoidHom

/-- The transfer product indexed by the chosen transversal itself. -/
private theorem transfer_eq_prod_transversal
    {G A : Type*} [Group G] [CommGroup A] [Finite G]
    {H : Subgroup G} (φ : H →* A) (T : H.LeftTransversal)
    [Fintype T.val] (g : G) :
    transfer φ g = ∏ t : T.val, φ ((T.property.equiv (g * t)).2) := by
  classical
  let := H.fintypeQuotientOfFiniteIndex
  have hf (x : G) : (T.property.equiv x).1 = T.property.toLeftFun x := by
    apply (isComplement_iff_existsUnique_inv_mul_mem.mp T.property x).unique
    · rw [T.property.equiv_fst_eq_mul_inv]
      simp
    · exact T.property.inv_toLeftFun_mul_mem x
  rw [transfer_def φ T g]
  unfold leftTransversals.diff
  apply Fintype.prod_equiv
    ((MulAction.toPerm g).symm.trans T.property.leftQuotientEquiv)
  intro q
  apply congrArg φ
  apply Subtype.ext
  rw [T.property.equiv_snd_eq_inv_mul, hf]
  simp only [Equiv.trans_apply, MulAction.toPerm_symm_apply,
    smul_apply_eq_smul_apply_inv_smul, smul_eq_mul]
  have hq : (QuotientGroup.mk
      (g * (T.property.leftQuotientEquiv (g⁻¹ • q) : G)) : G ⧸ H) = q := by
    change g • QuotientGroup.mk (T.property.leftQuotientEquiv (g⁻¹ • q) : G) = q
    exact (congrArg (g • ·)
      (T.property.leftQuotientEquiv.symm_apply_apply (g⁻¹ • q))).trans
      (smul_inv_smul g q)
  simp only [IsComplement.toLeftFun, Function.comp_apply, hq]

/-- Reindex the transversal product by an equivariant decomposition. -/
private theorem transfer_eq_prod_decomposition
    {G A I : Type*} [Group G] [CommGroup A] [Finite G] [Fintype I]
    {H : Subgroup G} (φ : H →* A) (e : G ≃ I × H)
    (he : ∀ i h, e.symm (i, h) = e.symm (i, 1) * h) (g : G) :
    transfer φ g = ∏ i, φ ((e (g * e.symm (i, 1))).2) := by
  classical
  let r : I → G := fun i => e.symm (i, 1)
  have hr : Function.Injective r := fun i j hij =>
    congrArg Prod.fst (e.symm.injective hij)
  let er : I ≃ Set.range r := Equiv.ofInjective r hr
  have hmul (x : Set.range r × H) :
      e.symm (er.symm x.1, x.2) = (x.1 : G) * x.2 := by
    rw [he]
    change r (er.symm x.1) * x.2 = _
    rw [show r (er.symm x.1) = (x.1 : G) from
      Equiv.apply_ofInjective_symm hr x.1]
  let T : H.LeftTransversal := ⟨Set.range r, by
    have hb := ((Equiv.prodCongr er.symm (Equiv.refl H)).trans e.symm).bijective
    change Function.Bijective (fun x : Set.range r × H => (x.1 : G) * x.2)
    convert hb using 1
    exact funext fun x => (hmul x).symm⟩
  let : Fintype T.val := Fintype.ofFinite _
  rw [transfer_eq_prod_transversal φ T]
  symm
  apply Fintype.prod_equiv er
  intro i
  apply congrArg φ
  have hd : e (g * r i) =
      (er.symm (T.property.equiv (g * r i)).1, (T.property.equiv (g * r i)).2) := by
    apply e.symm.injective
    rw [e.symm_apply_apply, hmul, T.property.equiv_fst_mul_equiv_snd]
  exact congrArg Prod.snd hd

/-- Ordinary transfer is transitive along a chain of subgroups. -/
public theorem transfer_transfer
    {G A : Type*} [Group G] [CommGroup A] [Finite G]
    (H K : Subgroup G) (hHK : H ≤ K) (φ : H →* A) :
    MonoidHom.transfer (H := K)
      (MonoidHom.transfer (H := H.subgroupOf K)
        (φ.comp (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom)) =
      MonoidHom.transfer φ := by
  classical
  let S : K.LeftTransversal := default
  let T : (H.subgroupOf K).LeftTransversal := default
  let := Fintype.ofFinite S.val
  let := Fintype.ofFinite T.val
  let a := Subgroup.subgroupOfEquivOfLe hHK
  let e : G ≃ (S.val × T.val) × H :=
    (S.property.equiv.trans
      (Equiv.prodCongr (Equiv.refl _) T.property.equiv)).trans
      ((Equiv.prodAssoc _ _ _).symm.trans
        (Equiv.prodCongr (Equiv.refl _) a.toEquiv))
  have he (i : S.val × T.val) (h : H) :
      e.symm (i, h) = e.symm (i, 1) * h := by
    change (i.1 : G) * (((i.2 : K) : G) * (h : G)) =
      ((i.1 : G) * (((i.2 : K) : G) * 1)) * (h : G)
    simp only [mul_one, mul_assoc]
  have hrep (i : S.val × T.val) :
      e.symm (i, 1) = (i.1 : G) * ((i.2 : K) : G) := by
    change (i.1 : G) * (((i.2 : K) : G) * 1) = _
    rw [mul_one]
  ext g
  rw [transfer_eq_prod_transversal _ S g,
    transfer_eq_prod_decomposition φ e he g, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro s _
  rw [transfer_eq_prod_transversal _ T]
  apply Finset.prod_congr rfl
  intro t _
  rw [hrep]
  change φ (a (T.property.equiv ((S.property.equiv (g * s)).2 * t)).2) =
    φ (a (T.property.equiv (S.property.equiv (g * ((s : G) * ((t : K) : G)))).2).2)
  rw [← mul_assoc, S.property.equiv_mul_right]

end MonoidHom

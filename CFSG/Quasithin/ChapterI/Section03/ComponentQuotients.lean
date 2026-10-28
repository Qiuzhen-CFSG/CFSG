module
public import Theory.GroupTheory.CComponent.TwoComponent.SwapQuotient
public import CFSG.Quasithin.ChapterI.Section03.Balance

/-!
# The two-component quotients in the transposed-pair branch of I.3.2

For distinct two-components J₁ and J₂, the quotient of their actual join
by O_{2',2} is the product of their intrinsic nonabelian simple quotients.
Both component inclusions are retained. An involution interchanging them
induces the factor swap, so the quotient centralizer is a full simple
diagonal. The final application uses conjugation by an actual ambient
involution, with its action on every element of the join recorded.

If the literal image of a local two-component remains a two-component
of this quotient centralizer, simplicity makes it the entire diagonal.
The original map then has kernel exactly the local component's intrinsic
O_{2',2}; this gives both the radical-intersection formula and the source
quotient equivalence. Component preservation is precisely the separate
GLS 5.22(iv) input discharged by the I.3 balance/assembly owner. No quotient
or diagonal equivalence, K-group recognition, B₂, or SQTK assumption is used
as an input to the structural argument. Odd-core solvability is discharged
by the existing odd order theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma I.3.2, printed pp.414–415 (PDF pp.425–426); GLS II, Chapter B,
Propositions 3.5, 4.7, 5.22(iv) and Lemma 4.8.
-/

public section
open Subgroup Theory.GroupTheory


namespace CFSG.Quasithin.ChapterI.ComponentQuotients

local instance oddCoreSolvable (A : Type*) [Group A] [Finite A] :
    Group.IsSolvable (pPrimeCore 2 A) :=
  odd_order_theorem _ (Nat.coprime_two_left.mp pPrimeCore_coprime_card)

variable {H : Type*} [Group H] [Finite H]

/-- The intrinsic source quotient of a two-component is nonabelian simple. -/
theorem twoComponent_quotient_simple {J : Subgroup H} (hJ : J.IsTwoComponent) :
    IsSimpleGroup (J ⧸ oddTwoCore J) ∧ ¬ IsMulCommutative (J ⧸ oddTwoCore J) :=
  ⟨hJ.isSimpleGroup_quotient_oddTwoCore, hJ.not_isMulCommutative_quotient_oddTwoCore⟩

/-- No odd-order-solvability premise remains in the finite source intersection formula. -/
theorem twoComponent_core_intersection {J : Subgroup H} (hJ : J.IsTwoComponent) :
    oddTwoCore J = (solvableRadical H).subgroupOf J :=
  hJ.oddTwoCore_eq_radical_intersection

omit [Finite H] in
private theorem join_factors_generate (J₁ J₂ : Subgroup H) :
    J₁.subgroupOf (J₁ ⊔ J₂) ⊔ J₂.subgroupOf (J₁ ⊔ J₂) = ⊤ := by
  apply map_injective (J₁ ⊔ J₂).subtype_injective
  simp only [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
    map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]

/-- The source core and radical agree in the actual join of the components. -/
theorem pair_core_eq_radical {J₁ J₂ : Subgroup H}
    (h₁ : J₁.IsTwoComponent) (h₂ : J₂.IsTwoComponent) :
    oddTwoCore ↥(J₁ ⊔ J₂) = solvableRadical ↥(J₁ ⊔ J₂) :=
  oddTwoCore_eq_solvableRadical_of_twoComponent_sup_eq_top
    (h₁.subgroupOf le_sup_left) (h₂.subgroupOf le_sup_right) (join_factors_generate J₁ J₂)

omit [Finite H] in
private theorem join_factors_ne {J₁ J₂ : Subgroup H} (hne : J₁ ≠ J₂) :
    J₁.subgroupOf (J₁ ⊔ J₂) ≠ J₂.subgroupOf (J₁ ⊔ J₂) := by
  intro he
  apply hne
  have hm := congrArg (map (J₁ ⊔ J₂).subtype) he
  simpa only [map_subgroupOf_eq_of_le le_sup_left,
    map_subgroupOf_eq_of_le le_sup_right] using hm

/-- The actual join has the product of the two intrinsic source quotients,
with the literal inclusions as its marked coordinates. -/
theorem pair_quotient_equiv {J₁ J₂ : Subgroup H}
    (h₁ : J₁.IsTwoComponent) (h₂ : J₂.IsTwoComponent) (hne : J₁ ≠ J₂) :
    ∃ e : (↥(J₁ ⊔ J₂) ⧸ oddTwoCore ↥(J₁ ⊔ J₂)) ≃*
        (J₁ ⧸ oddTwoCore J₁) × (J₂ ⧸ oddTwoCore J₂),
      (∀ j : J₁, e (QuotientGroup.mk' (oddTwoCore ↥(J₁ ⊔ J₂))
        ⟨j.val, mem_sup_left j.property⟩) = (QuotientGroup.mk' (oddTwoCore J₁) j, 1)) ∧
      (∀ j : J₂, e (QuotientGroup.mk' (oddTwoCore ↥(J₁ ⊔ J₂))
        ⟨j.val, mem_sup_right j.property⟩) = (1, QuotientGroup.mk' (oddTwoCore J₂) j)) := by
  let A := J₁.subgroupOf (J₁ ⊔ J₂)
  let B := J₂.subgroupOf (J₁ ⊔ J₂)
  obtain ⟨e, heA, heB⟩ := exists_oddTwoCore_quotient_prod_of_sup_eq_top
    (h₁.subgroupOf le_sup_left) (h₂.subgroupOf le_sup_right)
    (join_factors_ne hne) (join_factors_generate J₁ J₂)
  let a : A ≃* J₁ := subgroupOfEquivOfLe (show J₁ ≤ J₁ ⊔ J₂ from le_sup_left)
  let b : B ≃* J₂ := subgroupOfEquivOfLe (show J₂ ≤ J₁ ⊔ J₂ from le_sup_right)
  let qa := QuotientGroup.congr _ _ a (oddTwoCore_map_equiv a)
  let qb := QuotientGroup.congr _ _ b (oddTwoCore_map_equiv b)
  refine ⟨e.trans (qa.prodCongr qb), ?_, ?_⟩
  · intro j
    let jA : A := ⟨⟨j.val, mem_sup_left j.property⟩, j.property⟩
    change (qa.prodCongr qb) (e (QuotientGroup.mk' _ jA.val)) = _
    rw [heA jA]
    change (qa (QuotientGroup.mk' _ jA), qb 1) = _
    rw [map_one]
    rfl
  · intro j
    let jB : B := ⟨⟨j.val, mem_sup_right j.property⟩, j.property⟩
    change (qa.prodCongr qb) (e (QuotientGroup.mk' _ jB.val)) = _
    rw [heB jB]
    change (qa 1, qb (QuotientGroup.mk' _ jB)) = _
    rw [map_one]
    rfl

/-- The fixed subgroup in the quotient of the actual join is the simple diagonal. -/
noncomputable def pair_fixed_quotient_equiv {J₁ J₂ : Subgroup H}
    (h₁ : J₁.IsTwoComponent) (h₂ : J₂.IsTwoComponent) (hne : J₁ ≠ J₂)
    (σ : MulAut ↥(J₁ ⊔ J₂)) (hσ : Function.Involutive σ)
    (h₁₂ : (J₁.subgroupOf (J₁ ⊔ J₂)).map σ.toMonoidHom = J₂.subgroupOf (J₁ ⊔ J₂))
    (h₂₁ : (J₂.subgroupOf (J₁ ⊔ J₂)).map σ.toMonoidHom = J₁.subgroupOf (J₁ ⊔ J₂)) :
    (MulAut.oddTwoCoreQuotientAut σ).fixedSubgroup ≃* (J₁ ⧸ oddTwoCore J₁) := by
  let e := MulAut.fixedOddTwoCoreQuotientEquivLeftOfSwap
    (h₁.subgroupOf le_sup_left) (h₂.subgroupOf le_sup_right)
    (join_factors_ne hne) (join_factors_generate J₁ J₂) σ hσ h₁₂ h₂₁
  let a := subgroupOfEquivOfLe (show J₁ ≤ J₁ ⊔ J₂ from le_sup_left)
  exact e.trans (QuotientGroup.congr _ _ a (oddTwoCore_map_equiv a))

/-- In the transposed-pair branch, component preservation in the quotient
centralizer makes the literal image the entire diagonal. This is precisely
the GLS 5.22(iv) premise retained for the I.3 assembly owner. -/
theorem local_image_eq_top {J₁ J₂ : Subgroup H}
    (h₁ : J₁.IsTwoComponent) (h₂ : J₂.IsTwoComponent) (hne : J₁ ≠ J₂)
    (σ : MulAut ↥(J₁ ⊔ J₂)) (hσ : Function.Involutive σ)
    (h₁₂ : (J₁.subgroupOf (J₁ ⊔ J₂)).map σ.toMonoidHom = J₂.subgroupOf (J₁ ⊔ J₂))
    (h₂₁ : (J₂.subgroupOf (J₁ ⊔ J₂)).map σ.toMonoidHom = J₁.subgroupOf (J₁ ⊔ J₂))
    (L : Subgroup σ.fixedSubgroup)
    (himage : (L.map (MulAut.oddTwoCoreFixedMap σ)).IsTwoComponent) :
    L.map (MulAut.oddTwoCoreFixedMap σ) = ⊤ := by
  let : IsSimpleGroup (J₁ ⧸ oddTwoCore J₁) := h₁.isSimpleGroup_quotient_oddTwoCore
  let e := pair_fixed_quotient_equiv h₁ h₂ hne σ hσ h₁₂ h₂₁
  let : IsSimpleGroup (MulAut.oddTwoCoreQuotientAut σ).fixedSubgroup := e.isSimpleGroup
  rcases himage.1.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance with hb | ht
  · exact (himage.1.ne_bot hb).elim
  · exact ht

/-- The local two-component has exactly its intrinsic O_{2',2} as the kernel
of the original map into the quotient centralizer. -/
theorem local_core_eq_kernel {J₁ J₂ : Subgroup H}
    (h₁ : J₁.IsTwoComponent) (h₂ : J₂.IsTwoComponent) (hne : J₁ ≠ J₂)
    (σ : MulAut ↥(J₁ ⊔ J₂)) (hσ : Function.Involutive σ)
    (h₁₂ : (J₁.subgroupOf (J₁ ⊔ J₂)).map σ.toMonoidHom = J₂.subgroupOf (J₁ ⊔ J₂))
    (h₂₁ : (J₂.subgroupOf (J₁ ⊔ J₂)).map σ.toMonoidHom = J₁.subgroupOf (J₁ ⊔ J₂))
    {L : Subgroup σ.fixedSubgroup} (hL : L.IsTwoComponent)
    (himage : (L.map (MulAut.oddTwoCoreFixedMap σ)).IsTwoComponent) :
    ((MulAut.oddTwoCoreFixedMap σ).comp L.subtype).ker = oddTwoCore L := by
  let : IsSimpleGroup (J₁ ⧸ oddTwoCore J₁) := h₁.isSimpleGroup_quotient_oddTwoCore
  let e := pair_fixed_quotient_equiv h₁ h₂ hne σ hσ h₁₂ h₂₁
  let : IsSimpleGroup (MulAut.oddTwoCoreQuotientAut σ).fixedSubgroup := e.isSimpleGroup
  apply hL.ker_eq_oddTwoCore_of_surjective_simple
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp, range_subtype]
  exact local_image_eq_top h₁ h₂ hne σ hσ h₁₂ h₂₁ L himage

/-- The I.3.2 quotient identification for the transposed-pair branch. Only
preservation of the local component image remains an earlier-source premise;
no diagonal or quotient equivalence is assumed. -/
noncomputable def local_quotient_equiv_factor {J₁ J₂ : Subgroup H}
    (h₁ : J₁.IsTwoComponent) (h₂ : J₂.IsTwoComponent) (hne : J₁ ≠ J₂)
    (σ : MulAut ↥(J₁ ⊔ J₂)) (hσ : Function.Involutive σ)
    (h₁₂ : (J₁.subgroupOf (J₁ ⊔ J₂)).map σ.toMonoidHom = J₂.subgroupOf (J₁ ⊔ J₂))
    (h₂₁ : (J₂.subgroupOf (J₁ ⊔ J₂)).map σ.toMonoidHom = J₁.subgroupOf (J₁ ⊔ J₂))
    {L : Subgroup σ.fixedSubgroup} (hL : L.IsTwoComponent)
    (himage : (L.map (MulAut.oddTwoCoreFixedMap σ)).IsTwoComponent) :
    (L ⧸ oddTwoCore L) ≃* (J₁ ⧸ oddTwoCore J₁) := by
  let f := (MulAut.oddTwoCoreFixedMap σ).comp L.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    exact local_image_eq_top h₁ h₂ hne σ hσ h₁₂ h₂₁ L himage
  exact (QuotientGroup.liftEquiv (oddTwoCore L) hf
    (local_core_eq_kernel h₁ h₂ hne σ hσ h₁₂ h₂₁ hL himage).symm).trans
      (pair_fixed_quotient_equiv h₁ h₂ hne σ hσ h₁₂ h₂₁)

/-- The kernel formula is the literal intersection with the source core of the join,
including for a component which is subnormal only in the fixed subgroup. -/
theorem local_core_eq_intersection {J₁ J₂ : Subgroup H}
    (h₁ : J₁.IsTwoComponent) (h₂ : J₂.IsTwoComponent) (hne : J₁ ≠ J₂)
    (σ : MulAut ↥(J₁ ⊔ J₂)) (hσ : Function.Involutive σ)
    (h₁₂ : (J₁.subgroupOf (J₁ ⊔ J₂)).map σ.toMonoidHom = J₂.subgroupOf (J₁ ⊔ J₂))
    (h₂₁ : (J₂.subgroupOf (J₁ ⊔ J₂)).map σ.toMonoidHom = J₁.subgroupOf (J₁ ⊔ J₂))
    {L : Subgroup σ.fixedSubgroup} (hL : L.IsTwoComponent)
    (himage : (L.map (MulAut.oddTwoCoreFixedMap σ)).IsTwoComponent) :
    oddTwoCore L = (oddTwoCore ↥(J₁ ⊔ J₂)).comap
      (σ.fixedSubgroup.subtype.comp L.subtype) := by
  rw [← local_core_eq_kernel h₁ h₂ hne σ hσ h₁₂ h₂₁ hL himage]
  ext l
  change (MulAut.oddTwoCoreFixedMap σ l.val = 1) ↔ _
  rw [Subtype.ext_iff, MulAut.oddTwoCoreFixedMap_apply]
  exact QuotientGroup.eq_one_iff _

/-- Application to an actual ambient involution interchanging J and its conjugate.
The resulting action is conjugation on the actual join; every local component
whose image is preserved has the source quotient of J. This retains only the
GLS 5.22(iv) premise assigned to the balance theorem. -/
theorem involution_pair_local_quotients {J : Subgroup H} (hJ : J.IsTwoComponent)
    (t : H) (ht : t * t = 1) (hne : J ≠ J.map (MulAut.conj t).toMonoidHom) :
    ∃ σ : MulAut ↥(J ⊔ J.map (MulAut.conj t).toMonoidHom),
      Function.Involutive σ ∧
      (∀ x, (σ x : H) = t * (x : H) * t⁻¹) ∧
      ∀ L : Subgroup σ.fixedSubgroup, L.IsTwoComponent →
        (L.map (MulAut.oddTwoCoreFixedMap σ)).IsTwoComponent →
        Nonempty ((L ⧸ oddTwoCore L) ≃* (J ⧸ oddTwoCore J)) := by
  have hi : Function.Involutive (MulAut.conj t) := by
    intro g
    change t * (t * g * t⁻¹) * t⁻¹ = g
    calc
      _ = (t * t) * g * (t * t)⁻¹ := by group
      _ = g := by rw [ht]; simp
  obtain ⟨σ, hσ, h₁₂, h₂₁, hσx⟩ :=
    MulAut.exists_involutive_swap_on_join (MulAut.conj t) hi (A := J) rfl
  refine ⟨σ, hσ, hσx, ?_⟩
  intro L hL himage
  exact ⟨local_quotient_equiv_factor hJ (hJ.map_equiv (MulAut.conj t)) hne
    σ hσ h₁₂ h₂₁ hL himage⟩

end CFSG.Quasithin.ChapterI.ComponentQuotients

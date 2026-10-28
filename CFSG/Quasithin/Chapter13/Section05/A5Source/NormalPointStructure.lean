module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalBNPair
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.SymmetricThreeSquare
public import Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# The original normal A5 point quotient and residual factors

The marked cubic and the selected symmetric-three pair commute with trivial
intersection. When the point quotient has order eighteen they therefore
exhaust it, giving C3 x S3. At order thirty-six the faithful orthogonal
embedding is onto S3 x S3.

Transporting the original quaternion factors to the literal O2(H) retains
its center V1. Independent cubic actors then construct two SL2(3) subgroups
whose central product is the actual two-residual. The final consumer maps
these same factors into G, preserving the central line, the residual and
the quaternion two-core. No endpoint or amalgam isomorphism is assumed.

These are local recognition inputs for Aschbacher--Smith 13.5.17, printed
p.922, completing the point-quotient alternatives in 13.5.15(8), pp.920--921.
The quaternion residual argument reuses the intrinsic calculation of
14.2.21, p.988. The compatible unitary-amalgam isomorphism remains separate.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

/-- The original cubic and selected S3 pair exhaust the order-eighteen quotient. -/
theorem normal_point_quotient_of_eighteen
    (h18 : Nat.card (Source.Hstar H) = 18) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Multiplicative (ZMod 3) × Equiv.Perm (Fin 3)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have h : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨_,_,_,_,r,hrH,_,_,_,⟨j⟩⟩ := source_normal_pair_core d hA312 hH hU hn
  let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
  let π := QuotientGroup.mk' (pCore 2 H)
  let A := Source.starImage H (residualCentralizer L V₁)
  let J := Source.starImage H I
  change J ≃* Equiv.Perm (Fin 3) at j
  let : ((residualCentralizer L V₁).subgroupOf H).Normal := hn
  let : A.Normal := Normal.map hn π (QuotientGroup.mk'_surjective _)
  have hA : Nat.card A = 3 := by
    rw [Nat.card_congr (normal_residual_star_cubic d hA312 hH hU hn).toEquiv]
    simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
  have hJ : Nat.card J = 6 := by
    rw [Nat.card_congr j.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hseed : D.Vplus = ⁅D.V,D.L₁⁆ := d.third_eq_commutator
  have hv : Source.starImage H V ≤ centralizer (A : Set (Source.Hstar H)) := by
    rintro _ ⟨v,hv,rfl⟩ _ ⟨l,hl,rfl⟩
    have hc : ⁅v,l⁆ ∈ pCore 2 H := by
      have hm : (⁅v,l⁆ : H).val ∈ D.QH := h.UH_le_QH
        (le_conjugateSpanBy _ _ (hseed.symm ▸ commutator_mem_commutator hv hl))
      exact (show D.QH.subgroupOf H = pCore 2 H from
        comap_map_eq_self_of_injective H.subtype_injective _) ▸ hm
    have he : π v * π l = π l * π v := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [←map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hc
    exact he.symm
  have hconj : V.map (MulAut.conj r).toMonoidHom ≤ H := by
    rintro _ ⟨v,hv,rfl⟩
    exact H.mul_mem (H.mul_mem hrH (h.V_le_H hv)) (H.inv_mem hrH)
  have hcent : J ≤ centralizer (A : Set (Source.Hstar H)) := by
    change (I.subgroupOf H).map π ≤ _
    rw [show I = V ⊔ V.map (MulAut.conj r).toMonoidHom from rfl,
      subgroupOf_sup h.V_le_H hconj,Subgroup.map_sup]
    refine sup_le hv ?_
    rintro _ ⟨x,⟨v,hvV,he⟩,rfl⟩
    let rH : H := ⟨r,hrH⟩
    let vH : H := ⟨v,h.V_le_H hvV⟩
    have hx : x = rH*vH*rH⁻¹ := Subtype.ext he.symm
    rw [hx,map_mul,map_mul,map_inv]
    have hnA : π rH ∈ normalizer (A : Set (Source.Hstar H)) := by
      rw [A.normalizer_eq_top]
      trivial
    exact (mem_normalizer_iff.mp ((normalizer_le_normalizer_centralizer A) hnA)
      (π vH)).mp (hv (mem_map_of_mem π hvV))
  have hd : Disjoint A J := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    let xJ : J := ⟨x,hx.2⟩
    have he : j xJ = 1 := by
      have hc : ∀ x : Equiv.Perm (Fin 3), (∀ y, y*x=x*y) → x=1 := by decide +kernel
      apply hc
      intro y
      obtain ⟨y,rfl⟩ := j.surjective y
      rw [←map_mul,←map_mul]
      apply congrArg j
      exact Subtype.ext ((hcent y.property x hx.1).symm)
    have hx1 : xJ=1 := j.injective (he.trans j.map_one.symm)
    exact congrArg Subtype.val hx1
  let m : A × J →* Source.Hstar H :=
    A.subtype.noncommCoprod J.subtype (fun a j => hcent j.property a a.property)
  have hm : Function.Injective m := by
    apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
    exact ⟨A.subtype_injective,J.subtype_injective,by simpa only [range_subtype] using hd⟩
  have hb : Function.Bijective m := hm.bijective_of_nat_card_le (by
    rw [Nat.card_prod,hA,hJ,h18])
  exact ⟨(MulEquiv.ofBijective m hb).symm.trans
    (MulEquiv.prodCongr (normal_residual_star_cubic d hA312 hH hU hn) j)⟩

/-- The full order-thirty-six quotient exhausts its faithful orthogonal image. -/
theorem normal_point_quotient_of_thirtysix
    (h36 : Nat.card (Source.Hstar H) = 36) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  obtain ⟨f,hf⟩ := (normal_star_embedding d hA312 hH hU hn).1
  apply Nonempty.intro
  apply MulEquiv.ofBijective f
  apply hf.bijective_of_nat_card_le
  change Nat.card (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ≤ _
  rw [h36,Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]

/-- The two point-quotient models, with the original quotient retained. -/
theorem normal_point_quotient_models :
    Nonempty ((H ⧸ pCore 2 H) ≃* Multiplicative (ZMod 3) × Equiv.Perm (Fin 3)) ∨
    Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  rcases normal_star_card_cases d hA312 hH hU hn with h18 | h36
  · exact Or.inl (normal_point_quotient_of_eighteen d hA312 hH hU hn h18)
  · exact Or.inr (normal_point_quotient_of_thirtysix d hA312 hH hU hn h36)

/-- Quaternion coordinates on the literal point two-core retain its marked center. -/
theorem normal_point_core_geometry :
    ∃ _q : QuaternionCentralProductData (pCore 2 H),
      (center (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype) = V₁ := by
  obtain ⟨q,hz⟩ := normal_quaternion_with_center d hA312 hH hU hn
  let e : pCore 2 H ≃* Source.UH H V₃ :=
    ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (normal_core_eq_closure d hA312 hH hU hn))
  refine ⟨q.map e.symm,?_⟩
  have he : (Source.UH H V₃).subtype.comp e.toMonoidHom =
      H.subtype.comp (pCore 2 H).subtype := rfl
  rw [←hz,←center_map_equiv e,map_map,he]

/-- Both possible point orders, deduced from the literal quaternion core. -/
theorem normal_point_card_cases : Nat.card H = 576 ∨ Nat.card H = 1152 := by
  obtain ⟨q,_⟩ := normal_point_core_geometry d hA312 hH hU hn
  have hc := (pCore 2 H).card_mul_index
  rw [q.card,index_eq_card] at hc
  rcases normal_star_card_cases d hA312 hH hU hn with h18 | h36
  · left; change Nat.card (H ⧸ pCore 2 H) = 18 at h18; rw [h18] at hc; exact hc.symm
  · right; change Nat.card (H ⧸ pCore 2 H) = 36 at h36; rw [h36] at hc; exact hc.symm

/-- The original point two-residual is the central product of two actual
SL2(3) subgroups extending the same quaternion factors. -/
theorem normal_point_residual_factors :
    ∃ q : QuaternionCentralProductData (pCore 2 H),
      (center (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype) = V₁ ∧
      Nonempty (QuaternionResidualCentralProduct (pCore 2 H) q) := by
  obtain ⟨q,hz⟩ := normal_point_core_geometry d hA312 hH hU hn
  refine ⟨q,hz,?_⟩
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    rw [←d.characteristic_H H (le_sup_right.trans hH.1.2) hH.2.1]
    exact centralizer_generalizedFitting_le H
  rcases normal_star_card_cases d hA312 hH hU hn with h18 | h36
  · have hc : Nat.card H = 576 := by
      have hc := (pCore 2 H).card_mul_index
      rw [q.card,index_eq_card] at hc
      change Nat.card (H ⧸ pCore 2 H) = 18 at h18
      rw [h18] at hc
      exact hc.symm
    obtain ⟨a⟩ := independent_cubics_of_normal_quaternion_product_card_576
      (pCore 2 H) q hself hc
    obtain ⟨c,_,_⟩ := a.residual_central_product (pCore 2 H) q hc
    exact ⟨c⟩
  · obtain ⟨e⟩ := normal_point_quotient_of_thirtysix d hA312 hH hU hn h36
    exact quaternion_residual_central_product_of_symmetricThree_square
      (pCore 2 H) q rfl hself e

/-- The same factors in the original ambient group retain the source line,
quaternion core and literal point two-residual. -/
theorem normal_point_residual_in_ambient :
    ∃ A B : Subgroup G,
      A ≤ H ∧ B ≤ H ∧
      Nonempty (A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      Nonempty (B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧
      A ⊓ B = V₁ ∧ A ⊔ B = (pResidual 2 H).map H.subtype ∧
      A.pCoreIn 2 ⊔ B.pCoreIn 2 = Source.UH H V₃ := by
  obtain ⟨q,hz,⟨c⟩⟩ := normal_point_residual_factors d hA312 hH hU hn
  let A := c.left.map H.subtype
  let B := c.right.map H.subtype
  refine ⟨A,B,map_subtype_le _,map_subtype_le _,?_,?_,?_,?_,?_,?_⟩
  · exact ⟨(c.left.equivMapOfInjective H.subtype H.subtype_injective).symm.trans
      c.left_model.some⟩
  · exact ⟨(c.right.equivMapOfInjective H.subtype H.subtype_injective).symm.trans
      c.right_model.some⟩
  · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    exact congrArg Subtype.val (c.commute a ha b hb)
  · change c.left.map H.subtype ⊓ c.right.map H.subtype = _
    rw [←map_inf _ _ H.subtype H.subtype_injective,c.intersection,map_map]
    exact hz
  · change c.left.map H.subtype ⊔ c.right.map H.subtype = _
    rw [←Subgroup.map_sup,c.span]
  · change (c.left.map H.subtype).pCoreIn 2 ⊔ (c.right.map H.subtype).pCoreIn 2 = _
    rw [←map_pCoreIn_of_injective 2 c.left H.subtype H.subtype_injective,
      ←map_pCoreIn_of_injective 2 c.right H.subtype H.subtype_injective]
    simp only [pCoreIn]
    rw [c.left_core,c.right_core,←Subgroup.map_sup,←Subgroup.map_sup,q.span,
      ←MonoidHom.range_eq_map,range_subtype]
    exact normal_core_eq_closure d hA312 hH hU hn

end CFSG.Quasithin.Chapter13.Section05.A5Source

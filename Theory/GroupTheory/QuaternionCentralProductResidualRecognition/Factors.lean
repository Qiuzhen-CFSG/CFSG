module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Factors.Action
public import Theory.PGroupCore
public import Theory.SpecificGroups.Quaternion.PresentationHom

/-!
# Embedded quaternion–cubic recognition

A quaternion subgroup and an element of order three inducing a nontrivial
conjugation action generate an embedded copy of SL₂(3). The given quaternion
subgroup is exactly the image of its two-core in the ambient group.

Conjugation by the cubic element forces the action to have cube one. Choosing
standard quaternion coordinates gives a map from the binary tetrahedral
semidirect product. Coprime orders make this map injective, and its image is
the specified join. The quaternion kernel of the projection onto C₃ is the
two-core: every two-subgroup has trivial image in C₃. Transport along the
constructed equivalence retains the original embedded quaternion subgroup.

Source: the SL₂(3) factor step in Aschbacher–Smith, Lemma 14.2.21,
printed p.988 (PDF p.1005). This is the local recognition ingredient, not
an assertion of the whole amalgam lemma.
-/

namespace Subgroup

open GLS3.Chapter5.SchurPresentation

/-- The standard binary-tetrahedral semidirect product maps into an ambient
quaternion--cubic extension. -/
public theorem quaternion_cubic_semidirect_hom
    {G : Type*} [Group G]
    (B : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (x : G) (hx : orderOf x = 3)
    (a : MulAut B)
    (ha : ∀ b : B, (a b : G) = x * b * x⁻¹)
    (hne : a ≠ 1) :
    ∃ F : (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) →* G,
      ∃ e : B ≃* QuaternionGroup 2,
        (∀ q, F (SemidirectProduct.inl q) = e.symm q) ∧
        F (SemidirectProduct.inr (Multiplicative.ofAdd 1)) = x := by
  obtain ⟨e⟩ := hB
  have ha3 : a ^ 3 = 1 := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    change (a (a (a b)) : G) = b
    rw [ha, ha, ha]
    have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
    calc
      x * (x * (x * (b : G) * x⁻¹) * x⁻¹) * x⁻¹ =
          x ^ 3 * b * (x ^ 3)⁻¹ := by simp only [pow_succ, pow_zero, one_mul]; group
      _ = b := by rw [hx3]; simp
  obtain ⟨w, hw⟩ := QuaternionCubicAction.exists_coordinates (MulAut.congr e a)
    (by rw [← map_pow, ha3, map_one])
    (by intro h; apply hne; exact (MulAut.congr e).injective (h.trans (map_one _).symm))
  let e0 := e.trans w
  have he0 : MulAut.congr e0 a = q8Cycle := by
    ext q
    exact DFunLike.congr_fun hw q
  have hxpow : x ^ 3 = 1 := by
    exact (orderOf_eq_iff (by decide)).mp hx |>.1
  let phi : QuaternionGroup 2 →* G := B.subtype.comp e0.symm.toMonoidHom
  let psi : Multiplicative (ZMod 3) →* G :=
    QuaternionGroup.cyclicPowerHom 3 x hxpow
  have hactionOne (q : QuaternionGroup 2) :
      phi (q8Cycle q) = x * phi q * x⁻¹ := by
    have hq : MulAut.congr e0 a = q8Cycle := he0
    have hq' (z : QuaternionGroup 2) : e0 (a (e0.symm z)) = q8Cycle z := by
      have hz := DFunLike.congr_fun hq z
      simpa [MulAut.congr_apply] using hz
    have hb : e0.symm (q8Cycle q) = a (e0.symm q) := by
      apply e0.injective
      rw [e0.apply_symm_apply, hq']
    change (e0.symm (q8Cycle q) : G) = x * (e0.symm q : G) * x⁻¹
    rw [hb]
    exact ha (e0.symm q)
  have haction (k : Multiplicative (ZMod 3)) (q : QuaternionGroup 2) :
      phi (q8C3Action k q) = psi k * phi q * (psi k)⁻¹ := by
    change ZMod 3 at k
    fin_cases k
    · change phi ((q8Cycle ^ 0) q) = psi 1 * phi q * (psi 1)⁻¹
      simp
    · change phi ((q8Cycle ^ 1) q) =
        psi (Multiplicative.ofAdd 1) * phi q * (psi (Multiplicative.ofAdd 1))⁻¹
      simpa [phi, psi, QuaternionGroup.cyclicPowerHom_one] using hactionOne q
    · change phi (q8Cycle (q8Cycle q)) =
        psi (Multiplicative.ofAdd 2) * phi q * (psi (Multiplicative.ofAdd 2))⁻¹
      rw [show psi (Multiplicative.ofAdd 2) = x ^ 2 by
        simpa [psi] using QuaternionGroup.cyclicPowerHom_intCast 3 x hxpow 2]
      calc
        phi (q8Cycle (q8Cycle q)) = x * phi (q8Cycle q) * x⁻¹ := hactionOne (q8Cycle q)
        _ = x * (x * phi q * x⁻¹) * x⁻¹ := by rw [hactionOne]
        _ = x ^ 2 * phi q * (x ^ 2)⁻¹ := by rw [pow_two]; group
  let F : (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) →* G :=
    SemidirectProduct.lift phi psi (by
      intro k
      apply MonoidHom.ext
      intro q
      exact haction k q)
  refine ⟨F, e0, ?_, ?_⟩
  · intro q
    simp [F, phi]
  · simp [F, psi, QuaternionGroup.cyclicPowerHom_one]

private abbrev BinaryTetrahedral :=
  QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)

private theorem quaternion_cubic_map_properties
    {G : Type*} [Group G]
    (B : Subgroup G) (x : G) (hx : orderOf x = 3)
    (F : BinaryTetrahedral →* G) (e : B ≃* QuaternionGroup 2)
    (hFl : ∀ q, F (SemidirectProduct.inl q) = e.symm q)
    (hFx : F (SemidirectProduct.inr (Multiplicative.ofAdd 1)) = x) :
    Function.Injective F ∧ F.range = B ⊔ zpowers x := by
  have hFr (k : Multiplicative (ZMod 3)) :
      F (SemidirectProduct.inr k) = x ^ k.toAdd.val := by
    change ZMod 3 at k
    fin_cases k
    · change F 1 = x ^ 0
      simp
    · change F (SemidirectProduct.inr (Multiplicative.ofAdd 1)) = x ^ 1
      simpa only [pow_one] using hFx
    · have hk : (SemidirectProduct.inr (Multiplicative.ofAdd 2) : BinaryTetrahedral) =
          (SemidirectProduct.inr (Multiplicative.ofAdd 1)) ^ 2 := by decide
      change F (SemidirectProduct.inr (Multiplicative.ofAdd 2)) = x ^ 2
      rw [hk, map_pow, hFx]
  have hFrmem (k : Multiplicative (ZMod 3)) :
      F (SemidirectProduct.inr k) ∈ zpowers x := by
    rw [hFr]
    exact pow_mem (mem_zpowers x) _
  have hd : Disjoint B (zpowers x) := by
    apply disjoint_of_coprime_natCard
    rw [Nat.card_congr e.toEquiv, Nat.card_zpowers, hx, Nat.card_eq_fintype_card]
    norm_num [QuaternionGroup.card]
  have hright : Function.Injective (F.comp SemidirectProduct.inr) := by
    apply (injective_iff_map_eq_one _).mpr
    intro k hk
    change F (SemidirectProduct.inr k) = 1 at hk
    rw [hFr] at hk
    change ZMod 3 at k
    fin_cases k
    · rfl
    · change x ^ 1 = 1 at hk
      have ho := orderOf_dvd_of_pow_eq_one hk
      rw [hx] at ho
      norm_num at ho
    · change x ^ 2 = 1 at hk
      have ho := orderOf_dvd_of_pow_eq_one hk
      rw [hx] at ho
      norm_num at ho
  constructor
  · apply (injective_iff_map_eq_one F).mpr
    intro z hz
    have hm : (e.symm z.left : G) * F (SemidirectProduct.inr z.right) = 1 := by
      rw [← hFl, ← map_mul, SemidirectProduct.inl_left_mul_inr_right, hz]
    have hrB : F (SemidirectProduct.inr z.right) ∈ B := by
      rw [eq_inv_of_mul_eq_one_right hm]
      exact B.inv_mem (e.symm z.left).property
    have hr1 : F (SemidirectProduct.inr z.right) = 1 :=
      (Subgroup.disjoint_def.mp hd) hrB (hFrmem _)
    have hr : z.right = 1 := hright (hr1.trans (map_one _).symm)
    have hl : z.left = 1 := by
      rw [hr1, mul_one] at hm
      apply e.symm.injective
      apply Subtype.ext
      simpa using hm
    apply SemidirectProduct.ext <;> assumption
  · apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      rw [← SemidirectProduct.inl_left_mul_inr_right z, map_mul, hFl]
      exact mul_mem
        ((show B ≤ B ⊔ zpowers x from le_sup_left) (e.symm z.left).property)
        ((show zpowers x ≤ B ⊔ zpowers x from le_sup_right) (hFrmem _))
    · apply sup_le
      · intro b hb
        exact ⟨SemidirectProduct.inl (e ⟨b, hb⟩), by rw [hFl]; simp⟩
      · exact zpowers_le.mpr ⟨SemidirectProduct.inr (Multiplicative.ofAdd 1), hFx⟩

private theorem binaryTetrahedral_twoCore :
    pCore 2 BinaryTetrahedral =
      (SemidirectProduct.inl : QuaternionGroup 2 →* BinaryTetrahedral).range := by
  let i : QuaternionGroup 2 →* BinaryTetrahedral := SemidirectProduct.inl
  let r : BinaryTetrahedral →* Multiplicative (ZMod 3) := SemidirectProduct.rightHom
  have hn : i.range.Normal := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hq : IsPGroup 2 (QuaternionGroup 2) := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_eq_fintype_card]; norm_num [QuaternionGroup.card])
  have hi : IsPGroup 2 i.range := hq.of_surjective i.rangeRestrict i.rangeRestrict_surjective
  have hc : IsPGroup 3 (Multiplicative (ZMod 3)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_eq_fintype_card]; rfl)
  have hm : (pCore 2 BinaryTetrahedral).map r = ⊥ := by
    have hd := IsPGroup.disjoint_of_coprime (pCore_isPGroup.map r)
      (hc.to_subgroup ⊤) (by decide : Nat.Coprime 2 3)
    simpa using hd
  apply le_antisymm
  · rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    intro z hz
    have hh : r z ∈ (pCore 2 BinaryTetrahedral).map r := ⟨z, hz, rfl⟩
    rwa [hm, mem_bot] at hh
  · exact le_sSup ⟨hn, hi⟩

/-- An embedded quaternion subgroup extended by a nontrivial cubic conjugation
is SL₂(3), and its actual embedded two-core is the given quaternion subgroup. -/
public theorem quaternion_cubic_extension_recognition
    {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) (hB : Nonempty (B ≃* QuaternionGroup 2))
    (x : G) (hx : orderOf x = 3) (a : MulAut B)
    (ha : ∀ b : B, (a b : G) = x * b * x⁻¹) (hne : a ≠ 1) :
    Nonempty (↥(B ⊔ zpowers x) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      (pCore 2 ↥(B ⊔ zpowers x)).map (B ⊔ zpowers x).subtype = B := by
  obtain ⟨F, e, hFl, hFx⟩ := quaternion_cubic_semidirect_hom B hB x hx a ha hne
  obtain ⟨hFi, hFr⟩ := quaternion_cubic_map_properties B x hx F e hFl hFx
  let L := B ⊔ zpowers x
  have hmem (z : BinaryTetrahedral) : F z ∈ L := by
    change F z ∈ B ⊔ zpowers x
    rw [← hFr]
    exact ⟨z, rfl⟩
  let f : BinaryTetrahedral →* L := F.codRestrict L hmem
  have hf : Function.Bijective f := by
    constructor
    · intro y z h
      exact hFi (congrArg Subtype.val h)
    · intro y
      have hy : (y : G) ∈ F.range := by rw [hFr]; exact y.property
      obtain ⟨z, hz⟩ := hy
      exact ⟨z, Subtype.ext hz⟩
  let E : BinaryTetrahedral ≃* L := MulEquiv.ofBijective f hf
  refine ⟨⟨E.symm.trans binaryTetrahedralEquivSL⟩, ?_⟩
  change (pCore 2 L).map L.subtype = B
  rw [← pCore_map_iso 2 E, binaryTetrahedral_twoCore, map_map, MonoidHom.map_range]
  ext b
  constructor
  · rintro ⟨q, rfl⟩
    change F (SemidirectProduct.inl q) ∈ B
    rw [hFl]
    exact (e.symm q).property
  · intro hb
    refine ⟨e ⟨b, hb⟩, ?_⟩
    change F (SemidirectProduct.inl (e ⟨b, hb⟩)) = b
    rw [hFl]
    simp

end Subgroup

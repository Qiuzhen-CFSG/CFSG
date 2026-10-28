module

public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.NaturalIdentification.Cores

/-!
# Elementary sixteen-group normalizers in the split natural binary block

In the genuine semidirect product E₈ ⋊ SL₃(2), every elementary abelian
subgroup B of order sixteen has normalizer of order 192. Its intersection
with the translation kernel is a four-group, and the two subgroups have
exactly the same normalizer.

For the displayed middle subgroup, the intersection is the translation
plane v₂ = 0. Conjugating its two basis translations forces the last row
entries (2,0) and (2,1) of the projecting matrix to vanish. Thus its
normalizer is the literal line preimage. The established normalization
of the middle subgroup gives the reverse inclusion. Sylow conjugacy and
the uniqueness of the elementary sixteen-group in UT₄(2) then give the
result for arbitrary B, preserving the actual projection kernel.

This is the split-model normalizer calculation used in M. Aschbacher,
“A 2-local characterization of M12”, Lemma 3.2, printed p.37, with the
split extensions and elementary sixteen-group of Lemma 3.1. It does not
assert the ambient recognition conclusion L ≅ A₈.
Source: https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf
-/

public section


open Subgroup
namespace Matrix.PSL3Two.SplitParabolic

private theorem inl_mem_middle (v : E3) :
    (SemidirectProduct.inl v : Block) ∈ middleGroup ↔ v.toAdd 2 = 0 := by
  constructor
  · rintro ⟨w, hw⟩
    exact (congrArg (fun g : Block => g.left.toAdd 2) hw).symm
  · intro hv
    refine ⟨Multiplicative.ofAdd ![v.toAdd 1, v.toAdd 0, 0, 0], ?_⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      fin_cases i <;> simp [middleMap, middleElement, hv]
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> rfl

/-- The literal intersection is the translation plane with last coordinate zero. -/
theorem mem_middle_inf_ker (g : Block) :
    g ∈ middleGroup ⊓ projection.ker ↔ g.right = 1 ∧ g.left.toAdd 2 = 0 := by
  have he (h : g.right = 1) : (SemidirectProduct.inl g.left : Block) = g :=
    SemidirectProduct.ext rfl h.symm
  constructor
  · rintro ⟨hm, hk⟩
    have hk' : g.right = 1 := hk
    exact ⟨hk', (inl_mem_middle g.left).mp (he hk' ▸ hm)⟩
  · rintro ⟨hk, hv⟩
    exact ⟨he hk ▸ (inl_mem_middle g.left).mpr hv, hk⟩

private def middlePlaneEquiv : (middleGroup ⊓ projection.ker : Subgroup Block) ≃ (Fin 2 → ZMod 2) where
  toFun x := ![x.val.left.toAdd 0, x.val.left.toAdd 1]
  invFun v := ⟨SemidirectProduct.inl (Multiplicative.ofAdd ![v 0, v 1, 0]),
    (mem_middle_inf_ker _).mpr ⟨rfl, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      have hx := ((mem_middle_inf_ker _).mp x.property).2
      fin_cases i <;> simp [hx]
    · exact ((mem_middle_inf_ker _).mp x.property).1.symm
  right_inv v := by funext i; fin_cases i <;> rfl

/-- The middle sixteen-group meets the translation kernel in a four-group. -/
theorem card_middle_inf_ker : Nat.card (middleGroup ⊓ projection.ker : Subgroup Block) = 4 := by
  rw [Nat.card_congr middlePlaneEquiv, Nat.card_eq_fintype_card]
  decide

private theorem conj_inl (g : Block) (v : E3) :
    g * SemidirectProduct.inl v * g⁻¹ = SemidirectProduct.inl (naturalAction g.right v) := by
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one,
      SemidirectProduct.inv_left]
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    simp [mul_comm]
  · simp

private theorem normalizer_middle_inf_ker_le_line :
    normalizer ((middleGroup ⊓ projection.ker : Subgroup Block) : Set Block) ≤ linePreimage := by
  intro g hg
  have h (v : E3) (hv : v.toAdd 2 = 0) :
      (naturalAction g.right v).toAdd 2 = 0 := by
    have hm : (SemidirectProduct.inl v : Block) ∈ middleGroup ⊓ projection.ker :=
      (mem_middle_inf_ker _).mpr ⟨rfl, hv⟩
    have hc := (mem_normalizer_iff.mp hg _).mp hm
    rw [conj_inl] at hc
    exact ((mem_middle_inf_ker _).mp hc).2
  change g.right ∈ lineParabolicSL
  rw [mem_lineParabolicSL_iff]
  constructor
  · have h0 := h (Multiplicative.ofAdd ![1,0,0]) rfl
    change (g.right.val.mulVec ![1,0,0]) 2 = 0 at h0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h0
  · have h1 := h (Multiplicative.ofAdd ![0,1,0]) rfl
    change (g.right.val.mulVec ![0,1,0]) 2 = 0 at h1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h1

private theorem normalizer_middle_le_normalizer_inf_ker :
    normalizer (middleGroup : Set Block) ≤
      normalizer ((middleGroup ⊓ projection.ker : Subgroup Block) : Set Block) :=
  (le_inf le_rfl le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf

/-- The normalizer is the actual preimage of the line stabilizer under `projection`. -/
theorem normalizer_middle_eq_linePreimage :
    normalizer (middleGroup : Set Block) = linePreimage :=
  le_antisymm (normalizer_middle_le_normalizer_inf_ker.trans normalizer_middle_inf_ker_le_line)
    linePreimage_normalizes_middle

/-- The translation plane has the same literal normalizer as the middle sixteen-group. -/
theorem normalizer_middle_inf_ker_eq_linePreimage :
    normalizer ((middleGroup ⊓ projection.ker : Subgroup Block) : Set Block) = linePreimage :=
  le_antisymm normalizer_middle_inf_ker_le_line
    (linePreimage_normalizes_middle.trans normalizer_middle_le_normalizer_inf_ker)

/-- Uniqueness of the elementary sixteen-group inside the marked Sylow subgroup. -/
theorem elementary_sixteen_eq_middle_of_le_standardSylow
    (B : Subgroup Block) (hB : IsElementaryAbelian 2 B)
    (hc : Nat.card B = 16) (hle : B ≤ standardSylow) : B = middleGroup := by
  let _ := hB
  let C := (B.subgroupOf standardSylow).map sylowEquiv.symm.toMonoidHom
  let _ : IsElementaryAbelian 2 (B.subgroupOf standardSylow) :=
    IsElementaryAbelian.subgroupOf hle
  let _ : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  have hC : Nat.card C = 16 := by
    rw [card_map_of_injective sylowEquiv.symm.injective,
      Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hc]
  have hCA : C ≤ Unitriangular.A := Unitriangular.large_elementary_le C hC.ge
  apply eq_of_le_of_card_ge _ (by rw [hc, middleGroup_card])
  intro x hx
  have hcx : sylowEquiv.symm ⟨x, hle hx⟩ ∈ C := ⟨⟨x, hle hx⟩, hx, rfl⟩
  have hm : sylowMap (sylowEquiv.symm ⟨x, hle hx⟩) ∈ middleGroup := by
    rw [← middle_image]
    exact ⟨_, hCA hcx, rfl⟩
  have he : sylowMap (sylowEquiv.symm ⟨x, hle hx⟩) = x :=
    congrArg Subtype.val (sylowEquiv.apply_symm_apply ⟨x, hle hx⟩)
  exact he ▸ hm

/-- Every elementary sixteen-group is conjugate to the marked middle subgroup. -/
theorem elementary_sixteen_conjugate_middle (B : Subgroup Block)
    (hB : IsElementaryAbelian 2 B) (hc : Nat.card B = 16) :
    ∃ g : Block, B.map (MulAut.conj g).toMonoidHom = middleGroup := by
  let _ := hB
  obtain ⟨P, hBP⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Block P naturalSylow
  have hP : (P : Subgroup Block).map (MulAut.conj g).toMonoidHom = standardSylow :=
    congrArg (fun S : Sylow 2 Block => (S : Subgroup Block)) hg
  refine ⟨g, elementary_sixteen_eq_middle_of_le_standardSylow _
    (IsElementaryAbelian.map _) ?_ ?_⟩
  · exact (card_map_of_injective (MulAut.conj g).injective).trans hc
  · exact hP ▸ map_mono hBP

/-- The elementary-sixteen normalizer geometry in the genuine natural split extension. -/
theorem elementary_sixteen_normalizer_geometry (B : Subgroup Block)
    (hB : IsElementaryAbelian 2 B) (hc : Nat.card B = 16) :
    Nat.card (normalizer (B : Set Block)) = 192 ∧
      Nat.card (B ⊓ projection.ker : Subgroup Block) = 4 ∧
      normalizer (B : Set Block) = normalizer ((B ⊓ projection.ker : Subgroup Block) : Set Block) := by
  obtain ⟨g, hg⟩ := elementary_sixteen_conjugate_middle B hB hc
  let e := MulAut.conj g
  have he : B.map e.toMonoidHom = middleGroup := hg
  have hker : (B ⊓ projection.ker).map e.toMonoidHom = middleGroup ⊓ projection.ker := by
    rw [map_inf _ _ _ e.injective, he]
    exact congrArg (middleGroup ⊓ ·) (Normal.map_conj_eq projection.ker g)
  have hn : (normalizer (B : Set Block)).map e.toMonoidHom = linePreimage := by
    rw [map_equiv_normalizer_eq, he, normalizer_middle_eq_linePreimage]
  have hni : (normalizer ((B ⊓ projection.ker : Subgroup Block) : Set Block)).map
      e.toMonoidHom = linePreimage := by
    rw [map_equiv_normalizer_eq, hker, normalizer_middle_inf_ker_eq_linePreimage]
  refine ⟨?_, ?_, ?_⟩
  · rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, hn, card_linePreimage]
  · rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, hker, card_middle_inf_ker]
  · exact (Subgroup.map_injective (f := e.toMonoidHom) e.injective) (hn.trans hni.symm)

end Matrix.PSL3Two.SplitParabolic

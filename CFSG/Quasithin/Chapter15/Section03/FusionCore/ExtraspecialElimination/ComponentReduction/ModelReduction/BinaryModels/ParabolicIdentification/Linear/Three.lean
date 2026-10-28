module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Flags
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups

/-!
# Actual degree-three parabolics with the prescribed model

The concrete PSL₃(2) Borel has order eight. Its index-three overgroup has
order 24, so the proved Borel-overgroup exhaustion identifies it as the
point or line stabilizer. Transporting a conjugating matrix gives actual
basis flag coordinates for both the overgroup and the original Sylow.
The resulting flag retains the supplied projective marking.

Source: Aschbacher–Smith, 15.3.49(l), combined manuscript (1 March 2004),
printed pp.1143–1145; the concrete point-line exhaustion is in
`Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups`.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Three
open Chapter2.ComponentRefinement.LieType.Binary
open Chapter1
local notation "SL₃" => Matrix.PSL3Two.SL

private noncomputable def standardBasis : Basis 2 := Pi.basisFun (ZMod 2) (Fin 3)

private theorem cutSpace_mem (i : Fin 2) (v : Vector 3) :
    v ∈ cutSpace standardBasis i ↔ ∀ j : Fin 3, i.val < j.val → v j = 0 := by
  rw [cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  change (∀ j : Fin 3, v j ≠ 0 → j.val ≤ i.val) ↔ _
  constructor
  · intro h j hj
    by_contra hv
    exact Nat.not_le_of_gt hj (h j hv)
  · intro h j hj
    by_contra hle
    exact hj (h j (Nat.lt_of_not_ge hle))

private theorem cutSpace_zero (v : Vector 3) :
    v ∈ cutSpace standardBasis 0 ↔ v 1 = 0 ∧ v 2 = 0 := by
  rw [cutSpace_mem]
  simp [Fin.forall_fin_succ]

private theorem cutSpace_one (v : Vector 3) :
    v ∈ cutSpace standardBasis 1 ↔ v 2 = 0 := by
  rw [cutSpace_mem]
  simp [Fin.forall_fin_succ]

private theorem point_map :
    Matrix.PSL3Two.pointParabolicSL.map (slEquivLinear 3).toMonoidHom =
      cutStabilizer standardBasis {0} := by
  ext g
  obtain ⟨g, rfl⟩ := (slEquivLinear 3).surjective g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, mem_cutStabilizer]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [Matrix.PSL3Two.pointParabolicSL, MulAction.mem_stabilizer_set]
  apply forall_congr'
  intro v
  exact (iff_congr (cutSpace_zero ((slEquivLinear 3) g v)) (cutSpace_zero v)).symm

private theorem line_map :
    Matrix.PSL3Two.lineParabolicSL.map (slEquivLinear 3).toMonoidHom =
      cutStabilizer standardBasis {1} := by
  ext g
  obtain ⟨g, rfl⟩ := (slEquivLinear 3).surjective g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, mem_cutStabilizer]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [Matrix.PSL3Two.lineParabolicSL, MulAction.mem_stabilizer_set]
  apply forall_congr'
  intro v
  exact (iff_congr (cutSpace_one ((slEquivLinear 3) g v)) (cutSpace_one v)).symm

private theorem borel_map :
    Matrix.PSL3Two.borelSL.map (slEquivLinear 3).toMonoidHom =
      cutStabilizer standardBasis Set.univ := by
  rw [Matrix.PSL3Two.borelSL, Subgroup.map_inf _ _ _ (slEquivLinear 3).injective,
    point_map, line_map]
  ext g
  simp only [mem_inf, mem_cutStabilizer, Set.mem_singleton_iff, forall_eq,
    Set.mem_univ, forall_const]
  exact ⟨fun h i => by fin_cases i; exact h.1; exact h.2,
    fun h => ⟨h 0, h 1⟩⟩

private noncomputable def standardSylow : Sylow 2 SL₃ :=
  Sylow.ofCard Matrix.PSL3Two.borelSL (by
    rw [Matrix.PSL3Two.card_borelSL, Matrix.PSL3Two.card_SL]
    decide +kernel)

private theorem standard_overgroup (P : Subgroup SL₃) (hBP : Matrix.PSL3Two.borelSL ≤ P)
    (hi : Matrix.PSL3Two.borelSL.relIndex P = 3) :
    P = Matrix.PSL3Two.pointParabolicSL ∨ P = Matrix.PSL3Two.lineParabolicSL := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup SL₃) Matrix.PSL3Two.borelSL P bot_le hBP
  simp only [relIndex_bot_left, Matrix.PSL3Two.card_borelSL, hi] at hc
  have hcard : Nat.card P = 24 := hc.symm
  have htop : P ≠ ⊤ := by
    intro he
    rw [he, Nat.card_congr (Subgroup.topEquiv).toEquiv, Matrix.PSL3Two.card_SL] at hcard
    contradiction
  rcases Matrix.PSL3Two.overgroup_borelSL P hBP htop with hp | hl
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hp (by rw [hcard, Matrix.PSL3Two.card_pointParabolicSL]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hl (by rw [hcard, Matrix.PSL3Two.card_lineParabolicSL]))

private theorem cutSpace_map (b : Basis 2) (g : BinaryLinear.GL (Vector 3)) (i : Fin 2) :
    cutSpace (b.map g) i = (cutSpace b i).map g.toLinearMap := by
  rw [cutSpace, cutSpace, Submodule.map_span]
  congr 1
  ext v
  simp

private theorem cutStabilizer_map_conj (b : Basis 2) (cuts : Set (Fin 2))
    (g : BinaryLinear.GL (Vector 3)) :
    (cutStabilizer b cuts).map (MulAut.conj g).toMonoidHom =
      cutStabilizer (b.map g) cuts := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_cutStabilizer, mem_cutStabilizer]
  simp_rw [cutSpace_map, Submodule.mem_map_equiv]
  constructor
  · intro hx i hi v
    have h := hx i hi (g.symm v)
    simpa only [MulAut.conj_symm_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using h
  · intro hx i hi v
    have h := hx i hi (g v)
    simpa only [MulAut.conj_symm_apply, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using h

private theorem map_conj_linear (D : Subgroup SL₃) (g : SL₃) :
    (D.map (MulAut.conj g).toMonoidHom).map (slEquivLinear 3).toMonoidHom =
      (D.map (slEquivLinear 3).toMonoidHom).map
        (MulAut.conj (slEquivLinear 3 g)).toMonoidHom := by
  rw [map_map, map_map]
  apply congrArg (fun f : SL₃ →* BinaryLinear.GL (Vector 3) => D.map f)
  apply MonoidHom.ext
  intro x
  change slEquivLinear 3 (g * x * g⁻¹) = slEquivLinear 3 g * slEquivLinear 3 x * (slEquivLinear 3 g)⁻¹
  simp only [map_mul, map_inv]

private theorem coordinates (S : Sylow 2 SL₃) (P : Subgroup SL₃)
    (hSP : (S : Subgroup SL₃) ≤ P) (hi : (S : Subgroup SL₃).relIndex P = 3) :
    ∃ (b : Basis 2) (cuts : Set (Fin 2)),
      P.map (slEquivLinear 3).toMonoidHom = cutStabilizer b cuts ∧
      (S : Subgroup SL₃).map (slEquivLinear 3).toMonoidHom = cutStabilizer b Set.univ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL₃ standardSylow S
  have hmap : Matrix.PSL3Two.borelSL.map (MulAut.conj g).toMonoidHom =
      (S : Subgroup SL₃) := by
    change ((g • standardSylow : Sylow 2 SL₃) : Subgroup SL₃) = _
    rw [hg]
  let Q := P.map (MulAut.conj g).symm.toMonoidHom
  have hBQ : Matrix.PSL3Two.borelSL ≤ Q := by
    intro u hu
    apply Subgroup.mem_map_equiv.mpr
    apply hSP
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  have hQP : Q.map (MulAut.conj g).toMonoidHom = P :=
    (Subgroup.map_symm_eq_iff_map_eq Q (e := MulAut.conj g) (H := P)).mp rfl
  have hiQ : Matrix.PSL3Two.borelSL.relIndex Q = 3 := by
    rw [← relIndex_map_map_of_injective Matrix.PSL3Two.borelSL Q (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
      hmap, hQP]
    exact hi
  obtain ⟨cuts, hcuts⟩ : ∃ cuts : Set (Fin 2),
      Q.map (slEquivLinear 3).toMonoidHom = cutStabilizer standardBasis cuts := by
    rcases standard_overgroup Q hBQ hiQ with he | he
    · exact ⟨{0}, he ▸ point_map⟩
    · exact ⟨{1}, he ▸ line_map⟩
  refine ⟨standardBasis.map (slEquivLinear 3 g), cuts, ?_, ?_⟩
  · rw [← hQP, map_conj_linear, hcuts, cutStabilizer_map_conj]
  · rw [← hmap, map_conj_linear, borel_map, cutStabilizer_map_conj]

/-- The point or line stabilizer is transported through the canonical binary
linear action, retaining the supplied component equivalence. -/
theorem exists_position {K : Type*} [Group K] [Finite K]
    (L S P : Subgroup K) (e : L ≃* PSL 3) (hs : IsSylowIn 2 S L)
    (hSP : S ≤ P) (hPL : P ≤ L) (hi : S.relIndex P = 3) :
    ∃ pos : ModelExclusions.BinaryGeometry.Position L P 3, pos.model = e := by
  let f := e.trans (slEquivPSL 3).symm
  obtain ⟨Q, _, hQP, hindex⟩ := model_inputs L S P f hs hSP hPL hi
  obtain ⟨b, cuts, hP, hQ⟩ := coordinates Q _ hQP hindex
  have hlinear : ((P.subgroupOf L).map f.toMonoidHom).map (slEquivLinear 3).toMonoidHom =
      (P.subgroupOf L).map (linearModel e).toMonoidHom := by
    rw [map_map]
    rfl
  rw [hlinear] at hP
  apply position_of_coordinates (m := 2) (by decide) e hPL b cuts hP
  have heq := relIndex_map_map_of_injective (Q : Subgroup SL₃)
    ((P.subgroupOf L).map f.toMonoidHom) (f := (slEquivLinear 3).toMonoidHom) (slEquivLinear 3).injective
  rw [hQ, hlinear, hP, hindex] at heq
  exact heq

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Three

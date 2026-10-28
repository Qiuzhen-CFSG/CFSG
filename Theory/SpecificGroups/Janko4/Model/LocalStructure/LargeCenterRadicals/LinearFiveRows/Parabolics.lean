module
public import Theory.SpecificGroups.HigherLinear.RadicalParabolics
public import Theory.SpecificGroups.HigherLinear.SubspaceTransport
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.Blocks
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.RadicalNormalizerControl
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Large exterior fixed spaces force a hyperplane parabolic

A nontrivial two-radical of SL₅(2) has a partial-flag normalizer. Radical
saturation puts the entire two-core of every flag subspace stabilizer in the
radical. Cross-block transvections show that the cores for subspaces of
dimensions one, two and three fix at most four exterior dimensions.
A fixed space of order at least 64 therefore forces every flag subspace to
be a hyperplane. Strictness collapses the flag to one subspace, and the full
intrinsic normalizer quotient is the concrete A₈ through its SL₄(2) Levi.

This supplies the nontrivial linear-image row in the native J₄ reduction.
Source: An--O'Brien--Wilson (2003), Section 4 and Table 1, pp.122,124.
The type-A radical flag theorem is proved in `HigherLinear.RadicalParabolics`;
the exterior action is the literal second exterior power, as in
Kleidman--Wilson (1988), Lemma 1.1.1, p.485.
-/

@[expose] public noncomputable section
open Subgroup
open Representation.SL5TenDimensional Representation.SL5ExteriorSquare
open Matrix.HigherLinear BinaryLinear.OuterCyclic
namespace Janko4.LocalStructure.LargeCenterRadicals.LinearFiveParabolics

private theorem exists_conjugate_parabolic (W : Submodule (ZMod 2) (Fin 5 → ZMod 2)) :
    ∃ g : Group, (parabolicSL W).map (MulAut.conj g).toMonoidHom =
      Representation.SL5ExteriorSquare.parabolic (Module.finrank (ZMod 2) W) := by
  have hd : Module.finrank (ZMod 2) W ≤ 5 := by simpa using W.finrank_le
  obtain ⟨e,he⟩ := BinaryLinear.FourParabolicAction.exists_linearEquiv_map_eq W
    (naturalFlag (Module.finrank (ZMod 2) W)) (finrank_naturalFlag _ hd).symm
  let g := (slEquivLinear 5).symm e
  have heg : slEquivLinear 5 g = e := (slEquivLinear 5).apply_symm_apply e
  have heW (v : Fin 5 → ZMod 2) : e v ∈ naturalFlag (Module.finrank (ZMod 2) W) ↔ v ∈ W := by
    rw [← he]
    simp only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  refine ⟨g, ?_⟩
  ext x
  obtain ⟨x,rfl⟩ := (MulAut.conj g).surjective x
  rw [mem_map_equiv, MulEquiv.symm_apply_apply]
  change (∀ v, Matrix.SpecialLinearGroup.toLin' x v ∈ W ↔ v ∈ W) ↔
    ∀ v, Matrix.SpecialLinearGroup.toLin' (g * x * g⁻¹) v ∈ naturalFlag _ ↔ v ∈ naturalFlag _
  have hact : Matrix.SpecialLinearGroup.toLin' g = e := by
    apply LinearEquiv.ext
    intro v
    change slEquivLinear 5 g v = e v
    rw [heg]
  constructor
  · intro hx v
    obtain ⟨w,rfl⟩ := e.surjective v
    simp only [map_mul, LinearEquiv.mul_apply, map_inv, LinearEquiv.coe_inv,
      hact, LinearEquiv.symm_apply_apply, heW, hx]
  · intro hx v
    have hh := hx (e v)
    simpa only [map_mul, LinearEquiv.mul_apply, map_inv, LinearEquiv.coe_inv,
      hact, LinearEquiv.symm_apply_apply, heW] using hh

private theorem elementary_mem_core (k : ℕ) (hk : k ≤ 5) (i j : Fin 5)
    (hi : i.val < k) (hj : k ≤ j.val) :
    elementary i j ∈ (Representation.SL5ExteriorSquare.parabolic k).pCoreIn 2 := by
  have hij : i ≠ j := by intro h; subst j; omega
  have hp : elementary i j ∈ Representation.SL5ExteriorSquare.parabolic k := by
    rw [mem_parabolic_iff_lowerLeft_zero]
    intro a b ha hb
    have hab : a ≠ b := by intro h; subst b; omega
    have hia : i ≠ a := by intro h; subst a; omega
    simp [elementary, hij, Matrix.SpecialLinearGroup.transvection_coe,
      hab, hia]
  refine ⟨⟨elementary i j,hp⟩,?_,rfl⟩
  apply (mem_parabolic_twoCore_iff k hk ⟨elementary i j,hp⟩).mpr
  constructor
  · intro a b
    have hjb : j ≠ Fin.castLE hk b := by intro h; subst j; have := b.isLt; simp only [Fin.val_castLE] at hj; omega
    simp [elementary, hij, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.one_apply, hjb]
  · intro a b
    have hia : i ≠ (⟨k+a.val,by omega⟩ : Fin 5) := by intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp [elementary, hij, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.one_apply, hia, Fin.ext_iff]

private def lowerIndex : Fin 3 → Fin 10 → Fin 5 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]]

private def upperIndex : Fin 3 → Fin 10 → Fin 5 :=
  ![![1, 1, 1, 1, 1, 1, 1, 2, 2, 3], ![2, 2, 3, 4, 2, 3, 4, 2, 2, 3], ![3, 3, 3, 4, 3, 3, 4, 3, 4, 3]]

private def outputIndex : Fin 3 → Fin 10 → Fin 10 :=
  ![![0, 0, 0, 0, 1, 2, 3, 2, 3, 3], ![0, 0, 0, 0, 0, 0, 0, 2, 3, 3], ![0, 0, 0, 0, 0, 0, 0, 1, 1, 3]]

private def surviving : Fin 3 → Finset (Fin 10) := ![{0,1,2,3},{0},{0,1,4}]

private theorem index_cross (k : Fin 3) (t : Fin 10) :
    (lowerIndex k t).val < k.val + 1 ∧ k.val + 1 ≤ (upperIndex k t).val := by
  revert k t
  decide

private theorem coordinate_step (k : Fin 3) (v : V) (t : Fin 10)
    (ht : t ∉ surviving k) :
    coordinates (exteriorAction 2 (elementary (lowerIndex k t) (upperIndex k t)) v)
      (outputIndex k t) = coordinates v (outputIndex k t) + coordinates v t := by
  have row : actionMatrix (elementary (lowerIndex k t) (upperIndex k t)) (outputIndex k t) =
      Pi.single (outputIndex k t) 1 + Pi.single t 1 := by
    fin_cases k <;> fin_cases t
    all_goals first | exact (ht (by decide)).elim | (ext j; fin_cases j <;> rfl)
  rw [coordinates_action]
  change dotProduct (actionMatrix _ (outputIndex k t)) (coordinates v) = _
  rw [row, add_dotProduct]
  simp

private theorem small_parabolic_fixed_rank (k : Fin 3) :
    Module.finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace (exteriorAction 2)
      ((Representation.SL5ExteriorSquare.parabolic (k.val+1)).pCoreIn 2)) ≤ 4 := by
  have hle : Representation.BinaryOffender.fixedSpace (exteriorAction 2)
      ((Representation.SL5ExteriorSquare.parabolic (k.val+1)).pCoreIn 2) ≤ coordinateSpan (surviving k) := by
    intro v hv
    rw [mem_coordinateSpan]
    intro t ht
    have he := hv ⟨_,elementary_mem_core (k.val+1) (by omega) _ _
      (index_cross k t).1 (index_cross k t).2⟩
    have hh := coordinate_step k v t ht
    change exteriorAction 2 (elementary (lowerIndex k t) (upperIndex k t)) v = v at he
    rw [he] at hh
    exact add_eq_left.mp hh.symm
  have hh := Submodule.finrank_mono hle
  rw [finrank_coordinateSpan] at hh
  exact hh.trans ((by decide : ∀ k, (surviving k).card ≤ 4) k)

private theorem core_map (L : Subgroup Group) (g : Group) :
    (L.map (MulAut.conj g).toMonoidHom).pCoreIn 2 =
      (L.pCoreIn 2).map (MulAut.conj g).toMonoidHom := by
  have h := pCoreIn_range_of_injective 2 ((MulAut.conj g).toMonoidHom.comp L.subtype)
    ((MulAut.conj g).injective.comp L.subtype_injective)
  rw [MonoidHom.range_comp, range_subtype] at h
  simpa only [pCoreIn, map_map] using h

private theorem fixed_rank_conj (U : Subgroup Group) (g : Group) :
    Module.finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace (exteriorAction 2)
      (U.map (MulAut.conj g).toMonoidHom)) =
    Module.finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace (exteriorAction 2) U) := by
  let E : V ≃ₗ[ZMod 2] V :=
    LinearMap.GeneralLinearGroup.toLinearEquiv ((exteriorAction 2).asGroupHom g)
  have hE (a : Group) (v : V) :
      E (exteriorAction 2 a v) = exteriorAction 2 ((MulAut.conj g) a) (E v) := by
    change exteriorAction 2 g (exteriorAction 2 a v) =
      exteriorAction 2 (g*a*g⁻¹) (exteriorAction 2 g v)
    simp only [← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  rw [← Representation.BinaryOffender.fixedSpace_map_equivariant (exteriorAction 2)
    (exteriorAction 2) (MulAut.conj g).toMonoidHom E hE U, E.finrank_map_eq]

/-- Radical saturation puts the whole core of each containing parabolic in U. -/
theorem parabolic_core_le (U : Subgroup Group) (hU : U.IsPRadical 2)
    (W : Submodule (ZMod 2) (Fin 5 → ZMod 2))
    (hN : normalizer (U : Set Group) ≤ parabolicSL W) :
    (parabolicSL W).pCoreIn 2 ≤ U := by
  exact le_of_normalizer_le_normalizer_of_pCore_normalizer_le U _ hU.isPGroup
    (isPGroup_pCoreIn 2 _) hU.2.le
    (hN.trans ((parabolicSL W).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (parabolicSL W)))))

/-- A proper invariant subspace of a large-fixed-space radical is a hyperplane. -/
theorem invariant_subspace_rank (U : Subgroup Group) (hU : U.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (Representation.BinaryOffender.fixedSpace (exteriorAction 2) U))
    (W : Submodule (ZMod 2) (Fin 5 → ZMod 2)) (hW : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hN : normalizer (U : Set Group) ≤ parabolicSL W) : Module.finrank (ZMod 2) W = 4 := by
  have hdpos : 0 < Module.finrank (ZMod 2) W := by
    let := Submodule.nontrivial_iff_ne_bot.mpr hW
    exact Module.finrank_pos
  have hdlt : Module.finrank (ZMod 2) W < 5 := by simpa using Submodule.finrank_lt hWt
  by_contra hd
  have hdsmall : Module.finrank (ZMod 2) W ≤ 3 := by omega
  let k : Fin 3 := ⟨Module.finrank (ZMod 2) W - 1,by omega⟩
  have hk : k.val + 1 = Module.finrank (ZMod 2) W := by dsimp [k]; omega
  obtain ⟨g,hg⟩ := exists_conjugate_parabolic W
  have hc : (Representation.SL5ExteriorSquare.parabolic (k.val+1)).pCoreIn 2 ≤
      U.map (MulAut.conj g).toMonoidHom := by
    rw [hk, ← hg, core_map]
    exact map_mono (parabolic_core_le U hU W hN)
  have hrank : Module.finrank (ZMod 2)
      (Representation.BinaryOffender.fixedSpace (exteriorAction 2) U) ≤ 4 := by
    rw [← fixed_rank_conj U g]
    refine (Submodule.finrank_mono ?_).trans (small_parabolic_fixed_rank k)
    intro v hv a
    exact hv ⟨a.val,hc a.property⟩
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Representation.BinaryOffender.fixedSpace (exteriorAction 2) U)
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hrank
  simp only [ZMod.card, Nat.card_eq_fintype_card] at hcard
  omega

/-- The full normalizer of a nontrivial radical with at least 64 exterior
fixed vectors is conjugate to the hyperplane parabolic. -/
theorem radical_normalizer_hyperplane (U : Subgroup Group) (hU : U.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (Representation.BinaryOffender.fixedSpace (exteriorAction 2) U)) :
    ∃ g : Group, (normalizer (U : Set Group)).map (MulAut.conj g).toMonoidHom =
      Representation.SL5ExteriorSquare.parabolic 4 := by
  obtain ⟨k,W,hk,_,hs,hproper,hN⟩ := binary_five_radical_normalizer U hU
  have hd (i : Fin k) : Module.finrank (ZMod 2) (W i) = 4 :=
    invariant_subspace_rank U hU hlarge (W i) (hproper i).1 (hproper i).2
      (by rw [hN]; exact iInf_le _ i)
  let i : Fin k := ⟨0,hk⟩
  have hsame (j : Fin k) : W i = W j := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact hs.monotone (show i ≤ j from Nat.zero_le j.val)
    · rw [hd,hd]
  obtain ⟨g,hg⟩ := exists_conjugate_parabolic (W i)
  refine ⟨g,?_⟩
  have hnorm : normalizer (U : Set Group) = parabolicSL (W i) := by
    rw [hN]
    apply le_antisymm (iInf_le _ i)
    apply le_iInf
    intro j
    rw [hsame j]
  rw [hnorm, hg, hd]

/-- The full intrinsic quotient in the nontrivial linear image case is A8. -/
def radicalQuotientEquiv (U : Subgroup Group) (hU : U.IsPRadical 2)
    (hlarge : 64 ≤ Nat.card (Representation.BinaryOffender.fixedSpace (exteriorAction 2) U)) :
    (normalizer (U : Set Group) ⧸ pCore 2 (normalizer (U : Set Group))) ≃*
      alternatingGroup (Fin 8) := by
  let g := Classical.choose (radical_normalizer_hyperplane U hU hlarge)
  have hg := Classical.choose_spec (radical_normalizer_hyperplane U hU hlarge)
  let e := ((MulAut.conj g).subgroupMap (normalizer (U : Set Group))).trans
    (MulEquiv.subgroupCongr hg)
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (parabolicFourQuotientEquiv.trans
      (Atlas.Order20160A8.sl4TwoEquivPSL.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8))

end Janko4.LocalStructure.LargeCenterRadicals.LinearFiveParabolics

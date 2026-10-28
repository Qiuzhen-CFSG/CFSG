module
public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionResidual.Preserving.ScalarCubic
public import Theory.Representation.OrthogonalFourPlusMatrix.Displacement
public import Theory.Representation.OrthogonalFourPlusMatrix.SylowFixedDimension
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.AlternatingFivePairCubicCriterion
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# Elementary actors in the determinant tensor normalizer

The binary determinant tensor is the eight-dimensional restriction of scalars of
`M₂(𝔽₄)`, with `(a,b)` acting by `X ↦ a X b⁻¹`. Its full binary linear
normalizer acts on the two marked `SL₂(4)` factors. The odd scalar centralizer
makes this action faithful on elementary two-groups, so the automorphism
geometry of `A₅ × A₅` bounds their rank by four.

In rank three there is a nontrivial inner involution. Uniqueness of its lift
identifies the actual tensor operator, which moves at least four dimensions.
In rank four there are inner involutions on the separate factors; conjugating
them to transvections bounds the common fixed space by two and gives fixed
codimension at least six. These are the high-rank estimates used to exclude
FF offenders in the tensor case of Aschbacher--Smith, Appendix D.3.9(1)
(printed pp. 199--200). The low-rank exclusion is a separate result.
-/

@[expose] public noncomputable section
open Module Matrix
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Representation.BinaryOffender Representation.BinaryOffender.NaturalTensor
open Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms

local instance : Finite (Module.End (ZMod 2) V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

theorem action_asGroupHom_injective : Function.Injective action.asGroupHom :=
  fun _ _ h => action_injective (congrArg Units.val h)

def actionImageEquiv : G ≃* actionImage action :=
  MonoidHom.ofInjective action_asGroupHom_injective

def normalizerConjugation : linearNormalizer action →* MulAut G :=
  (MulAut.congr actionImageEquiv.symm).toMonoidHom.comp
    (actionImage action).normalizerMonoidHom

theorem normalizerConjugation_action (t : linearNormalizer action) (g : G) (v : V) :
    action (normalizerConjugation t g) (t.val.val v) = t.val.val (action g v) := by
  have he : action.asGroupHom (normalizerConjugation t g) =
      t.val * action.asGroupHom g * t.val⁻¹ := by
    exact congrArg Subtype.val (actionImageEquiv.apply_symm_apply
      ((actionImage action).normalizerMonoidHom t (actionImageEquiv g)))
  have hcomm : action.asGroupHom (normalizerConjugation t g) * t.val =
      t.val * action.asGroupHom g := by rw [he]; group
  exact congrArg (fun u : (Module.End (ZMod 2) V)ˣ => u.val v) hcomm

private theorem centralizing_involution_end_eq_one (T : Module.End (ZMod 2) V)
    (hT2 : T * T = 1)
    (hT : ∀ g v, T (action g v) = action g (T v)) : T = 1 := by
  let u : (Module.End (ZMod 2) V)ˣ := ⟨T, T, hT2, hT2⟩
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv u
  have he2 : e ^ 2 = 1 := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun D : Module.End (ZMod 2) V => D v) hT2
  have hc : ∀ g : G, Commute e (linearAction g) := by
    intro g
    change e * linearAction g = linearAction g * e
    apply LinearEquiv.ext
    intro v
    exact hT g v
  exact congrArg LinearEquiv.toLinearMap
    (InvolutionResidual.centralizing_involution_eq_one e he2 hc)

theorem normalizerConjugation_involution_ne_one (t : linearNormalizer action)
    (ht2 : t * t = 1) (ht : t ≠ 1) : normalizerConjugation t ≠ 1 := by
  intro he
  apply ht
  apply Subtype.ext
  apply Units.ext
  apply centralizing_involution_end_eq_one
  · exact congrArg (fun x : linearNormalizer action => x.val.val) ht2
  · intro g v
    have hh := normalizerConjugation_action t g v
    rw [he] at hh
    exact hh.symm

theorem normalizerConjugation_elementary_injective
    (A : Subgroup (linearNormalizer action)) [IsElementaryAbelian 2 A] :
    Function.Injective (normalizerConjugation.comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  by_contra hne
  exact normalizerConjugation_involution_ne_one x.val
    (by simpa only [pow_two] using
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : linearNormalizer action) x.property)
    hne hx

private theorem inner_intertwiner_eq_of_centralizing_involution
    {K H U : Type*} [Field K] [Group H] [AddCommGroup U] [Module K U]
    (ρ : Representation K H U)
    (hc : ∀ D : Module.End K U, D * D = 1 →
      (∀ g v, D (ρ g v) = ρ g (D v)) → D = 1)
    (T : Module.End K U) (hT2 : T * T = 1) (r : H) (hr : r * r = 1)
    (hT : ∀ g v, T (ρ g v) = ρ (r * g * r⁻¹) (T v)) : T = ρ r := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_left hr
  have hTr : T * ρ r = ρ r * T := by
    apply LinearMap.ext
    intro v
    have h := hT r v
    rw [hr, one_mul, hri] at h
    exact h
  let D := ρ r * T
  have hD2 : D * D = 1 := by
    calc
      D * D = ρ r * (T * ρ r) * T := by simp only [D, mul_assoc]
      _ = ρ r * (ρ r * T) * T := by rw [hTr]
      _ = (ρ r * ρ r) * (T * T) := by simp only [mul_assoc]
      _ = 1 := by rw [← map_mul, hr, map_one, hT2, one_mul]
  have hDcomm : ∀ g v, D (ρ g v) = ρ g (D v) := by
    intro g v
    change ρ r (T (ρ g v)) = ρ g (ρ r (T v))
    have hgr : r * (r * g * r⁻¹) = g * r := by
      rw [← mul_assoc, ← mul_assoc, hr, one_mul, hri]
    rw [hT, ← Module.End.mul_apply, ← map_mul, hgr, map_mul, Module.End.mul_apply]
  have hD := hc D hD2 hDcomm
  calc
    T = (ρ r * ρ r) * T := by rw [← map_mul, hr, map_one, one_mul]
    _ = ρ r * D := by simp only [D, mul_assoc]
    _ = ρ r := by rw [hD, mul_one]

theorem inner_involution_eq_action (t : linearNormalizer action)
    (ht2 : t * t = 1) (r : G) (hr : r * r = 1)
    (ht : normalizerConjugation t = MulAut.conj r) : t.val.val = action r := by
  apply inner_intertwiner_eq_of_centralizing_involution action
    centralizing_involution_end_eq_one t.val.val
    (congrArg (fun x : linearNormalizer action => x.val.val) ht2) r hr
  intro g v
  have h := normalizerConjugation_action t g v
  rw [ht] at h
  exact h.symm

theorem inner_involution_displacement (t : linearNormalizer action)
    (ht2 : t * t = 1) (r : G) (hr2 : r * r = 1) (hr : r ≠ 1)
    (ht : normalizerConjugation t = MulAut.conj r) :
    4 ≤ operatorFixedCodim t.val.val := by
  rw [inner_involution_eq_action t ht2 r hr2 ht]
  exact Displacement.displacement_rank_four r hr



private abbrev SL := Matrix.SpecialLinearGroup (Fin 2) F
private def root : SL := SpecialLinearGroup.transvection zero_ne_one (1 : F)

private lemma root_square : root * root = 1 := by
  rw [root, ← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    SpecialLinearGroup.transvection_coeff_zero]

private lemma root_inv : root⁻¹ = root := inv_eq_of_mul_eq_one_left root_square

private lemma root_ne_one : root ≠ 1 := by
  intro h
  have hh := congrArg (fun g : SL => g.val 0 1) h
  simp [root, SpecialLinearGroup.transvection_coe] at hh

private lemma exists_conjugate_root (a : SL) (ha : a * a = 1) (hne : a ≠ 1) :
    ∃ c : SL, c * root * c⁻¹ = a := by
  let e := Theory.PSL2.sl2QuotientEquiv F
  have hoa : orderOf a = 2 := (orderOf_eq_prime_iff (p := 2)).mpr ⟨by rw [pow_two, ha], hne⟩
  have hoq : orderOf root = 2 := (orderOf_eq_prime_iff (p := 2)).mpr
    ⟨by rw [pow_two, root_square], root_ne_one⟩
  have hp := Theory.PSL2.involutions_isConj (e root) (e a)
    ((e.orderOf_eq root).trans hoq) ((e.orderOf_eq a).trans hoa)
  have hc : IsConj root a := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      using e.symm.toMonoidHom.map_isConj hp
  exact isConj_iff.mp hc

/-- Two nonidentity inner involutions on separate factors fix at most a binary plane. -/
theorem common_inner_fixed_finrank (a b : Matrix.SpecialLinearGroup (Fin 2) F)
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    finrank (ZMod 2) ↥(LinearMap.ker (action (a, 1) - 1) ⊓
      LinearMap.ker (action (1, b) - 1)) ≤ 2 := by
  obtain ⟨c, hc⟩ := exists_conjugate_root a ha ha1
  obtain ⟨d, hd⟩ := exists_conjugate_root b hb hb1
  let W := LinearMap.ker (action (a, 1) - 1) ⊓ LinearMap.ker (action (1, b) - 1)
  let W' := W.map (action (c⁻¹, d⁻¹))
  have hleft (v : V) : action (root, 1) (action (c⁻¹, d⁻¹) v) =
      action (c⁻¹, d⁻¹) (action (a, 1) v) := by
    simp only [← Module.End.mul_apply, ← map_mul]
    apply congrArg (fun g : G => action g v)
    apply Prod.ext
    · change root * c⁻¹ = c⁻¹ * a
      rw [← hc]
      group
    · exact one_mul d⁻¹ |>.trans (mul_one d⁻¹).symm
  have hright (v : V) : action (1, root) (action (c⁻¹, d⁻¹) v) =
      action (c⁻¹, d⁻¹) (action (1, b) v) := by
    simp only [← Module.End.mul_apply, ← map_mul]
    apply congrArg (fun g : G => action g v)
    apply Prod.ext
    · exact one_mul c⁻¹ |>.trans (mul_one c⁻¹).symm
    · change root * d⁻¹ = d⁻¹ * b
      rw [← hd]
      group
  have hfixleft (v : V) (hv : v ∈ W') : action (root, 1) v = v := by
    obtain ⟨w, hw, rfl⟩ := hv
    rw [hleft, sub_eq_zero.mp hw.1, Module.End.one_apply]
  have hfixright (v : V) (hv : v ∈ W') : action (1, root⁻¹) v = v := by
    obtain ⟨w, hw, rfl⟩ := hv
    rw [root_inv, hright, sub_eq_zero.mp hw.2, Module.End.one_apply]
  have hbnd : finrank (ZMod 2) W' ≤ 2 :=
    finrank_le_two_of_fixed_transvections W' hfixleft hfixright
  have he : finrank (ZMod 2) W' = finrank (ZMod 2) W :=
    (linearAction (c⁻¹, d⁻¹)).finrank_map_eq W
  exact he.symm.le.trans hbnd

/-- The literal independent inner operators force displacement at least six. -/
theorem fixedCodim_ge_six_of_independent_inner
    (A : Subgroup (Module.End (ZMod 2) V)ˣ)
    (a b : Matrix.SpecialLinearGroup (Fin 2) F) (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (haA : action.asGroupHom (a, 1) ∈ A) (hbA : action.asGroupHom (1, b) ∈ A) :
    6 ≤ fixedCodim (Units.coeHom _) A := by
  let W := LinearMap.ker (action (a, 1) - 1) ⊓ LinearMap.ker (action (1, b) - 1)
  have hle : fixedSpace (Units.coeHom _) A ≤ W := by
    intro v hv
    exact ⟨sub_eq_zero.mpr (hv ⟨_, haA⟩), sub_eq_zero.mpr (hv ⟨_, hbA⟩)⟩
  have hh := (Submodule.finrank_mono hle).trans (common_inner_fixed_finrank a b ha hb ha1 hb1)
  have he := fixedCodim_add_finrank (Units.coeHom (Module.End (ZMod 2) V)) A
  change finrank (ZMod 2) (fixedSpace (Units.coeHom (Module.End (ZMod 2) V)) A) ≤ 2 at hh
  rw [finrank_binary] at he
  change 6 ≤ fixedCodim (Units.coeHom (Module.End (ZMod 2) V)) A
  omega


/-- The two marked SL₂(4) factors identified with the actual alternating groups. -/
def alternatingPairEquiv : G ≃* Pair :=
  Representation.SL2FourNatural.alternatingFiveEquiv.prodCongr
    Representation.SL2FourNatural.alternatingFiveEquiv

/-- Conjugation of the full linear normalizer on the actual alternating-five pair. -/
def alternatingConjugation : linearNormalizer action →* MulAut Pair :=
  (MulAut.congr alternatingPairEquiv).toMonoidHom.comp normalizerConjugation

theorem alternatingConjugation_elementary_injective
    (A : Subgroup (linearNormalizer action)) [IsElementaryAbelian 2 A] :
    Function.Injective (alternatingConjugation.comp A.subtype) :=
  (MulAut.congr alternatingPairEquiv).injective.comp
    (normalizerConjugation_elementary_injective A)

private theorem pullback_inner (t : linearNormalizer action) (r : Pair)
    (ht : alternatingConjugation t = MulAut.conj r) :
    normalizerConjugation t = MulAut.conj (alternatingPairEquiv.symm r) := by
  apply (MulAut.congr alternatingPairEquiv).injective
  change alternatingConjugation t = _
  rw [ht]
  apply MulEquiv.ext
  intro x
  simp [MulAut.congr]

/-- The full normalizer cannot increase the elementary two-rank past four. -/
theorem elementary_normalizer_rank_le_four
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A) : rank A ≤ 4 := by
  let := hA.2
  have hh := faithful_actor_rank_le_four (alternatingConjugation.comp A.subtype)
    (alternatingConjugation_elementary_injective A)
  rwa [← Representation.AlternatingFivePairCubicCriterion.rank_eq_primeRank A hA] at hh

/-- A rank-three actor contains an actual inner operator moving four dimensions. -/
theorem exists_inner_operator_of_rank_ge_three
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A) (hr : 3 ≤ rank A) :
    ∃ t ∈ A, t ≠ 1 ∧ 4 ≤ operatorFixedCodim t.val.val := by
  let := hA.2
  have hpr : 3 ≤ primeRank 2 A := by
    rwa [← Representation.AlternatingFivePairCubicCriterion.rank_eq_primeRank A hA]
  obtain ⟨t, ht, r, hr1, hr2, htr⟩ := faithful_actor_inner
    (alternatingConjugation.comp A.subtype) (alternatingConjugation_elementary_injective A) hpr
  have ht2 : (t : linearNormalizer action) * t = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (t : linearNormalizer action) t.property
  have hr2' : alternatingPairEquiv.symm r * alternatingPairEquiv.symm r = 1 := by
    simpa only [pow_two, map_mul, map_one] using congrArg alternatingPairEquiv.symm hr2
  have hr1' : alternatingPairEquiv.symm r ≠ 1 := by
    intro h
    apply hr1
    simpa only [map_one, MulEquiv.apply_symm_apply] using congrArg alternatingPairEquiv h
  refine ⟨t, t.property, ?_, inner_involution_displacement t ht2 _ hr2' hr1'
    (pullback_inner t r htr)⟩
  intro h
  exact ht (Subtype.ext h)

/-- The whole rank-three actor moves at least four dimensions. -/
theorem fixedCodim_ge_four_of_rank_ge_three
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A) (hr : 3 ≤ rank A) :
    4 ≤ fixedCodim (normalizerRepresentation action) A := by
  obtain ⟨t, ht, _, hb⟩ := exists_inner_operator_of_rank_ge_three A hA hr
  exact hb.trans (operatorFixedCodim_le_fixedCodim (normalizerRepresentation action) A ht)

/-- Rank four supplies independently supported actual inner operators and displacement six. -/
theorem fixedCodim_ge_six_of_rank_ge_four
    (A : Subgroup (linearNormalizer action)) (hA : IsElementaryTwo A) (hr : 4 ≤ rank A) :
    6 ≤ fixedCodim (normalizerRepresentation action) A := by
  let := hA.2
  have hpr : 4 ≤ primeRank 2 A := by
    rwa [← Representation.AlternatingFivePairCubicCriterion.rank_eq_primeRank A hA]
  obtain ⟨t, u, r, s, hr1, hs1, hr2, hs2, htr, hus⟩ := faithful_actor_independent_inner
    (alternatingConjugation.comp A.subtype) (alternatingConjugation_elementary_injective A) hpr
  let a := Representation.SL2FourNatural.alternatingFiveEquiv.symm r
  let b := Representation.SL2FourNatural.alternatingFiveEquiv.symm s
  have ha : a * a = 1 := by
    simpa only [a, pow_two, map_mul, map_one] using
      congrArg Representation.SL2FourNatural.alternatingFiveEquiv.symm hr2
  have hb : b * b = 1 := by
    simpa only [b, pow_two, map_mul, map_one] using
      congrArg Representation.SL2FourNatural.alternatingFiveEquiv.symm hs2
  have ha1 : a ≠ 1 := by
    intro h
    apply hr1
    simpa only [a, map_one, MulEquiv.apply_symm_apply] using
      congrArg Representation.SL2FourNatural.alternatingFiveEquiv h
  have hb1 : b ≠ 1 := by
    intro h
    apply hs1
    simpa only [b, map_one, MulEquiv.apply_symm_apply] using
      congrArg Representation.SL2FourNatural.alternatingFiveEquiv h
  have ht2 : (t : linearNormalizer action) * t = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (t : linearNormalizer action) t.property
  have hu2 : (u : linearNormalizer action) * u = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (u : linearNormalizer action) u.property
  have hfirst : alternatingPairEquiv.symm (r, 1) = (a, 1) := by
    apply Prod.ext
    · rfl
    · exact map_one Representation.SL2FourNatural.alternatingFiveEquiv.symm
  have hsecond : alternatingPairEquiv.symm (1, s) = (1, b) := by
    apply Prod.ext
    · exact map_one Representation.SL2FourNatural.alternatingFiveEquiv.symm
    · rfl
  have htr' : normalizerConjugation t = MulAut.conj (a, 1) := by
    rw [← hfirst]
    exact pullback_inner t (r, 1) htr
  have hus' : normalizerConjugation u = MulAut.conj (1, b) := by
    rw [← hsecond]
    exact pullback_inner u (1, s) hus
  have hte := inner_involution_eq_action t ht2 (a, 1) (Prod.ext ha (one_mul _)) htr'
  have hue := inner_involution_eq_action u hu2 (1, b) (Prod.ext (one_mul _) hb) hus'
  have htmem : action.asGroupHom (a, 1) ∈ A.map (linearNormalizer action).subtype := by
    refine ⟨t, t.property, ?_⟩
    exact Units.ext hte
  have humem : action.asGroupHom (1, b) ∈ A.map (linearNormalizer action).subtype := by
    refine ⟨u, u.property, ?_⟩
    exact Units.ext hue
  have hh := fixedCodim_ge_six_of_independent_inner
    (A.map (linearNormalizer action).subtype) a b ha hb ha1 hb1 htmem humem
  rw [← fixedCodim_map_equivariant (normalizerRepresentation action) (Units.coeHom _)
    (linearNormalizer action).subtype (LinearEquiv.refl (ZMod 2) V)
    (fun _ _ => rfl) A] at hh
  exact hh

end ClassicalOrthogonal.FourPlusMatrix.Binary

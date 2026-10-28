module
public import Theory.Representation.AlternatingFiveMovedPair.NaturalDisplacement
public import Theory.Representation.AlternatingFiveMovedPair.NaturalJointDisplacement
public import Theory.Representation.AlternatingFiveMovedPair.NaturalSwapIntertwiners
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OrthogonalFour.TensorModel
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Basic

/-!
# Full normalizer involutions on the natural descent pair

The faithful natural descent pair gives literal conjugation on SL₂(4)².
Automorphisms preserve or exchange the two factors. In the first case an
inner or field intertwiner bound gives displacement eight. In the second,
explicit inner and field lifts conjugate the operator to an arbitrary
involutory swap intertwiner, whose displacement is at least six. The
centralizing involution theorem removes the conjugation kernel on elementary
two-subgroups, retaining the original actor and its rank.

Source: Aschbacher–Smith, quasithin manuscript, D.3.5, pp.195–196.
-/

@[expose] public noncomputable section
open Module
open scoped TensorProduct
namespace Representation.AlternatingFiveMovedPair.Natural
open SL2FourNatural BinaryOffender BinaryOffender.NaturalTensor

/-- The marked product acts faithfully on the first tensor constituent. -/
theorem action_injective : Function.Injective action := by
  intro g h he
  apply ClassicalOrthogonal.FourPlusMatrix.Binary.action_injective
  apply LinearMap.ext
  intro m
  obtain ⟨v, rfl⟩ := (RankTwo.OrthogonalFour.tensorCoordinates (K := F)).surjective m
  have hv := congrArg (fun f : Module.End (ZMod 2) Space => (f (v, 0)).1) he
  change first g v = first h v at hv
  have hm := congrArg (RankTwo.OrthogonalFour.tensorCoordinates (K := F)) hv
  exact (RankTwo.OrthogonalFour.tensorCoordinates_equivariant g v).symm.trans
    (hm.trans (RankTwo.OrthogonalFour.tensorCoordinates_equivariant h v))

theorem action_asGroupHom_injective : Function.Injective action.asGroupHom :=
  fun _ _ h => action_injective (congrArg Units.val h)

/-- The faithful action identifies the marked product with its linear image. -/
def actionImageEquiv : (SL × SL) ≃* actionImage action :=
  MonoidHom.ofInjective action_asGroupHom_injective

/-- Literal conjugation on the original two marked SL₂ factors. -/
def normalizerConjugation : linearNormalizer action →* MulAut (SL × SL) :=
  (MulAut.congr actionImageEquiv.symm).toMonoidHom.comp
    (actionImage action).normalizerMonoidHom

theorem normalizerConjugation_action (t : linearNormalizer action) (g : SL × SL) (v : Space) :
    action (normalizerConjugation t g) (t.val.val v) = t.val.val (action g v) := by
  have he : action.asGroupHom (normalizerConjugation t g) =
      t.val * action.asGroupHom g * t.val⁻¹ := by
    have h := congrArg Subtype.val (actionImageEquiv.apply_symm_apply
      ((actionImage action).normalizerMonoidHom t (actionImageEquiv g)))
    exact h
  have hcomm : action.asGroupHom (normalizerConjugation t g) * t.val =
      t.val * action.asGroupHom g := by rw [he]; group
  exact congrArg (fun u : (Module.End (ZMod 2) Space)ˣ => u.val v) hcomm

lemma tensorFrobenius_action (g : SL × SL) (v : Tensor) :
    tensorFrobenius (first g v) =
      first (slFrobenius g.1, slFrobenius g.2) (tensorFrobenius v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change tensorFrobenius (SL2FourNatural.action g.1 x ⊗ₜ[F]
        SL2FourNatural.action g.2 y) = _
    rw [tensorFrobenius_tmul, tensorFrobenius_tmul, frobenius_action, frobenius_action]
    rfl
  | add u v hu hv => simp only [map_add, hu, hv]

/-- Exchanging the descent constituents twists the second factor. -/
def secondFieldLift : Space ≃ₗ[ZMod 2] Space := LinearEquiv.prodComm _ _ _

lemma secondFieldLift_action (g : SL × SL) (v : Space) :
    secondFieldLift (action g v) = action (g.1, slFrobenius g.2) (secondFieldLift v) := by
  apply Prod.ext
  · rfl
  · change first g v.1 = first (g.1, slFrobenius (slFrobenius g.2)) v.1
    rw [slFrobenius_involutive]

/-- Simultaneous Frobenius followed by constituent exchange twists the first factor. -/
def firstFieldLift : Space ≃ₗ[ZMod 2] Space :=
  (tensorFrobenius.prodCongr tensorFrobenius).trans secondFieldLift

lemma firstFieldLift_action (g : SL × SL) (v : Space) :
    firstFieldLift (action g v) = action (slFrobenius g.1, g.2) (firstFieldLift v) := by
  apply Prod.ext
  · change tensorFrobenius (first (g.1, slFrobenius g.2) v.2) = _
    rw [tensorFrobenius_action, slFrobenius_involutive]
    rfl
  · exact tensorFrobenius_action g v.1

theorem automorphism_cases (a : MulAut SL) :
    (∃ r : SL, a = MulAut.conj r) ∨
      (∃ r : SL, a = MulAut.conj r * slFrobenius) := by
  obtain ⟨r, σ, hσ⟩ := Theory.PSL2.sl2_semilinear_coverage a
  rcases SemilinearNormalizer.fieldAutomorphism_cases σ with h | h
  · left
    refine ⟨r, ?_⟩
    rw [hσ, h]
    change MulAut.conj r * 1 = MulAut.conj r
    exact mul_one _
  · right
    refine ⟨r, ?_⟩
    rw [hσ, h]
    rfl

/-- Every automorphism of the first factor has an actual binary linear lift. -/
theorem exists_first_automorphism_lift (a : MulAut SL) :
    ∃ E : Space ≃ₗ[ZMod 2] Space,
      ∀ g v, E (action g v) = action (a g.1, g.2) (E v) := by
  rcases automorphism_cases a with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · refine ⟨LinearMap.GeneralLinearGroup.toLinearEquiv (action.asGroupHom (r, 1)), ?_⟩
    intro g v
    change action (r, 1) (action g v) =
      action (r * g.1 * r⁻¹, g.2) (action (r, 1) v)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    have hh : (r, (1 : SL)) * g = (r * g.1 * r⁻¹, g.2) * (r, 1) := by
      ext <;> simp [mul_assoc]
    rw [hh]
  · let R := LinearMap.GeneralLinearGroup.toLinearEquiv (action.asGroupHom (r, 1))
    refine ⟨firstFieldLift.trans R, ?_⟩
    intro g v
    change action (r, 1) (firstFieldLift (action g v)) =
      action (r * slFrobenius g.1 * r⁻¹, g.2) (action (r, 1) (firstFieldLift v))
    rw [firstFieldLift_action, ← Module.End.mul_apply, ← Module.End.mul_apply,
      ← map_mul, ← map_mul]
    have hh : (r, (1 : SL)) * (slFrobenius g.1, g.2) =
        (r * slFrobenius g.1 * r⁻¹, g.2) * (r, 1) := by
      ext <;> simp [mul_assoc]
    rw [hh]



private lemma inner_square (r : SL) (h : MulAut.conj r * MulAut.conj r = 1) :
    r * r = 1 := by
  apply Theory.GroupTheory.conj_injective_of_center_eq_bot (Theory.PSL2.sl2_center_eq_bot F)
  rw [map_mul, h, map_one]

private lemma first_automorphism_intertwiner_bound (T : Module.End (ZMod 2) Space)
    (hTi : Function.Injective T) (a : MulAut SL) (ha2 : a * a = 1) (ha : a ≠ 1)
    (hT : ∀ g v, T (action (g, 1) v) = action (a g, 1) (T v)) :
    8 ≤ operatorFixedCodim T := by
  rcases automorphism_cases a with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · apply first_inner_intertwiner_bound T hTi r (inner_square r ha2) _ hT
    intro hr
    apply ha
    rw [hr, map_one]
  · apply first_field_intertwiner_bound T r fieldFrobenius.toRingHom _ hT
    refine ⟨⟨0, 1⟩, ?_⟩
    decide +kernel

private lemma second_automorphism_intertwiner_bound (T : Module.End (ZMod 2) Space)
    (hTi : Function.Injective T) (a : MulAut SL) (ha2 : a * a = 1) (ha : a ≠ 1)
    (hT : ∀ g v, T (action (1, g) v) = action (1, a g) (T v)) :
    8 ≤ operatorFixedCodim T := by
  rcases automorphism_cases a with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · apply second_inner_intertwiner_bound T hTi r (inner_square r ha2) _ hT
    intro hr
    apply ha
    rw [hr, map_one]
  · apply second_field_intertwiner_bound T r fieldFrobenius.toRingHom _ hT
    refine ⟨⟨0, 1⟩, ?_⟩
    decide +kernel

/-- Factor-preserving nontrivial involutions move eight dimensions, even when
an intertwiner mixes the two descent constituents. -/
theorem preserving_involution_intertwiner_bound (T : Module.End (ZMod 2) Space)
    (hTi : Function.Injective T) (a b : MulAut SL)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hne : a ≠ 1 ∨ b ≠ 1)
    (hT : ∀ g v, T (action g v) = action (a g.1, b g.2) (T v)) :
    8 ≤ operatorFixedCodim T := by
  rcases hne with ha | hb
  · apply first_automorphism_intertwiner_bound T hTi a ha2 ha
    intro g v
    simpa only [map_one] using hT (g, 1) v
  · apply second_automorphism_intertwiner_bound T hTi b hb2 hb
    intro g v
    simpa only [map_one] using hT (1, g) v

/-- Arbitrary markings on the two exchanged factors do not change the
six-dimensional lower bound for an involutory swap intertwiner. -/
theorem swapped_involution_intertwiner_bound (T : Module.End (ZMod 2) Space)
    (hT2 : T * T = 1) (a b : MulAut SL) (_hab : a * b = 1) (hba : b * a = 1)
    (hT : ∀ g v, T (action g v) = action (a g.2, b g.1) (T v)) :
    6 ≤ operatorFixedCodim T := by
  obtain ⟨E, hE⟩ := exists_first_automorphism_lift a
  let S := E.symm.conj T
  have hES (v : Space) : E (S v) = T (E v) := by simp [S]
  have hS2 : S * S = 1 := by
    apply LinearMap.ext
    intro v
    apply E.injective
    change E (S (S v)) = E v
    rw [hES, hES]
    exact congrArg (fun f : Module.End (ZMod 2) Space => f (E v)) hT2
  have hS (g : SL × SL) (v : Space) :
      S (action g v) = action (g.2, g.1) (S v) := by
    apply E.injective
    rw [hES, hE, hT, hE, hES]
    have hbg : b (a g.1) = g.1 := MulEquiv.congr_fun hba g.1
    rw [hbg]
  have hd := swap_intertwiner_displacement S hS2 hS
  have he := operatorFixedCodim_eq_of_equiv S T E hES
  rwa [he] at hd

/-- The full normalizer has no nonidentity involution in its conjugation kernel. -/
theorem normalizerConjugation_involution_ne_one (t : linearNormalizer action)
    (ht2 : t * t = 1) (ht : t ≠ 1) : normalizerConjugation t ≠ 1 := by
  intro he
  apply ht
  apply Subtype.ext
  apply Units.ext
  apply centralizing_involution_eq_one
  · exact congrArg (fun x : linearNormalizer action => x.val.val) ht2
  · intro g v
    have hh := normalizerConjugation_action t g v
    rw [he] at hh
    exact hh.symm

/-- Elementary actors retain their original rank under literal conjugation. -/
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


private theorem product_automorphism_cases (f : MulAut (SL × SL)) :
    (∃ a b : MulAut SL, f = a.prodCongr b) ∨
    (∃ a b : MulAut SL, f = a.prodCongr b * (MulEquiv.prodComm : MulAut (SL × SL))) := by
  let : Theory.GroupTheory.IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : Theory.GroupTheory.IsQuasisimple SL :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv alternatingFiveEquiv.symm
  exact Theory.GroupTheory.AutomorphismSquare.normal_form (Theory.PSL2.sl2_center_eq_bot F) f

/-- Every nonidentity involution in the full linear normalizer moves at least
six binary dimensions. All induced factor automorphisms and scalar lifts are covered. -/
theorem normalizer_involution_displacement (t : linearNormalizer action)
    (ht2 : t * t = 1) (ht : t ≠ 1) : 6 ≤ operatorFixedCodim t.val.val := by
  let f := normalizerConjugation t
  have hf2 : f * f = 1 := by dsimp [f]; rw [← map_mul, ht2, map_one]
  have hf : f ≠ 1 := normalizerConjugation_involution_ne_one t ht2 ht
  have hT : ∀ g v, t.val.val (action g v) = action (f g) (t.val.val v) :=
    fun g v => (normalizerConjugation_action t g v).symm
  rcases product_automorphism_cases f with ⟨a, b, hform⟩ | ⟨a, b, hform⟩
  · have ha2 : a * a = 1 := by
      apply MulEquiv.ext
      intro g
      exact congrArg Prod.fst (MulEquiv.congr_fun (show _ from hform ▸ hf2) (g, 1))
    have hb2 : b * b = 1 := by
      apply MulEquiv.ext
      intro g
      exact congrArg Prod.snd (MulEquiv.congr_fun (show _ from hform ▸ hf2) (1, g))
    have hne : a ≠ 1 ∨ b ≠ 1 := by
      by_contra hn
      push Not at hn
      apply hf
      rw [hform, hn.1, hn.2]
      rfl
    have hh := preserving_involution_intertwiner_bound t.val.val
      (LinearMap.GeneralLinearGroup.toLinearEquiv t.val).injective a b ha2 hb2 hne
      (fun g v => by
        have hh := hT g v
        have hfg : f g = (a g.1, b g.2) := by rw [hform]; rfl
        rwa [hfg] at hh)
    omega
  · have hab : a * b = 1 := by
      apply MulEquiv.ext
      intro g
      exact congrArg Prod.fst (MulEquiv.congr_fun (show _ from hform ▸ hf2) (g, 1))
    have hba : b * a = 1 := by
      apply MulEquiv.ext
      intro g
      exact congrArg Prod.snd (MulEquiv.congr_fun (show _ from hform ▸ hf2) (1, g))
    exact swapped_involution_intertwiner_bound t.val.val
      (congrArg (fun x : linearNormalizer action => x.val.val) ht2) a b hab hba
      (fun g v => by
        have hh := hT g v
        have hfg : f g = (a g.2, b g.1) := by rw [hform]; rfl
        rwa [hfg] at hh)

private lemma pair_conj_first {G H : Type*} [Group G] [Group H]
    (r : G × H) (g : G) :
    MulAut.conj r (g, 1) = (r.1 * g * r.1⁻¹, 1) := by
  apply Prod.ext
  · rfl
  · exact (congrArg (fun x => x * r.2⁻¹) (mul_one r.2)).trans (mul_inv_cancel r.2)

private lemma pair_conj_second {G H : Type*} [Group G] [Group H]
    (r : G × H) (g : H) :
    MulAut.conj r (1, g) = (1, r.2 * g * r.2⁻¹) := by
  apply Prod.ext
  · exact (congrArg (fun x => x * r.1⁻¹) (mul_one r.1)).trans (mul_inv_cancel r.1)
  · rfl

/-- A nonidentity inner involution in the full normalizer moves at least eight
binary dimensions. The input is its original operator, with no chosen scalar lift. -/
theorem normalizer_inner_involution_displacement (t : linearNormalizer action)
    (r : SL × SL) (hr2 : r * r = 1) (hr : r ≠ 1)
    (ht : normalizerConjugation t = MulAut.conj r) :
    8 ≤ operatorFixedCodim t.val.val := by
  by_cases h1 : r.1 = 1
  · refine second_inner_intertwiner_bound t.val.val
      (LinearMap.GeneralLinearGroup.toLinearEquiv t.val).injective r.2
      (congrArg Prod.snd hr2) ?_ ?_
    · intro h2
      exact hr (Prod.ext h1 h2)
    · intro g v
      have hh := (normalizerConjugation_action t (1, g) v).symm
      have hfg : normalizerConjugation t (1, g) = (1, r.2 * g * r.2⁻¹) := by
        exact (MulEquiv.congr_fun ht (1, g)).trans (pair_conj_second r g)
      rwa [hfg] at hh
  · refine first_inner_intertwiner_bound t.val.val
      (LinearMap.GeneralLinearGroup.toLinearEquiv t.val).injective r.1
      (congrArg Prod.fst hr2) h1 ?_
    intro g v
    have hh := (normalizerConjugation_action t (g, 1) v).symm
    have hfg : normalizerConjugation t (g, 1) = (r.1 * g * r.1⁻¹, 1) := by
      exact (MulEquiv.congr_fun ht (g, 1)).trans (pair_conj_first r g)
    rwa [hfg] at hh

end Representation.AlternatingFiveMovedPair.Natural

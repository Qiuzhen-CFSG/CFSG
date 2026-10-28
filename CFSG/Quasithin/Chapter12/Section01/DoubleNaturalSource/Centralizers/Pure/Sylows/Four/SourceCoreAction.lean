module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.CaseFour

/-!
# Actual pure-point core action on the natural summand

The literal natural summand lies in the MS commutator core. Its displacement
under the whole join core lies in the original central point line. These
statements follow from the original pure stabilizer projection, with its
surjectivity retained; no classification of the commutator core is used.

The intrinsic two-core of the original point residual acts nontrivially on
the natural summand. This follows from the same surjection with a two-group
kernel and the nontrivial geometric radical of the binary point stabilizer.
These are the original action inputs for a large-distance small-displacement
argument, rather than a centrality assertion about a replacement fixed factor.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

private noncomputable def residualAction (w : componentOrbit V (T : Subgroup G)) :
    B.pointResidual w →* S.setup.stabilizer (Additive.ofMul w) :=
  (S.pureLocalAction w).comp (inclusion
    (le_inf (B.pointResidual_le_normalizer w) ((B.pointResidual_le w).trans inf_le_right)))

private theorem residualAction_surjective
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) : Function.Surjective (residualAction S w) := by
  intro a
  let u : S.setup.natural := ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩
  have ha : a.val ∈ S.setup.residual (Additive.ofMul w) :=
    (S.setup.pure_stabilizer_eq_residual u hw).1 ▸ a.property
  rw [← S.pointResidual_image w] at ha
  obtain ⟨l, hl, he⟩ := ha
  exact ⟨⟨l, mem_map_of_mem _ hl⟩, Subtype.ext he⟩

omit [Finite G] in
private theorem residualAction_kernel_two
    (w : componentOrbit V (T : Subgroup G)) : IsPGroup 2 (residualAction S w).ker := by
  let j : B.pointResidual w →* L := inclusion ((B.pointResidual_le w).trans inf_le_left)
  have hj : (residualAction S w).ker ≤ (pCore 2 L).comap j := by
    intro x hx
    change j x ∈ pCore 2 L
    rw [← B.componentToActionQuotient_ker]
    exact congrArg Subtype.val (show residualAction S w x = 1 from hx)
  exact (pCore_isPGroup.comap_of_injective j
    (inclusion_injective ((B.pointResidual_le w).trans inf_le_left))).to_le hj

include S in
/-- The original natural summand is in the commutator core and has only the
original central point line as displacement under the full join core. -/
theorem pure_natural_msCore_small_displacement
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    let X := B.pointResidual w
    let R := B.pointSylow w
    B.naturalSummand ≤ msQ X R ∧
      ⁅B.naturalSummand, (X ⊔ R).pCoreIn 2⁆ ≤ zpowers (w : G) ∧
      zpowers (w : G) ≤ (X ⊔ R) ⊓ centralizer ((X ⊔ R : Subgroup G) : Set G) ∧
      Nat.card (zpowers (w : G)) = 2 := by
  intro X R
  let W := componentOrbit V (T : Subgroup G)
  let J := X ⊔ R
  have hWR : W ≤ R := by
    intro x hx
    exact ⟨hWT hx, mem_centralizer_singleton_iff.mpr (W.le_centralizer hx w w.property).symm⟩
  have hJC : J ≤ B.localPointCentralizer w := sup_le
    (le_inf (B.pointResidual_le_normalizer w) ((B.pointResidual_le w).trans inf_le_right))
    (inf_le_inf hTM le_rfl)
  have hWQ : W ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 W) (hWR.trans le_sup_right) (hNM.symm ▸ hJC.trans inf_le_left)
  have hNQ : B.naturalSummand ≤ msQ X R := by
    rw [← (S.pure_residual_commutators hNM w hw hp).1]
    exact commutator_mono (B.naturalSummand_le.trans hWQ) le_rfl
  let f : J →* S.setup.stabilizer (Additive.ofMul w) :=
    (S.pureLocalAction w).comp (inclusion hJC)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨x, hx⟩ := residualAction_surjective S w hw hp a
    exact ⟨⟨x, (show X ≤ J from le_sup_left) x.property⟩, hx⟩
  have himage : (pCore 2 J).map f ≤ pCore 2 (S.setup.stabilizer (Additive.ofMul w)) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _ hf, pCore_isPGroup.map _⟩
  refine ⟨hNQ, ?_, ?_, ?_⟩
  · rw [commutator_comm]
    apply commutator_le.mpr
    rintro q ⟨a, ha, rfl⟩ x hx
    let v : W := ⟨x, B.naturalSummand_le hx⟩
    let u : S.setup.natural := ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩
    have hv : Additive.ofMul v ∈ S.setup.natural :=
      (S.natural_marking v).mpr ((B.mem_naturalSummand v).mp hx)
    have hd := S.setup.pure_core_natural_displacement u hw (f a)
      (himage (mem_map_of_mem _ ha)) (Additive.ofMul v) hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd
    change c • Additive.ofMul w = _ at hc
    have hm : ((S.setup.representation (f a).val (Additive.ofMul v) -
        Additive.ofMul v).toMul : G) ∈ zpowers (w : G) := by
      rw [← hc]
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · simp
      · simpa only [one_smul, toMul_ofMul] using mem_zpowers (w : G)
    rw [S.representation_eq] at hm
    simp only [toMul_sub, div_eq_mul_inv] at hm
    exact hm
  · apply zpowers_le.mpr
    refine ⟨(hWR.trans le_sup_right) w.property, ?_⟩
    intro j hj
    exact mem_centralizer_singleton_iff.mp ((hJC.trans inf_le_right) hj)
  · rw [Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ w.property)
      (fun he => hw (Subtype.ext he))

include S in
/-- The intrinsic two-core of the same original residual does not fix the
natural summand pointwise. -/
theorem pure_residual_core_moves_natural
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    ¬ B.naturalSummand ≤ centralizer ((B.pointResidual w).pCoreIn 2 : Set G) := by
  intro hc
  let u : S.setup.natural := ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩
  let x := S.setup.naturalCoordinates u
  have hx := S.setup.naturalCoordinates_ne_zero u hw
  let f := residualAction S w
  have hf := residualAction_surjective S w hw hp
  have hk := residualAction_kernel_two S w
  let e := S.setup.purePointEquiv u hw
  have hmap : (pCore 2 (B.pointResidual w)).map f = pCore 2 (S.setup.stabilizer (Additive.ofMul w)) := by
    rw [← f.comap_pCore_of_ker_isPGroup hf hk, map_comap_eq_self_of_surjective hf]
  have hzero : pCore 2 (BinaryNaturalDual.VectorStabilizers.Pure.pointStabilizer x) = ⊥ := by
    apply bot_unique
    intro a ha
    rw [← pCore_map_iso 2 e] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rw [← hmap] at hb
    obtain ⟨l, hl, rfl⟩ := hb
    apply mem_bot.mpr
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change (S.setup.purePointEquiv u hw (f l)).val v = v
    have he := S.setup.pure_natural_action u hw (f l) v
    have hv : (S.setup.naturalEmbedding v).toMul.val ∈ B.naturalSummand :=
      (B.mem_naturalSummand _).mpr ((S.natural_marking _).mp
        (S.setup.naturalCoordinates.symm v).property)
    have hfix : S.setup.representation (f l).val (S.setup.naturalEmbedding v) =
        S.setup.naturalEmbedding v := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [S.representation_eq]
      change (l : G) * ((S.setup.naturalEmbedding v).toMul : G) * (l : G)⁻¹ = _
      rw [hc hv (l : G) (mem_map_of_mem _ hl), mul_inv_cancel_right]
    rw [hfix] at he
    have he' := congrArg (fun z => (S.setup.model.coordinates z).1) he
    simpa only [S.setup.naturalEmbedding_coordinates] using he'.symm
  have hcard := BinaryNaturalDual.VectorStabilizers.Pure.pointKernel_card hx
  rw [← BinaryNaturalDual.VectorStabilizers.Pure.point_twoCore, hzero] at hcard
  have hn := B.degree
  simp only [BinaryLinear.OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin,
    Subgroup.card_bot] at hcard
  rcases hn with rfl | rfl <;> norm_num at hcard

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

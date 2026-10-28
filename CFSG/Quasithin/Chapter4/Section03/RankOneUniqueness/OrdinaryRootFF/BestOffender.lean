module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.Offender
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The marked full-module image is a best offender

An element of the plane radical outside the point radical has the same
centralizer in the point radical as the full plane radical. This is a direct
calculation in the original symplectic marking. The fixed-factor identity
Q = R C_Q(W) extends it to Q, so every nontrivial subgroup of W's actual
image fixes exactly C_U(W). The offender inequality and monotonicity of
subgroup order then show that the whole W-image is a best offender.

Source: Aschbacher–Smith 4.3.6, printed p.615, the FF* claim after (**).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise Matrix
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

private theorem plane_point_commute {F : Type*} [Field F] [CharP F 2]
    (w : Sp F) (hw : w ∈ planeRadicalAmbient) (hwn : w ∉ pointRadicalAmbient)
    (r : Sp F) (hr : r ∈ pointRadicalAmbient) (hc : Commute r w) :
    r ∈ planeRadicalAmbient := by
  obtain ⟨w, hw, rfl⟩ := hw
  obtain ⟨r, hr, rfl⟩ := hr
  let B := (Plane.radicalEquiv (⟨w,hw⟩ : Plane.radical)).toAdd
  have hwB : w = Plane.shear B :=
    congrArg Subtype.val (Plane.radicalEquiv.symm_apply_apply (⟨w,hw⟩ : Plane.radical)).symm
  have hsym : B.val 1 0 = B.val 0 1 := congrFun (congrFun B.property 0) 1
  have hB : B.val 1 1 ≠ 0 := by
    intro hz
    apply hwn
    refine ⟨pointRadicalElement (B.val 0 1) 0 (B.val 0 0), pointRadicalElement_mem _ _ _, ?_⟩
    rw [hwB]
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [pointRadicalElement, pointRadicalMatrix, Plane.shear, Plane.shearSp,
        Matrix.fromBlocks, hsym, hz]
  obtain ⟨u,v,z,he⟩ : ∃ u v z, r = pointRadicalElement u v z :=
    ⟨_,_,_,pointRadical_eq_element r hr⟩
  have hv : v = 0 := by
    have hm := congrArg (fun g : Sp F => g.val (.inl 0) (.inr 1)) hc.eq
    rw [hwB,he] at hm
    change (pointRadicalMatrix u v z * (Plane.shearSp B).val) (.inl 0) (.inr 1) =
      ((Plane.shearSp B).val * pointRadicalMatrix u v z) (.inl 0) (.inr 1) at hm
    simp [pointRadicalMatrix, Plane.shearSp, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two] at hm
    have hp : v * B.val 1 1 = 0 := by linear_combination hm
    exact (mul_eq_zero.mp hp).resolve_right hB
  subst v
  let C : Plane.symmetricMatrices F := ⟨!![z,u;u,0], by
    ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  refine ⟨Plane.shear C, Plane.quotientMap_shear C, ?_⟩
  rw [he]
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [C, pointRadicalElement, pointRadicalMatrix, Plane.shear, Plane.shearSp, Matrix.fromBlocks]

omit [Finite G] in
theorem fullModule_point_centralizer (hn : 1 < n)
    (w : G) (hw : w ∈ c.ordinaryModule) (hwn : w ∉ m.second.pCoreIn 2)
    (r : G) (hr : r ∈ m.second.pCoreIn 2) (hc : Commute r w) : r ∈ c.ordinaryModule := by
  obtain ⟨w',hw',hew⟩ := (m.planeRadical_image hn).ge hw
  obtain ⟨r',hr',her⟩ := (m.pointRadical_image hn).ge hr
  have hwr : w' ∉ pointRadicalAmbient := fun h => hwn
    (hew ▸ (m.pointRadical_image hn).le (mem_map_of_mem _ h))
  have hc' : Commute r' w' := by
    apply m.modelEmbedding_injective
    simpa only [map_mul,hew,her] using hc.eq
  exact her ▸ (m.planeRadical_image hn).le
    (mem_map_of_mem _ (plane_point_commute w' hw' hwr r' hr' hc'))

omit [Finite G] in
theorem core_centralizer_of_fullModule_element (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m)) (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (w : G) (hw : w ∈ c.ordinaryModule) (hwn : w ∉ m.second.pCoreIn 2)
    (q : G) (hq : q ∈ m.rootCore) (hc : Commute q w) :
    q ∈ centralizer (c.ordinaryModule : Set G) := by
  let R := m.second.pCoreIn 2
  let C := m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)
  have hnC : C ≤ normalizer (R : Set G) := inf_le_left.trans
    (((core_centralizes_span m hr hUN).trans (centralizer_le hcore)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hp : q ∈ (R : Set G) * (C : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left R C hnC, ← hQ]
    exact hq
  obtain ⟨r,hr',d,hd,rfl⟩ := hp
  have hrw : Commute r w := by
    apply mul_right_cancel (b := d)
    calc
      (r*w)*d = (r*d)*w := by rw [mul_assoc,hd.2 w hw,← mul_assoc]
      _ = w*(r*d) := hc.eq
      _ = (w*r)*d := (mul_assoc _ _ _).symm
  have hrW := fullModule_point_centralizer m hn w hw hwn r hr' hrw
  let := fullModule_elementary m hn
  have hrC : r ∈ centralizer (c.ordinaryModule : Set G) := by
    intro a ha
    exact congrArg Subtype.val (mul_comm (⟨a,ha⟩ : c.ordinaryModule) ⟨r,hrW⟩)
  exact (centralizer (c.ordinaryModule : Set G)).mul_mem hrC hd.2

omit [Finite G] in
theorem fullModule_fixedSpace_eq (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m)) (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (B : Subgroup (Actor m)) (hB : B ≤ image m c.ordinaryModule) (hne : B ≠ ⊥) :
    letI := hr.elementary
    fixedSpace (representation m hr) B = fixedSpace (representation m hr) (image m c.ordinaryModule) := by
  let := hr.elementary
  obtain ⟨b,hb,hbne⟩ := B.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨w,hw,hew⟩ := hB hb
  have hwn : (w : G) ∉ m.second.pCoreIn 2 := by
    intro hwR
    have hm : projection m w ∈ image m m.rootCore := mem_map_of_mem _
      (hcore.trans (span_le_core m hr hUN) hwR)
    rw [core_image_eq_bot m hr,mem_bot,hew] at hm
    exact hbne hm
  apply le_antisymm
  · intro v hv
    have he : representation m hr (projection m w) v = v := by
      rw [hew]
      exact hv ⟨b,hb⟩
    have hcomm := congrArg (fun x : Additive (moduleSubgroup m) => (x.toMul.val : G)) he
    rw [representation_apply m hr] at hcomm
    have huC := core_centralizer_of_fullModule_element m hn hr hUN hcore hQ w hw hwn
      v.toMul.val (span_le_core m hr hUN v.toMul.property)
      (mul_inv_eq_iff_eq_mul.mp hcomm).symm
    apply (Representation.NormalElementaryQuotient.mem_fixedSpace_image
      (moduleSubgroup m) (projection m) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) (c.ordinaryModule.subgroupOf m.rootNormalizer) v).mpr
    intro a ha
    exact Subtype.ext (huC a ha)
  · intro v hv b'
    exact hv ⟨b',hB b'.property⟩

theorem fullModule_isBestOffender (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m)) (hUN : m.rootSpan ≤ m.rootNormalizer)
    (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G))) :
    letI := hr.elementary
    IsBestOffender (representation m hr) (image m c.ordinaryModule) := by
  let := hr.elementary
  have hoff := fullModule_isOffender m hn hr hUN hcore hQ
  refine ⟨hoff.1, ?_⟩
  intro B hB
  by_cases hb : B = ⊥
  · rw [hb,weight_bot]
    exact (fixedCodim_le_rank_iff _ _).mp hoff.2
  · unfold weight
    rw [fullModule_fixedSpace_eq m hn hr hUN hcore hQ B hB hb]
    apply Nat.add_le_add_right
    exact Nat.log_mono_right (Nat.card_le_card_of_injective (inclusion hB) (inclusion_injective hB))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF

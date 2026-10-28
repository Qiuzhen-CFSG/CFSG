module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.Quotient
public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions
public import Theory.SpecificGroups.BinaryLinear.PointStabilizerRank
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
public import Theory.Quasithin.EvenCharacteristic

/-!
# Moved-point stabilizers in a Mathieu 2A centralizer

The elementary order-sixteen octad kernel acts freely on the sixteen points
outside the octad: each nonidentity kernel element is a 2A involution, and its
eight fixed points already include the octad. Cardinality then gives regularity.
Correcting a lift by a kernel element identifies a moved-point stabilizer in the
full centralizer with the stabilizer of a nonzero vector in GL4(2). The latter
is a proper binary parabolic and has self-centralizing two-core.

Conjugation transports the conclusion to every 2A involution and every moved
point in the original degree-24 action. This is the geometric input to the
eight-fixed-point M22 outer-centralizer row of Aschbacher–Smith 16.1.5(5),
printed p.1171 of `refs/quasithin.pdf`.
-/

public section

open Subgroup
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers
open MathieuCode
open scoped Pointwise

namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA

private theorem translation_fixes_octad (u : translationKernel) (a : Fin 24)
    (ha : a ∈ fixedOctad.val) : u.val.val • a = a := by
  have hu : toOctad u.val ∈ OctadAction.Core fixedOctad := u.property
  rw [OctadAction.Core, CocodeOctad.core_eq_coordinateKernel,
    CocodeOctad.mem_coordinateAction_ker] at hu
  exact hu a ha

private theorem translation_fixedPoints (u : translationKernel) (hu : u ≠ 1) :
    M24ChapterHStabilizers.fixedPoints u.val.val = fixedOctad.val := by
  have hs : u ^ 2 = 1 := by
    apply translationCoordinates.injective
    rw [map_pow, map_one, pow_two]
    change (translationCoordinates u).toAdd + (translationCoordinates u).toAdd = 0
    ext i
    exact (by decide : ∀ x : ZMod 2, x + x = 0) _
  have ho : orderOf u.val.val = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact orderOf_eq_prime hs hu
  have hle : fixedOctad.val ⊆ M24ChapterHStabilizers.fixedPoints u.val.val := by
    intro a ha
    exact (M24ChapterHStabilizers.mem_fixedPoints _ _).mpr (translation_fixes_octad u a ha)
  rcases involution_classes u.val.val ho with hA | hB
  · symm
    apply Finset.eq_of_subset_of_card_le hle
    rw [m24Blocks_card _ (class2A_fixed_octad hA), m24Blocks_card _ fixedOctad.property]
  · have he := class2B_fixed_empty hB
    have hcard := Finset.card_le_card hle
    rw [he, Finset.card_empty, m24Blocks_card _ fixedOctad.property] at hcard
    omega

private theorem translation_free {a : Fin 24} (ha : a ∉ fixedOctad.val)
    (u : translationKernel) (hu : u.val.val • a = a) : u = 1 := by
  by_contra hne
  exact ha ((translation_fixedPoints u hne) ▸
    (M24ChapterHStabilizers.mem_fixedPoints _ _).mpr hu)

private theorem translation_transitive {a b : Fin 24}
    (ha : a ∉ fixedOctad.val) (hb : b ∉ fixedOctad.val) :
    ∃ u : translationKernel, u.val.val • a = b := by
  classical
  let f : translationKernel → {i : Fin 24 // i ∉ fixedOctad.val} := fun u =>
    ⟨u.val.val • a, by
      intro h
      have hf := translation_fixes_octad u⁻¹ _ h
      change u.val.val⁻¹ • (u.val.val • a) = u.val.val • a at hf
      rw [inv_smul_smul] at hf
      exact ha (hf.symm ▸ h)⟩
  have hi : Function.Injective f := by
    intro u v huv
    have he : (v⁻¹ * u).val.val • a = a := by
      change (v.val.val⁻¹ * u.val.val) • a = a
      rw [mul_smul, show u.val.val • a = v.val.val • a from congrArg Subtype.val huv,
        inv_smul_smul]
    exact (inv_mul_eq_one.mp (translation_free ha _ he)).symm
  have hc : Nat.card {i : Fin 24 // i ∉ fixedOctad.val} = Nat.card translationKernel := by
    rw [translationKernel_card, Nat.card_eq_fintype_card]
    change Fintype.card {i : Fin 24 // i ∈ fixedOctad.valᶜ} = 16
    rw [Fintype.card_coe, Finset.card_compl, m24Blocks_card _ fixedOctad.property]
    rfl
  obtain ⟨u, hu⟩ := (hi.bijective_of_nat_card_le hc.le).surjective ⟨b, hb⟩
  exact ⟨u, congrArg Subtype.val hu⟩

private noncomputable def pointedAction (a : Fin 24) :
    MulAction.stabilizer centralizer2A a →*
      Theory.LinearAlgebra.BinaryFivePointStabilizer.stabilizer markedVector :=
  pointAction.comp (MulAction.stabilizer centralizer2A a).subtype

private theorem pointedAction_bijective (a : Fin 24) (ha : a ∉ fixedOctad.val) :
    Function.Bijective (pointedAction a) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro g hg
    have hk : g.val ∈ translationKernel := by
      rw [← pointAction_ker]
      exact hg
    have he := translation_free ha (⟨g.val, hk⟩ : translationKernel) g.property
    exact Subtype.ext (congrArg (fun q : translationKernel => q.val) he)
  · intro q
    obtain ⟨g, rfl⟩ := pointAction_surjective q
    have hga : g.val • a ∉ fixedOctad.val := by
      intro h
      apply ha
      have hstab := centralizer_le_octad ((centralizer2A).inv_mem g.property)
      have he := MulAction.mem_stabilizer_finset'.mp hstab h
      simpa only [inv_smul_smul] using he
    obtain ⟨u, hu⟩ := translation_transitive hga ha
    refine ⟨⟨u.val * g, hu⟩, ?_⟩
    change pointAction (u.val * g) = pointAction g
    rw [map_mul, show pointAction u.val = 1 from
      (pointAction_ker.symm ▸ u.property : u.val ∈ pointAction.ker), one_mul]

private noncomputable def pointedEquiv (a : Fin 24) (ha : a ∉ fixedOctad.val) :
    MulAction.stabilizer centralizer2A a ≃*
      Theory.LinearAlgebra.BinaryFivePointStabilizer.stabilizer markedVector :=
  MulEquiv.ofBijective (pointedAction a) (pointedAction_bijective a ha)

/-- A moved-point stabilizer in the marked 2A centralizer has characteristic two. -/
theorem pointed_twoCore (a : Fin 24) (ha : a ∉ fixedOctad.val) :
    centralizer (pCore 2 (MulAction.stabilizer centralizer2A a) :
      Set (MulAction.stabilizer centralizer2A a)) ≤
      pCore 2 (MulAction.stabilizer centralizer2A a) := by
  apply (Theory.Quasithin.centralizer_pCore_le_iff 2 (pointedEquiv a ha)).mpr
  change centralizer (pCore 2 (MulAction.stabilizer (BinaryLinear.GL OctadAction.Space)
    markedVector) : Set (MulAction.stabilizer (BinaryLinear.GL OctadAction.Space)
    markedVector)) ≤ pCore 2 (MulAction.stabilizer (BinaryLinear.GL OctadAction.Space) markedVector)
  rw [BinaryLinear.PointStabilizerRank.stabilizer_eq_parabolic]
  apply BinaryLinear.centralizer_parabolic_twoCore_le
  · exact mt Submodule.span_singleton_eq_bot.mp markedVector_ne_zero
  · intro he
    have hd : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {markedVector}) = 1 :=
      finrank_span_singleton markedVector_ne_zero
    rw [he, finrank_top, Module.finrank_pi, Fintype.card_fin] at hd
    norm_num at hd

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA

namespace Sporadic.Mathieu.M24InvolutionCentralizers

private noncomputable def pointedConjEquiv (g x y : M24) (a b : Fin 24)
    (hxy : MulAut.conj g x = y) (hab : g • a = b) :
    MulAction.stabilizer (centralizer ({x} : Set M24)) a ≃*
      MulAction.stabilizer (centralizer ({y} : Set M24)) b where
  toFun u := ⟨⟨MulAut.conj g u.val.val, by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hxy, ← map_mul, ← map_mul]
    exact congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp u.val.property)⟩, by
      change (g * u.val.val * g⁻¹) • b = b
      rw [← hab, mul_smul, inv_smul_smul, mul_smul,
        show u.val.val • a = a from u.property]⟩
  invFun u := ⟨⟨(MulAut.conj g).symm u.val.val, by
    apply mem_centralizer_singleton_iff.mpr
    apply (MulAut.conj g).injective
    simpa only [map_mul, MulEquiv.apply_symm_apply, hxy] using
      mem_centralizer_singleton_iff.mp u.val.property⟩, by
      apply (MulAction.toPerm g).injective
      change g • (((MulAut.conj g).symm u.val.val) • a) = g • a
      have hpre : (MulAut.conj g).symm u.val.val = g⁻¹ * u.val.val * g := by rfl
      rw [hpre, mul_smul, mul_smul, smul_inv_smul, hab]
      exact u.property⟩
  left_inv u := Subtype.ext (Subtype.ext ((MulAut.conj g).symm_apply_apply u.val.val))
  right_inv u := Subtype.ext (Subtype.ext ((MulAut.conj g).apply_symm_apply u.val.val))
  map_mul' u v := Subtype.ext (Subtype.ext ((MulAut.conj g).map_mul u.val.val v.val.val))

/-- The same two-core conclusion holds for every conjugate and every moved point. -/
theorem pointed_twoCore_of_class2A (x : M24) (hx : IsConj involution2A x)
    (a : Fin 24) (ha : x • a ≠ a) :
    centralizer (pCore 2 (MulAction.stabilizer (centralizer ({x} : Set M24)) a) :
      Set (MulAction.stabilizer (centralizer ({x} : Set M24)) a)) ≤
      pCore 2 (MulAction.stabilizer (centralizer ({x} : Set M24)) a) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  have hb : g⁻¹ • a ∉ TwoA.fixedOctad.val := by
    intro hb
    apply ha
    have hfix := (TwoA.fixed_iff _).mpr hb
    rw [← hg, mul_smul, mul_smul, hfix, smul_inv_smul]
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (pointedConjEquiv g involution2A x (g⁻¹ • a) a hg (smul_inv_smul g a))).mp
      (TwoA.pointed_twoCore _ hb)

end Sporadic.Mathieu.M24InvolutionCentralizers

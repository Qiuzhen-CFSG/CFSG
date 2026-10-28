module
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoLocalOrders
public import Theory.SpecificGroups.SL2.BinaryThreeSection
public import Theory.GroupTheory.PCoreImage

/-!
# No binary-three quotient in a Ree two-local subgroup

A perfect actor in the full linear parabolic has trivial projection to
its complementary field torus. The remaining SL₂ projection has two-group
kernel, so it cannot preserve the order-four section in SL₃(2). The Suzuki
parabolic is three-free. Normalizer coverage applies these two obstructions
to the actual intrinsic two-core of a perfect subgroup.

Source: Aschbacher--Smith A.3.12 and 10.2.9, printed pp.47--48,750--751;
the native parabolics and normalizer coverage use GLS3 §§2.6,3.1.
The point-control consumer is RankTwo.BinaryThree.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace ReeF4.ConverseParabolics

/-- A perfect group mapping through a two-group kernel to a Ree linear
parabolic cannot have an SL₃(2) quotient. -/
theorem no_binary_three_quotient_in_linear_parabolic
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (π : A →* SL(3,ZMod 2)) (hπ : Function.Surjective π)
    {m : ℕ} (hm : 1 ≤ m)
    (f : A →* parabolic m .linear) (hf : IsPGroup 2 f.ker) : False := by
  let g := (linearProjection hm).comp f
  have hg : IsPGroup 2 g.ker :=
    (linearProjection_ker_isPGroup hm).comap_of_ker_isPGroup f hf
  let χ := (MonoidHom.snd SL(2,CoefficientField m) (CoefficientField m)ˣ).comp g
  let : Group.IsPerfect χ.range := Group.IsPerfect.range χ
  let : Subsingleton χ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  have hχ (a : A) : χ a = 1 :=
    congrArg Subtype.val (Subsingleton.elim (χ.rangeRestrict a) 1)
  let r := (MonoidHom.fst SL(2,CoefficientField m) (CoefficientField m)ˣ).comp g
  apply Matrix.SpecialLinearGroup.no_binary_three_quotient_of_two_kernel π hπ r
  have hr : r.ker = g.ker := by
    ext a
    constructor
    · intro ha
      exact Prod.ext ha (hχ a)
    · intro ha
      exact congrArg Prod.fst ha
  rwa [hr]

/-- The Suzuki parabolic is three-free; the linear parabolic has the
binary rank-one obstruction. Both use the literal parabolic inclusion. -/
theorem no_binary_three_quotient_in_parabolic
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (π : A →* SL(3,ZMod 2)) (hπ : Function.Surjective π)
    {m : ℕ} (hm : 1 ≤ m) (s : LargeLocalSeeds.Side)
    (f : A →* parabolic m s) (hf : Function.Injective f) : False := by
  cases s with
  | linear =>
    apply no_binary_three_quotient_in_linear_parabolic π hπ hm f
    rw [f.ker_eq_bot_iff.mpr hf]
    exact IsPGroup.of_card (n := 0) (by simp)
  | suzuki =>
    apply suzuki_parabolic_three_free hm
    have hd := Subgroup.card_dvd_of_surjective π hπ
    rw [Matrix.PSL3Two.card_SL] at hd
    exact (by decide : 3 ∣ 168).trans
      (hd.trans (Subgroup.card_dvd_of_injective f hf))

/-- A perfect subgroup with nontrivial two-core cannot have binary-three
quotient in any large Ree carrier. -/
theorem not_binary_three_core_quotient
    {m : ℕ} (hm : 1 ≤ m) (B : Subgroup (Model m)) [Group.IsPerfect B]
    (hcore : pCore 2 B ≠ ⊥) (e : (B ⧸ pCore 2 B) ≃* SL(3,ZMod 2)) : False := by
  let R := (pCore 2 B).map B.subtype
  have hR : R ≠ ⊥ := fun hz => hcore
    ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp hz)
  have hBN : B ≤ normalizer (R : Set (Model m)) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  obtain ⟨g,s,hg⟩ := normalizer_cover hm R hR (pCore_isPGroup.map B.subtype)
  let a := MulAut.conj g
  have hBP : B.map a.toMonoidHom ≤ parabolic m s := (map_mono hBN).trans hg
  let f : B →* parabolic m s := (a.toMonoidHom.comp B.subtype).codRestrict _
    (fun b => hBP (mem_map_of_mem a.toMonoidHom b.property))
  have hf : Function.Injective f := fun b c h => Subtype.ext
    (a.injective (congrArg Subtype.val h))
  exact no_binary_three_quotient_in_parabolic
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hm s f hf

end ReeF4.ConverseParabolics

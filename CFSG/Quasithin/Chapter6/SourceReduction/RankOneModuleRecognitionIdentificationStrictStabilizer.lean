module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictDisplacement
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Uniqueness of the strict moved-plane involution

For a nondegenerate binary alternating form B, an operator D with
B(Dx,x)=0 and image a plane is determined by that plane. Its kernel is
the orthogonal complement of the image. The induced alternating form on
the two-dimensional quotient is the unique nonzero alternating form
there over the binary field.

Apply this to the displacement of the actual layer involution and to
its conjugates. The setwise stabilizer of its moved plane is exactly
its centralizer. This uses the faithful dotted representation and the
type-a₂ calculation, without a model classification.

Source: Aschbacher--Smith, the first assertion in the proof of 6.2.16(5),
printed p.689. The ambient normalizer lift and nontransitivity are the
subsequent steps of the same strict-branch task.
-/

public noncomputable section
open Module
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem plane_alt_zero {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hd : finrank (ZMod 2) W = 2)
    (B : LinearMap.BilinForm (ZMod 2) W) (ha : B.IsAlt)
    (hz : B (finBasisOfFinrankEq (ZMod 2) W hd 0)
      (finBasisOfFinrankEq (ZMod 2) W hd 1) = 0) : B = 0 := by
  let e := finBasisOfFinrankEq (ZMod 2) W hd
  apply LinearMap.BilinForm.ext_iff.mpr
  intro x y
  rw [← e.sum_repr x, ← e.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have hq : B (e 0) (e 1) = 0 := hz
  have hr : B (e 1) (e 0) = 0 := by
    rw [← neg_eq_zero, ← ha.neg_eq]
    simpa using hq
  simp [ha.self_eq_zero, hq, hr]

private theorem plane_alt_unique {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hd : finrank (ZMod 2) W = 2)
    (B C : LinearMap.BilinForm (ZMod 2) W) (hB : B.IsAlt) (hC : C.IsAlt)
    (hb : B ≠ 0) (hc : C ≠ 0) : B = C := by
  let e := finBasisOfFinrankEq (ZMod 2) W hd
  have hbe : B (e 0) (e 1) ≠ 0 := fun h => hb (plane_alt_zero hd B hB h)
  have hce : C (e 0) (e 1) ≠ 0 := fun h => hc (plane_alt_zero hd C hC h)
  have he : B (e 0) (e 1) = C (e 0) (e 1) := by
    exact (by decide : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a = b) _ _ hbe hce
  apply sub_eq_zero.mp
  apply plane_alt_zero hd (B-C) (hB.sub hC)
  exact sub_eq_zero.mpr he

private theorem same_range_alt_operator {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (B : LinearMap.BilinForm (ZMod 2) W)
    (hBn : B.Nondegenerate) (D E : W →ₗ[ZMod 2] W)
    (hD : (B.comp D LinearMap.id).IsAlt) (hE : (B.comp E LinearMap.id).IsAlt)
    (hd : finrank (ZMod 2) D.range = 2) (hr : D.range = E.range) : D = E := by
  let C := B.comp D LinearMap.id
  let F := B.comp E LinearMap.id
  have hker (X : W →ₗ[ZMod 2] W) : (B.comp X LinearMap.id).ker = X.ker := by
    ext x
    constructor
    · intro hx
      exact hBn.1 (X x) (fun y => LinearMap.congr_fun hx y)
    · intro hx
      apply LinearMap.ext
      intro y
      change B (X x) y = 0
      rw [show X x = 0 from hx, map_zero]
      rfl
  have hk : D.ker = E.ker := by
    have ho (X : W →ₗ[ZMod 2] W) (ha : (B.comp X LinearMap.id).IsAlt) :
        X.ker = B.orthogonal X.range := by
      ext x
      constructor
      · intro hx y hy
        obtain ⟨w, rfl⟩ := hy
        exact ha.isRefl x w (by change B (X x) w = 0; rw [show X x = 0 from hx, map_zero]; rfl)
      · intro hx
        apply hBn.1 (X x)
        intro y
        exact ha.isRefl y x (hx (X y) ⟨y, rfl⟩)
    rw [ho D hD, ho E hE, hr]
  have hdc : D.ker ≤ C.ker := (hker D).ge
  have hef : D.ker ≤ F.ker := hk.trans (hker E).symm |>.le
  have hdc' : D.ker ≤ C.flip.ker := hD.isRefl.ker_flip ▸ hdc
  have hef' : D.ker ≤ F.flip.ker := hE.isRefl.ker_flip ▸ hef
  let Cq := LinearMap.liftQ₂ D.ker D.ker C hdc hdc'
  let Fq := LinearMap.liftQ₂ D.ker D.ker F hef hef'
  have hdq : finrank (ZMod 2) (W ⧸ D.ker) = 2 := by
    have hq := Submodule.finrank_quotient_add_finrank D.ker
    have hn := D.finrank_range_add_finrank_ker
    omega
  have haq (X : LinearMap.BilinForm (ZMod 2) W) (ha : X.IsAlt)
      (hx : D.ker ≤ X.ker) (hx' : D.ker ≤ X.flip.ker) :
      (LinearMap.liftQ₂ D.ker D.ker X hx hx').IsAlt := by
    intro x
    refine Submodule.Quotient.induction_on D.ker x ?_
    intro w
    exact ha w
  have hnq (X : W →ₗ[ZMod 2] W) (hx : D.ker ≤ (B.comp X LinearMap.id).ker)
      (hx' : D.ker ≤ (B.comp X LinearMap.id).flip.ker)
      (hxr : finrank (ZMod 2) X.range = 2) :
      LinearMap.liftQ₂ D.ker D.ker (B.comp X LinearMap.id) hx hx' ≠ 0 := by
    intro hz
    have hx0 : X = 0 := by
      apply LinearMap.ext
      intro w
      apply hBn.1 (X w)
      intro y
      exact congrArg (fun Q : LinearMap.BilinForm (ZMod 2) (W ⧸ D.ker) =>
        Q (Submodule.Quotient.mk w) (Submodule.Quotient.mk y)) hz
    rw [hx0, LinearMap.range_zero, finrank_bot] at hxr
    omega
  have heq : Cq = Fq := plane_alt_unique hdq Cq Fq (haq C hD hdc hdc')
    (haq F hE hef hef') (hnq D hdc hdc' hd) (hnq E hef hef' (hr ▸ hd))
  apply LinearMap.ext
  intro x
  apply sub_eq_zero.mp
  apply hBn.1 (D x - E x)
  intro y
  have hh := congrArg (fun Q : LinearMap.BilinForm (ZMod 2) (W ⧸ D.ker) =>
    Q (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)) heq
  change B (D x) y = B (E x) y at hh
  rw [map_sub, LinearMap.sub_apply, hh, sub_self]

private theorem rank_two_stabilizer_iff_commute
    {W A : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Group A]
    (ρ : Representation (ZMod 2) A W) (hf : Function.Injective ρ)
    (B : LinearMap.BilinForm (ZMod 2) W) (hBa : B.IsAlt) (hBn : B.Nondegenerate)
    (hpres : ∀ a x y, B (ρ a x) (ρ a y) = B x y)
    (a : A) (hd : finrank (ZMod 2) (Representation.RankTwo.movedSpace ρ a) = 2)
    (ha : ∀ x, B x (ρ a x) = 0) (b : A) :
    (∀ x, x ∈ Representation.RankTwo.movedSpace ρ a ↔
      ρ b x ∈ Representation.RankTwo.movedSpace ρ a) ↔ Commute b a := by
  constructor
  · intro hb
    let c := b * a * b⁻¹
    have hinv (x : W) : ρ b (ρ b⁻¹ x) = x := by
      simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have hinv' (x : W) : ρ b⁻¹ (ρ b x) = x := by
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hc (x : W) : ρ c (ρ b x) = ρ b (ρ a x) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 1
      dsimp [c]
      group
    have hmove (x : W) : ρ c x - x = ρ b (ρ a (ρ b⁻¹ x) - ρ b⁻¹ x) := by
      rw [map_sub, hinv, ← hc, hinv]
    have hr : Representation.RankTwo.movedSpace ρ a =
        Representation.RankTwo.movedSpace ρ c := by
      ext w
      constructor
      · intro hw
        have hi : ρ b⁻¹ w ∈ Representation.RankTwo.movedSpace ρ a :=
          (hb (ρ b⁻¹ w)).mpr (by simpa only [hinv] using hw)
        obtain ⟨x, hx⟩ := hi
        refine ⟨ρ b x, ?_⟩
        change ρ c (ρ b x) - ρ b x = w
        rw [hc, ← map_sub]
        change ρ a x - x = ρ b⁻¹ w at hx
        rw [hx, hinv]
      · rintro ⟨x, rfl⟩
        change ρ c x - x ∈ Representation.RankTwo.movedSpace ρ a
        rw [hmove]
        apply (hb _).mp
        exact ⟨ρ b⁻¹ x, rfl⟩
    have hca : ∀ x, B x (ρ c x) = 0 := by
      intro x
      have hh := hpres b (ρ b⁻¹ x) (ρ a (ρ b⁻¹ x))
      rw [hinv, ← hc, hinv, ha] at hh
      exact hh
    have halt (t : A) (ht : ∀ x, B x (ρ t x) = 0) :
        (B.comp (ρ t - 1) LinearMap.id).IsAlt := by
      intro x
      change B (ρ t x - x) x = 0
      rw [map_sub, LinearMap.sub_apply, hBa.self_eq_zero, sub_zero]
      exact hBa.eq_iff.mpr (ht x)
    have he := same_range_alt_operator B hBn (ρ a - 1) (ρ c - 1)
      (halt a ha) (halt c hca) hd hr
    have hac : a = c := hf (sub_left_injective he)
    change b * a = a * b
    calc
      b * a = c * b := by dsimp [c]; group
      _ = a * b := congrArg (· * b) hac.symm
  · intro hb
    exact Representation.RankTwo.mem_movedSpace_map_iff_of_commute ρ hb

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}
  [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]

/-- On the actual central quotient, the moved-plane stabilizer is the
centralizer of the unique nonidentity layer image. -/
theorem LocalAnalysis.strict_plane_stabilizer_iff_commute
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    (a : StrictActor (T : Subgroup G) L R z)
    (ha : a ∈ strictLayerImage (T : Subgroup G) L R z) (hane : a ≠ 1)
    (b : StrictActor (T : Subgroup G) L R z) :
    (∀ x, x ∈ strictCentralPlane (T : Subgroup G) L R z ↔
      strictRepresentation (T : Subgroup G) L R z b x ∈ strictCentralPlane (T : Subgroup G) L R z) ↔
      Commute b a := by
  obtain ⟨he, B, hBa, hBn, _, hpres, hmark⟩ :=
    A.strict_symplectic_layer_action h611 hnatural hz horder hstrict
  obtain ⟨_, hplane, hd, htype⟩ := hmark a ha hane
  rw [← hplane]
  exact rank_two_stabilizer_iff_commute _ (strictRepresentation_injective _ _ _ _)
    B hBa hBn hpres a hd htype b

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

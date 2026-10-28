module
public import Theory.GroupTheory.SolvableResidual.PrimeTo
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Generation by residuals across a solvable kernel

Suppose two subgroups generate a perfect group and share a solvable
supplement to their solvable residuals. The supplement normalizes the join
of those residuals. That join is therefore normal, and its quotient is a
solvable image of the supplement; perfectness makes the quotient trivial.

Full preimages under a surjection with solvable kernel preserve these
hypotheses. In particular, the kernel need not be central. This is the
lifting step for the higher-field parabolic residuals in Aschbacher--Smith,
15.1.20(2), printed p.1095.
-/

public section
open Subgroup
namespace Subgroup
variable {X Y : Type*} [Group X] [Group Y] [Finite X]

omit [Finite X] in
theorem residuals_sup_eq_top_of_common_solvable_supplement [Group.IsPerfect X]
    (P Q B : Subgroup X) [Group.IsSolvable B]
    (hBP : B ≤ P) (hBQ : B ≤ Q) (hgen : P ⊔ Q = ⊤)
    (hP : (solvableResidual P).map P.subtype ⊔ B = P)
    (hQ : (solvableResidual Q).map Q.subtype ⊔ B = Q) :
    (solvableResidual P).map P.subtype ⊔ (solvableResidual Q).map Q.subtype = ⊤ := by
  let R := (solvableResidual P).map P.subtype ⊔ (solvableResidual Q).map Q.subtype
  have hB : B ≤ normalizer (R : Set X) :=
    (le_inf
      ((hBP.trans P.le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image P (solvableResidual P)))
      ((hBQ.trans Q.le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image Q (solvableResidual Q)))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hRB : R ⊔ B = ⊤ := by
    rw [← hgen, ← hP, ← hQ]
    dsimp only [R]
    ac_rfl
  let : R.Normal := normalizer_eq_top_iff.mp
    (top_unique (hRB ▸ sup_le R.le_normalizer hB))
  let q := QuotientGroup.mk' R
  let f := q.comp B.subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective R y
    obtain ⟨r,hr,b,hb,rfl⟩ := mem_sup_of_normal_left.mp (hRB.symm ▸ mem_top x)
    refine ⟨⟨b,hb⟩,?_⟩
    change q b = q (r*b)
    rw [map_mul, show q r = 1 from (QuotientGroup.eq_one_iff r).mpr hr, one_mul]
  let : Group.IsSolvable (X ⧸ R) := Group.isSolvable_of_surjective hf
  exact top_unique (by simpa only [solvableResidual_eq_top] using
    solvableResidual_le_of_solvable_quotient R)

/-- Lift generation by parabolic residuals through a solvable kernel, without centrality. -/
theorem preimage_residuals_sup_eq_top [Group.IsPerfect X]
    (f : X →* Y) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (P Q B : Subgroup Y) [Group.IsSolvable B]
    (hBP : B ≤ P) (hBQ : B ≤ Q) (hgen : P ⊔ Q = ⊤)
    (hP : (solvableResidual P).map P.subtype ⊔ B = P)
    (hQ : (solvableResidual Q).map Q.subtype ⊔ B = Q) :
    (solvableResidual (P.comap f)).map (P.comap f).subtype ⊔
      (solvableResidual (Q.comap f)).map (Q.comap f).subtype = ⊤ := by
  let : Group.IsSolvable (B.comap f) := isSolvable_comap_of_solvable_ker f B
  have hs (D : Subgroup Y)
      (hD : (solvableResidual D).map D.subtype ⊔ B = D) :
      (solvableResidual (D.comap f)).map (D.comap f).subtype ⊔ B.comap f = D.comap f := by
    have hm : ((solvableResidual (D.comap f)).map (D.comap f).subtype ⊔ B.comap f).map f = D := by
      rw [map_sup,map_solvableResidual_comap f hf,map_comap_eq_self_of_surjective hf,hD]
    have hh := congrArg (comap f) hm
    rw [comap_map_eq, sup_eq_left.mpr
      (show f.ker ≤ (solvableResidual (D.comap f)).map (D.comap f).subtype ⊔ B.comap f from
        (MonoidHom.ker_le_comap f B).trans le_sup_right)] at hh
    exact hh
  apply residuals_sup_eq_top_of_common_solvable_supplement
    (P.comap f) (Q.comap f) (B.comap f) (comap_mono hBP) (comap_mono hBQ) _ (hs P hP) (hs Q hQ)
  rw [comap_sup_eq _ _ _ hf,hgen,comap_top]
end Subgroup

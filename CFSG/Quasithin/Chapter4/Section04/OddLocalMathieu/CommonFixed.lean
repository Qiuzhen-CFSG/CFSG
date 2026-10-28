module
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.SeedCore
public import Theory.GroupAction.CommonFixedComponents

/-!
# The Mathieu seed in the common fixed group of the entire odd actor

The full source seed P is normal in C intersect C_G(A), and its image in
Q lies in the common fixed group of A. Restriction preserves its normality.
Coprime lifting through the original two-core, followed by normal-image
central descent, makes the quasisimple simple-section image an ordinary
component of the common fixed group. No central kernel is assumed trivial,
and no normality in a single actor element's fixed group is asserted.

Hall.OddNormalizer.OddLocalComponent supplies the actual exterior seed and
its proved quasisimplicity. Source: Aschbacher--Smith 4.4.3, printed p.623,
the placement of K_Z* in the C-layer of C_{L_Z*}(B*).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
variable {G : Type*} [Group G] [Finite G]

/-- The fixed group of all original actors on the literal double quotient. -/
@[expose] def commonSimpleFixed {C : Subgroup G} (Q : Subgroup C) [Q.Normal]
    (A : Subgroup G) (hAC : A ≤ C) : Subgroup (SimpleSection Q) :=
  ⨅ x : A, (simpleAction Q (inclusion hAC x)).fixedSubgroup

attribute [-instance] MulAction.quotient in
/-- The full original seed maps to a component in the fixed group of the
whole odd actor. The two-core and central quotients are the literal source maps. -/
theorem seed_component_in_common_fixed
    {C A : Subgroup G} (hAC : A ≤ C)
    (Q : Subgroup C) [Q.Normal]
    (P : Subgroup (C ⊓ centralizer (A : Set G) : Subgroup G)) [P.Normal]
    (hPQ : P.map (inclusion inf_le_left) ≤ Q)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hA : IsPGroup p A)
    (hqs : IsQuasisimple ((projection Q).comp (seedInclusion inf_le_left hPQ)).range) :
    IsComponentIn ((projection Q).comp (seedInclusion inf_le_left hPQ)).range
      (commonSimpleFixed Q A hAC) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let α : A →* MulAut Q := MulAut.conjNormal.comp (inclusion hAC)
  let β : A →* MulAut (Q ⧸ pCore 2 Q) := (quotientAut (pCore 2 Q)).comp α
  let γ : A →* MulAut (SimpleSection Q) := (simpleAction Q).comp (inclusion hAC)
  let : MulDistribMulAction A Q := MulDistribMulAction.compHom Q α
  let : MulDistribMulAction A (Q ⧸ pCore 2 Q) :=
    MulDistribMulAction.compHom (Q ⧸ pCore 2 Q) β
  let : MulDistribMulAction A (SimpleSection Q) :=
    MulDistribMulAction.compHom (SimpleSection Q) γ
  let q := QuotientGroup.mk' (pCore 2 Q)
  let r := QuotientGroup.mk' (center (Q ⧸ pCore 2 Q))
  have he (a : A) (x : Q) : q (a • x) = a • q x := by
    exact (quotientAut_apply_mk (pCore 2 Q) (α a) x).symm
  have he' (a : A) (x : Q ⧸ pCore 2 Q) : r (a • x) = a • r x := by
    exact (quotientAut_apply_mk (center (Q ⧸ pCore 2 Q)) (β a) x).symm
  have hk : ¬ p ∣ Nat.card q.ker := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := Q)).exists_card_eq
    rw [hn]
    exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow hd))
  have hproj (a : A) (x : Q) : projection Q (a • x) = a • projection Q x := by
    exact (simpleAction_projection Q (inclusion hAC a) x).symm
  have hn : (FixedPoints.mapHom (projection Q) hproj).range.Normal :=
    FixedPoints.mapHom_range_normal_of_coprime_central_kernel hA q
      (QuotientGroup.mk'_surjective _) he hk r (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']) he'
  let j := seedInclusion inf_le_left hPQ
  let B := j.range
  let U := fixedPointSubgroup A Q
  have hBU : B ≤ U := by
    rintro _ ⟨y,rfl⟩ a
    apply Subtype.ext
    apply Subtype.ext
    change (a : G) * ((y : (C ⊓ centralizer (A : Set G) : Subgroup G)) : G) *
      (a : G)⁻¹ = _
    rw [y.val.property.2 (a : G) a.property,mul_inv_cancel_right]
    rfl
  let t : U →* (C ⊓ centralizer (A : Set G) : Subgroup G) := {
    toFun x := ⟨((x : Q) : C),⟨(x : Q).val.property,by
      apply mem_centralizer_iff.mpr
      intro a ha
      have hh := congrArg (fun z : Q => ((z : C) : G)) (x.property (⟨a,ha⟩ : A))
      change a * (((x : Q) : C) : G) * a⁻¹ = (((x : Q) : C) : G) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh⟩⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hBpre : B.subgroupOf U = P.comap t := by
    ext x
    constructor
    · rintro ⟨y,hy⟩
      have hh : t x = y := Subtype.ext
        (congrArg (fun z : Q => ((z : C) : G)) hy.symm)
      change t x ∈ P
      rw [hh]
      exact y.property
    · intro hx
      exact ⟨⟨t x,hx⟩,rfl⟩
  have hBn : (B.subgroupOf U).Normal := hBpre ▸ inferInstance
  have himage : B.map (projection Q) = ((projection Q).comp j).range :=
    (MonoidHom.range_comp _ _).symm
  have hqs' : IsQuasisimple (B.map (projection Q)) := himage.symm ▸ hqs
  have hcomp := FixedPoints.component_image_of_normal_fixed_image
    (projection Q) hproj hn B hBU hBn hqs'
  have hfixed : fixedPointSubgroup A (SimpleSection Q) = commonSimpleFixed Q A hAC := by
    ext x
    simp only [commonSimpleFixed,mem_iInf,MulAut.mem_fixedSubgroup]
    rfl
  rwa [himage,hfixed] at hcomp
end CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu

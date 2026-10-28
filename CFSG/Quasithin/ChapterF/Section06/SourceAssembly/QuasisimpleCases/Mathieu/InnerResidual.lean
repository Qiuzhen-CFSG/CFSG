module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.M12
public import Theory.Mathieu.M12.SmallParabolicPair.CoverOrbits.Residual
public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup.Coordinates
public import Theory.GroupTheory.PResidual.SylowSupplement
public import CFSG.Quasithin.ChapterF.Section06.Basic

/-!
# The marked Mathieu Sylow lies in the source two-residual

The two quaternion generators lie in the first local two-residual. The
moving cubic lies in the second, so its two-sided product with the first
quaternion generator lies in the ambient two-residual too. These are the
three established generators of the actual M₁₂ Sylow. Both commuting squares
of the marked amalgam transport this argument to the original group.
Since that intersection is an ambient Sylow in a Goldschmidt triple, the
ambient group is its own two-residual. The same coordinates give exponent
at most eight and an actual element of order eight inside this component.

Source: Aschbacher–Smith, F.6.18(12), printed p.310; F.6.6 and 14.2.21.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu

private def powerIndex (i : Fin 64) : ℕ → Fin 64
  | 0 => 0
  | n+1 => SylowAutomorphismGroup.multiply i (powerIndex i n)

private theorem element_powerIndex (i : Fin 64) (n : ℕ) :
    SylowAutomorphismGroup.element (powerIndex i n) =
      SylowAutomorphismGroup.element i ^ n := by
  induction n with
  | zero => exact SylowAutomorphismGroup.element_zero
  | succ n ih =>
    rw [powerIndex, SylowAutomorphismGroup.element_multiply, ih, pow_succ']

private theorem index_eight : ∀ i : Fin 64, powerIndex i 8 = 0 := by decide +kernel

/-- Every element of the literal Mathieu common Sylow has eighth power one. -/
theorem m12_sylow_pow_eight (x : sylowCandidate) : x ^ 8 = 1 := by
  obtain ⟨i, rfl⟩ := SylowAutomorphismGroup.element_surjective x
  rw [← element_powerIndex, index_eight, SylowAutomorphismGroup.element_zero]

/-- The third marked Sylow generator realizes order eight. -/
theorem m12_sylow_generator_order_eight :
    orderOf (SylowAutomorphismGroup.generator 2) = 8 := by
  exact orderOf_eq_prime_pow (p := 2) (n := 2)
    (by decide +kernel) (m12_sylow_pow_eight _)

variable {G : Type*} [Group G] {G₁ G₂ : Subgroup G}

/-- The literal source intersection belongs to its actual ambient two-residual. -/
theorem intersection_le_residual_of_m12_amalgam
    (hM : GreenBook.MathieuTwelve.IsM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    G₁ ⊓ G₂ ≤ pResidual 2 G := by
  obtain ⟨j⟩ := hM
  let e := (j.trans GreenBook.MathieuTwelve.concreteIso).symm
  let f₁ : firstParabolic →* G := G₁.subtype.comp e.left.toMonoidHom
  let f₂ : secondParabolic →* G := G₂.subtype.comp e.right.toMonoidHom
  let fS : sylowCandidate →* G := (G₁ ⊓ G₂).subtype.comp e.middle.toMonoidHom
  have h₁ (s : sylowCandidate) :
      f₁ (Subgroup.inclusion inf_le_left s) = fS s :=
    congrArg Subtype.val (e.left_commutes s)
  have h₂ (s : sylowCandidate) :
      f₂ (Subgroup.inclusion inf_le_right s) = fS s :=
    congrArg Subtype.val (e.right_commutes s)
  have hcore (s : sylowCandidate) (hs : (s : M12) ∈ core) : fS s ∈ pResidual 2 G := by
    obtain ⟨a, ha, has⟩ := CoverOrbits.core_le_coverResidual hs
    have he : a = Subgroup.inclusion inf_le_left s := Subtype.ext has
    rw [he] at ha
    rw [← h₁]
    exact map_pResidual_le 2 f₁ ⟨_, ha, rfl⟩
  have hfirst : fS (SylowAutomorphismGroup.generator 0) ∈ pResidual 2 G :=
    hcore _ ((mem_core _).mpr ⟨.a 1,.a 0,by decide +kernel⟩)
  have hsecond : fS (SylowAutomorphismGroup.generator 1) ∈ pResidual 2 G :=
    hcore _ ((mem_core _).mpr ⟨.a 0,.a 1,by decide +kernel⟩)
  let c : secondParabolic := ⟨movingActor, movingActor_mem⟩
  have hc : f₂ c ∈ pResidual 2 G := map_pResidual_le 2 f₂
    ⟨c,movingActor_residual,rfl⟩
  have hthird : fS (SylowAutomorphismGroup.generator 2) ∈ pResidual 2 G := by
    rw [← h₂]
    have he : Subgroup.inclusion inf_le_right (SylowAutomorphismGroup.generator 2) =
        c * Subgroup.inclusion inf_le_right (SylowAutomorphismGroup.generator 0) * c := rfl
    rw [he, map_mul, map_mul, h₂]
    exact (pResidual 2 G).mul_mem ((pResidual 2 G).mul_mem hc hfirst) hc
  have hgenerators (i : Fin 3) : fS (SylowAutomorphismGroup.generator i) ∈ pResidual 2 G := by
    fin_cases i
    · exact hfirst
    · exact hsecond
    · exact hthird
  have hword (w : List (Fin 3)) : fS (SylowAutomorphismGroup.evaluate w) ∈ pResidual 2 G := by
    induction w with
    | nil => simpa only [SylowAutomorphismGroup.evaluate, map_one] using (pResidual 2 G).one_mem
    | cons i w ih =>
      rw [SylowAutomorphismGroup.evaluate, map_mul]
      exact (pResidual 2 G).mul_mem (hgenerators i) ih
  intro x hx
  let s := e.middle.symm ⟨x,hx⟩
  obtain ⟨i, hi⟩ := SylowAutomorphismGroup.element_surjective s
  have hh := hword (SylowAutomorphismGroup.words i)
  change fS (SylowAutomorphismGroup.element i) ∈ pResidual 2 G at hh
  rw [hi] at hh
  simpa only [fS, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    s, MulEquiv.apply_symm_apply, Subgroup.subtype_apply] using hh

/-- With the original ambient Sylow condition, the marked M₁₂ case is perfect
with respect to the two-residual before any ambient model is recognized. -/
theorem residual_eq_top_of_m12_amalgam [Finite G]
    (h : IsGoldschmidtTriple G₁ G₂)
    (hM : GreenBook.MathieuTwelve.IsM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    pResidual 2 G = ⊤ := by
  obtain ⟨T, hT⟩ := h.intersection_sylow
  have hle : (T : Subgroup G) ≤ pResidual 2 G :=
    hT ▸ intersection_le_residual_of_m12_amalgam hM
  simpa only [sup_eq_left.mpr hle] using pResidual_sup_sylow_eq_top T

end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu

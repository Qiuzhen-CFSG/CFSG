module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.PCoreImage
public import Mathlib.GroupTheory.Nilpotent

/-!
# The marked A₇ input for the central-vector pushing-up argument

This is a specialized form of C.6.2 and C.6.4(I)--(III). The group in
the source is literally K S, its two-residual is K, and its quotient by
its two-core is identified with S₇. The image of R is the specified
transposition subgroup. All normalizers and the two-residual of N_K(R)
use the original ambient embeddings.

The strict containment R < Λ replaces the weaker C.6.2(3) assumption:
the normalizer condition in the finite two-group Λ, together with (II),
implies that assumption below. No central-vector conclusion is a field.
The application is original 4.3.7, where (K,R,S,Λ) denotes
(K,O₂(I),T ∩ H,O₂(LT)).

Source: Aschbacher--Smith C.6.2--4, printed pp.166--169.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
variable {G : Type*} [Group G]

/-- Genuine marked pushing-up hypotheses, with no C.6.4 conclusion. -/
structure Input (K R S Λ : Subgroup G) where
  block : IsAlternatingBlock K 7
  residual : (pResidual 2 (K ⊔ S : Subgroup G)).map (K ⊔ S).subtype = K
  quotientIso : ((K ⊔ S : Subgroup G) ⧸ pCore 2 (K ⊔ S : Subgroup G)) ≃*
    Equiv.Perm (Fin 7)
  transposition : (R.subgroupOf (K ⊔ S)).map
    (quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (K ⊔ S : Subgroup G)))) =
      zpowers (Equiv.swap (0 : Fin 7) 1)
  core_le : (K ⊔ S).pCoreIn 2 ≤ R
  R_le_S : R ≤ S
  S_two : IsPGroup 2 S
  S_normalizes_R : S ≤ normalizer (R : Set G)
  S_normalizes_Λ : S ≤ normalizer (Λ : Set G)
  Λ_two : IsPGroup 2 Λ
  proper : R < Λ
  control : ∀ A : Subgroup G, A ≠ ⊥ → A ≤ R →
    K ⊔ S ≤ normalizer (A : Set G) → Λ ⊓ normalizer (A : Set G) = R
  levi_normalizes :
    (pResidual 2 (K ⊓ normalizer (R : Set G) : Subgroup G)).map
      (K ⊓ normalizer (R : Set G)).subtype ≤ normalizer (Λ : Set G)

variable [Finite G] {K R S Λ : Subgroup G}

/-- The normalizer condition supplies the strict inequality used in C.6.2(3). -/
theorem Input.lt_normalizer (d : Input K R S Λ) :
    R < Λ ⊓ normalizer (R : Set G) := by
  let : Group.IsNilpotent Λ := d.Λ_two.isNilpotent
  have hp : R.subgroupOf Λ < ⊤ := lt_top_iff_ne_top.mpr
    (fun he => d.proper.not_ge (subgroupOf_eq_top.mp he))
  obtain ⟨x,hxn,hxr⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (R.subgroupOf Λ) hp)
  have hx : (x : G) ∈ normalizer (R : Set G) := by
    rwa [← subgroupOf_normalizer_eq d.proper.le] at hxn
  exact lt_of_le_not_ge (le_inf d.proper.le R.le_normalizer)
    (fun hle => hxr (hle ⟨x.property,hx⟩))

/-- C.6.4(II), together with R < Λ, supplies exactly C.6.2(3). -/
theorem Input.no_normal_subgroup (d : Input K R S Λ)
    {A : Subgroup G} (hne : A ≠ ⊥) (hAR : A ≤ R)
    (hn : K ⊔ S ≤ normalizer (A : Set G)) :
    ¬ Λ ⊓ normalizer (R : Set G) ≤ Λ ⊓ normalizer (A : Set G) := by
  rw [d.control A hne hAR hn]
  exact d.lt_normalizer.not_ge

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector

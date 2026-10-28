module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The A₆ section excludes the linear-three Xi model

The literal projective A₆ section forces five to divide the containing
component's order, and this divisor survives its two-core quotient.
Both linear-three models at field order three have order 5616, which is
prime to five. The full inclusion and both original core quotients are
retained. `M22CodeComponentSieve` supplies the original residual inclusion.

Source: Aschbacher--Smith 8.2.2(1), printed p.715, inspecting the
alternatives of 1.3.4, refs/quasithin.pdf. The matrix order calculation
uses the existing attributed ATLAS support API.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]

private theorem linear_three_card {Q : Type*} [Group Q]
    (h : LinearThreeModel 3 Q) : Nat.card Q = 5616 := by
  rcases h with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv,Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center (Matrix.SpecialLinearGroup (Fin 3) F)),Atlas.ExceptionalSupport.card_sl_center,
      Fintype.card_fin,hF]
    have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    rw [hF] at hh
    change Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) * Nat.gcd 3 (3 - 1) = 5616
    norm_num [Fin.prod_univ_succ] at hh ⊢
    omega
  · have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    rw [hF,←Nat.card_congr e.toEquiv] at hh
    norm_num [Fin.prod_univ_succ] at hh
    omega

/-- A projective A₆ section excludes both full linear-three core-quotient models at three. -/
theorem not_linear_three_of_projective_six_injective
    {R : Type*} [Group R] [Finite R]
    (e : ((R ⧸ pCore 2 R) ⧸ center (R ⧸ pCore 2 R)) ≃*
      alternatingGroup (Fin 6)) (f : R →* G) (hf : Function.Injective f) :
    ¬ LinearThreeModel 3 (G ⧸ pCore 2 G) := by
  let q := e.toMonoidHom.comp ((QuotientGroup.mk' (center (R ⧸ pCore 2 R))).comp
    (QuotientGroup.mk' (pCore 2 R)))
  have hq : Function.Surjective q := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have h5R : 5 ∣ Nat.card R := (show 5 ∣ Nat.card (alternatingGroup (Fin 6)) by
    rw [nat_card_alternatingGroup]; norm_num).trans (card_dvd_of_surjective q hq)
  have h5G : 5 ∣ Nat.card G := h5R.trans (card_dvd_of_injective f hf)
  have h5core : ¬ 5 ∣ Nat.card (pCore 2 G) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    intro hd
    exact (by decide : ¬ 5 ∣ 2) (Nat.prime_five.dvd_of_dvd_pow hd)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 G)] at h5G
  have h5 := (Nat.prime_five.dvd_mul.mp h5G).resolve_right h5core
  intro hm
  rw [linear_three_card hm] at h5
  norm_num at h5
end CFSG.Quasithin.Chapter8.MathieuShadowRows

module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveNormalizer.Residual
public import CFSG.Quasithin.ChapterJ.Section04To05.Span.Order

/-!
# The source intersection of the five-commutator span with Q

The actual product Q₅W has order 2048. It contains Q₀Q₅ of order 1024,
while the selected involution lies in W outside Q. Thus its intersection
with Q is exactly Q₀Q₅. This identifies the hyperplane preserved by the
second-parabolic complement in the normalizer argument.

Source: Aschbacher–Smith, J.4.4(3), printed p.441.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

theorem SourceChoice.card_Q₅_sup_W (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) : Nat.card (Q₅ d B5⊔p.W:Subgroup G)=2048 := by
  have hI := hat_card d (Q₅ d B5⊓p.W)
    (inf_le_left.trans ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _)))
  rw [s.hat_Q₅_inf_W_card B5 hi,
    inf_eq_right.mpr (le_inf (U_le_Q₅ d B5) p.U_le_W),d.ru2.card_U d.card_Z] at hI
  have hQ := hat_card d (Q₅ d B5) ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _))
  rw [hat_Q₅_card,inf_eq_right.mpr (U_le_Q₅ d B5),d.ru2.card_U d.card_Z] at hQ
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes p.W (Q₅ d B5)
    ((Q₅_le_Q d B5).trans p.W_normalized_Q)
  rw [p.card_W,inf_comm,sup_comm,←hI,←hQ] at h
  norm_num at h
  omega

theorem SourceChoice.Q₅_sup_W_inf_Q (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    (Q₅ d B5⊔p.W)⊓d.toTypeRuSetup.Q=fiveHyperplane d B5 := by
  have h0 : Q₀ d≤p.W := by
    intro x hx
    change x∈(p.W:Set G)
    rw [p.W_eq_product]
    exact ⟨1,one_mem _,x,hx,one_mul x⟩
  have hD : fiveHyperplane d B5≤(Q₅ d B5⊔p.W)⊓d.toTypeRuSetup.Q :=
    le_inf (sup_le (h0.trans le_sup_right) le_sup_left) (fiveHyperplane_le_Q d B5)
  have hlt : (Q₅ d B5⊔p.W)⊓d.toTypeRuSetup.Q < Q₅ d B5⊔p.W := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hv : s.v∈Q₅ d B5⊔p.W :=
      (show p.W≤Q₅ d B5⊔p.W from le_sup_right) (p.W₀_le_W (s.Uα_le_W₀ s.v_mem))
    exact s.v_not_Q ((he.symm ▸ hv).2)
  have hc : Nat.card ((Q₅ d B5⊔p.W)⊓d.toTypeRuSetup.Q:Subgroup G) <
      Nat.card (Q₅ d B5⊔p.W:Subgroup G) := by
    apply lt_of_not_ge
    intro hc
    exact hlt.ne (eq_of_le_of_card_ge hlt.le hc)
  rw [s.card_Q₅_sup_W B5 hi] at hc
  have hd := card_dvd_of_le hD
  rw [fiveHyperplane_card] at hd
  apply (eq_of_le_of_card_ge hD ?_).symm
  rw [fiveHyperplane_card]
  omega

end CFSG.Quasithin.ChapterJ.RuSubgroup

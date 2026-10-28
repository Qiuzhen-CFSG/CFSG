module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.AmbientReduction

/-!
# The two PSL2 component profiles under an ambient dihedral-eight Sylow

An odd PSL2 component has Sylow order four or eight. In the latter case
the two-group quotient above the component is trivial and the field order
is seven or nine modulo sixteen. In the former case the component is
proper, the field order is three or five modulo eight, and the source
degree-at-most-two restriction forces the field to have prime order.

Source: Aschbacher--Smith F.6.18(5)--(6), printed p.310.
-/

public section
open Subgroup Theory.GroupTheory Theory.ClassicalSmallSylow
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G} [K.Normal]

/-- The source parameter split is determined by the actual component's
Sylow subgroup and the original ambient two-part. -/
theorem psl_component_parameters_of_sylow_eight
    (T : Sylow 2 G) (hT : Nat.card T = 8) (hquot : IsPGroup 2 (G ⧸ K))
    {p f : ℕ} (hp : p.Prime) (ho : Odd p) (hf : 1 ≤ f) (hf2 : f ≤ 2)
    (hm : ClassicalGroup.IsPSL K 2 (p ^ f)) :
    (K = ⊤ ∧ (p ^ f % 16 = 7 ∨ p ^ f % 16 = 9)) ∨
    (K ≠ ⊤ ∧ f = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5)) := by
  obtain ⟨F, _, _, hF, ⟨eK⟩⟩ := hm
  let P : Sylow 2 PSL(2,F) := default
  have hP : Nat.card P ≤ 8 :=
    (sylow_card_section_le T K eK.toMonoidHom eK.surjective P).trans hT.le
  have hop : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, ho, by omega, hF⟩
  rcases psl2_small_sylow_parameters hop P hP with ⟨hP4, hmod⟩ | ⟨hP8, hmod⟩
  · have hproper : K ≠ ⊤ := by
      intro htop
      have hd : 8 ∣ Nat.card PSL(2,F) := by
        rw [← Nat.card_congr eK.toEquiv, htop, card_top, ← hT]
        exact T.card_subgroup_dvd_card
      have hh := P.pow_dvd_card_of_pow_dvd_card (n := 3) hd
      rw [hP4] at hh
      norm_num at hh
    rw [hF] at hmod
    have he := degree_one_of_small_degree_nonsquare_mod_eight hf2 hmod
    exact .inr ⟨hproper, he, by simpa [he] using hmod⟩
  · have h8 : 8 ∣ Nat.card K := by
      rw [Nat.card_congr eK.toEquiv, ← hP8]
      exact P.card_subgroup_dvd_card
    exact .inl ⟨normal_eq_top_of_sylow_eight_of_eight_dvd T hT K hquot h8,
      by simpa [hF] using hmod⟩

end CFSG.Quasithin.ChapterF.SourceAssembly

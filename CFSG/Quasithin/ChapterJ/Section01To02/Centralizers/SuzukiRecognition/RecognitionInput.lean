module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Geometry
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Nonnormality

/-!
# Assembling the pre-recognition deductions of J.2.9

The earlier local product and Suzuki two-group identify V and prove the
transfer hypotheses. Transfer and normal Sylow intersection construct the
actual Sylow subgroup of L_s. The seven-group orbit computes its involution
centralizers. The earlier fusion and a local non-core witness force V to
be nonnormal, so the existing TI and strong-embedding criteria apply.

This is a conditional intermediate result, not J.2.9 itself. The
Z₂×Sz(2) non-core witness and the ensuing simple-group recognition and
outer-action calculations remain to be supplied in final assembly.

Source: Aschbacher–Smith, J.2.9, printed p.438 (PDF p.449).
-/

public section
open Subgroup BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalSetup G} (c : Choices d)

/-- Every recognition premise here is proved from the preceding local
geometry and the explicit non-core model witness. -/
theorem residual_recognition_inputs [IsElementaryAbelian 2 c.S0]
    (P : Sylow 2 c.Gs) (hP : (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs)
    (e : P ≃* c.S0 × c.S1)
    (he : ∀ x : P, ((x : c.Gs) : G) = ((e x).1 : G) * ((e x).2 : G))
    (hsuzuki : IsSuzukiTwoGroup c.S1) (htrans : c.B7TransitiveOnV)
    (hCL : d.L ⊓ c.Gs = c.Ts ⊔ c.B7)
    (hH : centralizer ({c.z} : Set G) = d.toTypeRuSetup.H)
    (hHs : d.toTypeRuSetup.H ⊓ c.Gs = c.Ts)
    (hzV : c.z ∈ d.V) (hz1 : c.z ≠ 1)
    (hsfusion : ∀ t ∈ d.toTypeRuSetup.H, IsConj c.s t →
      ∃ h ∈ d.toTypeRuSetup.H, h * c.s * h⁻¹ = t)
    {t v : G} (hst : IsConj c.s t) (hv : v ∈ centralizer ({t} : Set G))
    (hzv : IsConj c.z v) (hvn : v ∉ (centralizer ({t} : Set G)).pCoreIn 2) :
    Disjoint c.S0 c.Ls ∧ IsPPerfect 2 c.Ls ∧
      (omega₁ c.S1 (p := 2)).map c.S1.subtype = d.V ∧
      ∃ Q : Sylow 2 c.Ls,
        (Q : Subgroup c.Ls) = c.S1.subgroupOf c.Ls ∧
        (∀ x : c.Ls, x ∈ d.V.subgroupOf c.Ls ↔
          x ∈ c.S1.subgroupOf c.Ls ∧ x ^ 2 = 1) ∧
        (∀ x : c.Ls, x ∈ d.V.subgroupOf c.Ls → x ≠ 1 →
          centralizer ({x} : Set c.Ls) = c.S1.subgroupOf c.Ls) ∧
        normalizer (d.V.subgroupOf c.Ls : Set c.Ls) ≠ ⊤ ∧
        IsTISubgroup (d.V.subgroupOf c.Ls) ∧
        BenderSuzuki.IsStronglyEmbedded (normalizer (d.V.subgroupOf c.Ls : Set c.Ls)) := by
  have hd := c.disjoint_S0_Ls_of_suzuki_two_group P hP e he hsuzuki htrans hCL
  have hproduct : ∀ x ∈ c.Ts, ∃ a ∈ c.S0, ∃ b ∈ c.S1, x = a * b := by
    intro x hx
    let xG : c.Gs := ⟨x, (show c.Ts ≤ c.Gs from inf_le_right) hx⟩
    let xP : P := ⟨xG, by change xG ∈ (P : Subgroup c.Gs); rw [hP]; exact hx⟩
    exact ⟨(e xP).1, (e xP).1.property, (e xP).2, (e xP).2.property, he xP⟩
  have hi := c.Ts_inf_Ls hd hproduct
  obtain ⟨Q, hQ⟩ := c.exists_sylow_Ls P hP hi
  have hC := c.uniform_Ls_centralizers (c.Ls_inf_centralizer_z hH hHs hi)
    (htrans c.z hzV hz1)
  have hV (x : c.Ls) : x ∈ d.V.subgroupOf c.Ls ↔
      x ∈ c.S1.subgroupOf c.Ls ∧ x ^ 2 = 1 := by
    constructor
    · intro hx
      obtain ⟨hm, hp⟩ := (c.mem_V_iff_S1_square_one hsuzuki htrans x).mp hx
      exact ⟨hm, Subtype.ext hp⟩
    · rintro ⟨hm, hp⟩
      exact (c.mem_V_iff_S1_square_one hsuzuki htrans x).mpr
        ⟨hm, congrArg Subtype.val hp⟩
  have hn := c.V_normalizer_ne_top_of_z_not_mem_twoCore
    ((c.V_le_S1 hsuzuki.2.1 htrans).trans c.S1_le_Ls) hzV
    (c.z_not_mem_twoCore_of_local_witness hH hsfusion hst hv hzv hvn)
  exact ⟨hd, c.Ls_isPPerfect, c.omega_S1_eq_V hsuzuki htrans,
    Q, hQ, hV, hC, hn, c.residual_ti_and_strongEmbedding Q hQ hV hC hn⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices

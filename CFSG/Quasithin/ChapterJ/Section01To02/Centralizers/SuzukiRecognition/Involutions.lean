module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Geometry
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Nonnormality

/-!
# The involution-class equality in J.2.9(3)

Every residual involution is conjugate into its actual Sylow S₁, hence
into V=Ω₁(S₁), and the seven-group fuses it to z. Conversely, the earlier
H-fusion makes zᴳ∩C_G(s) one C_G(s)-class. Relative normality of L_s
therefore puts this entire class in L_s. This proves the source set
equality without using the later Suzuki identification.

Source: Aschbacher–Smith, J.2.9(3), printed p.438 (PDF p.449).
-/

public section
open Subgroup BenderSuzuki.PFAppendixIII
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalSetup G} (c : Choices d)

/-- Sylow conjugacy and the Singer orbit fuse every residual involution to z. -/
theorem residual_involution_isConj_z
    (P : Sylow 2 c.Ls) (hP : (P : Subgroup c.Ls) = c.S1.subgroupOf c.Ls)
    (hsuzuki : IsSuzukiTwoGroup c.S1) (htrans : c.B7TransitiveOnV)
    (hzV : c.z ∈ d.V) (hz1 : c.z ≠ 1)
    {x : G} (hxL : x ∈ c.Ls) (hx : IsInvolution x) : IsConj c.z x := by
  let xL : c.Ls := ⟨x, hxL⟩
  have hxI : IsInvolution xL :=
    ⟨fun h => hx.ne_one (congrArg Subtype.val h), Subtype.ext hx.sq_eq_one⟩
  obtain ⟨Q, hQ⟩ := (BenderSuzuki.isPGroup_zpowers_of_involution hxI).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq c.Ls Q P
  let y := (MulAut.conj g) xL
  have hyP : y ∈ (P : Subgroup c.Ls) := by
    rw [← hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hQ (mem_zpowers xL))
  have hyS : (y : G) ∈ c.S1 := by rwa [hP] at hyP
  have hy2 : y ^ 2 = 1 := by
    change ((MulAut.conj g) xL) ^ 2 = 1
    rw [← map_pow, hxI.sq_eq_one, map_one]
  have hy1 : (y : G) ≠ 1 := by
    intro h
    have hy : y = 1 := Subtype.ext h
    exact hxI.ne_one ((MulAut.conj g).injective (hy.trans (map_one _).symm))
  have hyV := (c.mem_V_iff_S1_square_one hsuzuki htrans y).mpr
    ⟨hyS, congrArg Subtype.val hy2⟩
  obtain ⟨b, _, hb⟩ := htrans c.z hzV hz1 y hyV hy1
  have hxy : IsConj x (y : G) := isConj_iff.mpr ⟨(g : G), rfl⟩
  exact (isConj_iff.mpr ⟨b, hb⟩).trans hxy.symm

/-- J.2.9(3), conditional only on the constructed Sylow and the preceding
J.2.3 and J.2.7 fusion data. Both sides are literal subsets of G. -/
theorem z_class_intersection_Gs
    (P : Sylow 2 c.Ls) (hP : (P : Subgroup c.Ls) = c.S1.subgroupOf c.Ls)
    (hsuzuki : IsSuzukiTwoGroup c.S1) (htrans : c.B7TransitiveOnV)
    (hzV : c.z ∈ d.V) (hz1 : c.z ≠ 1)
    (hH : centralizer ({c.z} : Set G) = d.toTypeRuSetup.H)
    (hsfusion : ∀ t ∈ d.toTypeRuSetup.H, IsConj c.s t →
      ∃ h ∈ d.toTypeRuSetup.H, h * c.s * h⁻¹ = t) :
    {x : G | IsConj c.z x} ∩ (c.Gs : Set G) =
      {x : G | x ∈ c.Ls ∧ IsInvolution x} := by
  have hzL := c.S1_le_Ls (c.V_le_S1 hsuzuki.2.1 htrans hzV)
  have hz2 : c.z ^ 2 = 1 := congrArg Subtype.val
    (d.ru1.natural.square_eq_one_of_trivial_kernel rfl ⟨c.z, hzV⟩)
  ext x
  constructor
  · rintro ⟨hconj, hxG⟩
    obtain ⟨k, hk, he⟩ := c.z_fusion_in_Gs hH hsfusion hxG hconj
    have hm : x ∈ c.Ls := he ▸ (c.Gs_normalizes_Ls hk c.z).mp hzL
    have hfx : (MulAut.conj k) c.z = x := he
    refine ⟨hm, ?_, ?_⟩
    · intro hx1
      exact hz1 ((MulAut.conj k).injective ((hfx.trans hx1).trans (map_one _).symm))
    · have hh := congrArg (MulAut.conj k) hz2
      simpa only [map_pow, map_one, hfx] using hh
  · rintro ⟨hxL, hx⟩
    exact ⟨c.residual_involution_isConj_z P hP hsuzuki htrans hzV hz1 hxL hx,
      c.Ls_le_Gs hxL⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices

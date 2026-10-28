module

public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.SourceChoice
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The two original points span the selected Ru plane

The second residual normalizes V₂. Its selected element lies outside H,
so it moves the subgroup Z of order two: normalization of Z would force
centralization. Thus Z and its selected conjugate generate V₂. The proof
retains the actual chosen element and the original ambient subgroups.

Source: Aschbacher–Smith, J.4.1 proof, printed p.440.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

/-- The selected conjugate point lies in the original plane. -/
theorem SourceChoice.conjugate_point_le (s : SourceChoice p) :
    d.toTypeRuSetup.Z.map (MulAut.conj s.g).toMonoidHom ≤ p.group := by
  have hn := ((p.mem_parabolic s.g).mp (p.L₂_le_parabolic s.in_residual)).2
  have he := mem_normalizer_iff_map_conj_eq.mp hn
  exact (map_mono p.point_le).trans_eq he

/-- The selected conjugate point is distinct from the original point. -/
theorem SourceChoice.conjugate_point_not_le (s : SourceChoice p) :
    ¬ d.toTypeRuSetup.Z.map (MulAut.conj s.g).toMonoidHom ≤ d.toTypeRuSetup.Z := by
  intro h
  have he : d.toTypeRuSetup.Z.map (MulAut.conj s.g).toMonoidHom = d.toTypeRuSetup.Z :=
    eq_of_le_of_card_ge h (by rw [card_map_of_injective (MulAut.conj s.g).injective])
  exact s.outside_H (normalizer_le_centralizer_of_card_two _ d.card_Z
    (mem_normalizer_iff_map_conj_eq.mpr he))

/-- The source identity V₂ = ZZα for the literal selected conjugator. -/
theorem SourceChoice.plane_eq_join_points (s : SourceChoice p) :
    p.group = d.toTypeRuSetup.Z ⊔
      d.toTypeRuSetup.Z.map (MulAut.conj s.g).toMonoidHom := by
  let J := d.toTypeRuSetup.Z ⊔ d.toTypeRuSetup.Z.map (MulAut.conj s.g).toMonoidHom
  have hle : J ≤ p.group := sup_le p.point_le s.conjugate_point_le
  have hZJ : d.toTypeRuSetup.Z ≤ J := le_sup_left
  have h2dvd : 2 ∣ Nat.card J := d.card_Z ▸ card_dvd_of_le hZJ
  have hpos : 0 < Nat.card J := Nat.card_pos
  have hne : Nat.card J ≠ 2 := by
    intro hc
    have he : d.toTypeRuSetup.Z = J :=
      eq_of_le_of_card_ge hZJ (by rw [hc,d.card_Z])
    exact s.conjugate_point_not_le (le_sup_right.trans_eq he.symm)
  have hfour : 4 ≤ Nat.card J := by
    obtain ⟨n,hn⟩ := h2dvd
    omega
  exact (eq_of_le_of_card_ge hle (by rw [p.card]; exact hfour)).symm

end CFSG.Quasithin.ChapterJ.RuSubgroup

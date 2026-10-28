module
public import CFSG.Quasithin.ChapterJ.Section04To05.SecondParabolic.Local
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicGeneration.SecondPoint

/-!
# The original second endpoint moves the central point of A

Conjugating Z by the actual second endpoint spans the original plane of
order four. If every automorphism of A fixed its marked involution, the
normality of A in that endpoint would instead keep the entire span in Z.
Thus an actual automorphism of A moves the original point. Together with
the intrinsic description of A this excludes the bad first-endpoint
cyclic-four extensions.

Source: Aschbacher–Smith J.4.5, printed p.442.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

/-- An automorphism of the actual second core moves the original central point.
The second endpoint supplies it through its genuine action on the plane. -/
theorem SourceChoice.exists_A_moving_point (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (z:p.A B5) (hz:zpowers (z:G)=d.toTypeRuSetup.Z) :
    ∃α:MulAut (p.A B5),α z≠z := by
  by_contra hn
  have hfix:∀α:MulAut (p.A B5),α z=z:=by simpa only [not_exists,not_not] using hn
  obtain ⟨X,hgen,_⟩:=s.exists_second_local p B5 hi
  have hFN:p.F₂ B5 X≤normalizer (p.A B5:Set G):=
    (normal_subgroupOf_iff_le_normalizer (p.A_le_F₂ B5 X)).mp inferInstance
  have hFZ:p.F₂ B5 X≤normalizer (d.toTypeRuSetup.Z:Set G):=by
    intro f hf
    have hh:=congrArg (fun a:p.A B5=>(a:G))
      (hfix ((p.A B5).normalizerMonoidHom ⟨f,hFN hf⟩))
    change f*(z:G)*f⁻¹=(z:G) at hh
    rw [←hz,mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (f*(z:G)*f⁻¹)=zpowers (z:G)
    rw [hh]
  have hspan:p.group≤d.toTypeRuSetup.Z:=by
    rw [←s.point_span_supplement (p.F₂ B5 X) hgen]
    exact conjugateSpanBy_le le_rfl hFZ
  have hc:=card_le_of_le hspan
  rw [p.card,d.card_Z] at hc
  omega

end CFSG.Quasithin.ChapterJ.RuSubgroup

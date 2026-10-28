module
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedQ0
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Local

/-!
# The original cyclic-four centralizer inside the two-core

The literal marked diagonal has square z and belongs to HC outside U.
Consequently its whole centralizer lies in H=C_G(z), and source J.2.4 gives
its exact intersection with Q as Iz·U. No whole-centralizer decomposition
is assumed. Source: Aschbacher–Smith J.4.8 preparation, printed p.443.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.DiagonalCentralizer
open Subgroup Centralizers Centralizers.Choices MarkedNormalizer MarkedInverter
open Tits.ExceptionalParabolics.FullRee
open Tits.ExceptionalParabolics.FullRee.LongRootPaths
open Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer
open Tits.ExceptionalParabolics.FullRee.LongRootPaths.RootRelations
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

theorem diagonal_mem_first : s*q⁻¹ ∈ first :=
  sylow_le_first (S.mul_mem s_mem_sylow (S.inv_mem q_mem_sylow))

def modelDiagonal : first := ⟨s*q⁻¹,diagonal_mem_first⟩
def diagonal : G := e modelDiagonal

omit [Finite G] in
theorem sourceIz_eq_zpowers : sourceIz e = zpowers (diagonal e) := by
  have h : Iz.subgroupOf first = zpowers modelDiagonal := by
    apply map_injective first.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Iz≤first from zpowers_le.mpr diagonal_mem_first),MonoidHom.map_zpowers]
    rfl
  rw [sourceIz,h,MonoidHom.map_zpowers]
  rfl

theorem diagonal_square_source (hz : (e modelZ:G)=c.z) : (diagonal e)^2=c.z := by
  have h : modelDiagonal^2=modelZ := Subtype.ext diagonal_square
  simpa only [diagonal,map_pow,coe_pow,hz] using congrArg (fun a:F => (a:G)) (congrArg e h)

theorem diagonal_mem_HC
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    diagonal e ∈ d.toTypeRuSetup.HC := by
  apply five_centralizer_le_HC B5
  apply sourceIz_le_CQ c B5 e hz hfive
  rw [sourceIz_eq_zpowers]
  exact mem_zpowers _

theorem diagonal_not_mem_U (hz : (e modelZ:G)=c.z) : diagonal e ∉ d.toTypeRuSetup.U := by
  intro hi
  let := d.elementary_U
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 d.toTypeRuSetup.U)
      (⟨diagonal e,hi⟩ : d.toTypeRuSetup.U)
  have hz1 : c.z=1 := (diagonal_square_source c e hz).symm.trans (congrArg Subtype.val h)
  have ho := SourceCompletion.z_order c
  simp [hz1] at ho

theorem centralizer_le_H (hz : (e modelZ:G)=c.z) :
    centralizer (sourceIz e : Set G) ≤ d.toTypeRuSetup.H := by
  rw [c.H_eq_centralizer_z]
  have hzI : c.z∈sourceIz e := by
    rw [sourceIz_eq_zpowers,← diagonal_square_source c e hz]
    exact pow_mem (mem_zpowers _) _
  exact centralizer_le (Set.singleton_subset_iff.mpr hzI)

theorem Q_inf_centralizer
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    d.toTypeRuSetup.Q ⊓ centralizer (sourceIz e : Set G) =
      sourceIz e ⊔ d.toTypeRuSetup.U := by
  rw [sourceIz_eq_zpowers, zpowers_eq_closure, centralizer_closure]
  rw [← zpowers_eq_closure]
  exact ((SourceCompletion.fusion c).1 (diagonal e)
    (diagonal_mem_HC c B5 e hz hfive) (diagonal_not_mem_U c e hz)).2.2

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.DiagonalCentralizer

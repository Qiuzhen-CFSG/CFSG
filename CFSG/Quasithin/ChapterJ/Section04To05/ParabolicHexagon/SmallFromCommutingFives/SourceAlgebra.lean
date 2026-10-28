module
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.Exchange
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.PathTransport

/-!
# SourceAlgebra for the commuting-five smallness argument

The original z inverts each nontrivial element of its fixed-five factor.
Thus its product with the b-conjugate label has order5, while the original
base five centralizes b. The literal injective map from the source
completion transports both assertions without completion recognition.

Source: Aschbacher–Smith J.4.10, printed p.445.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.ParabolicHexagon.SmallFromCommutingFives
open FiveHexagon FiveHexagon.MarkedInverter Centralizers.Choices
open ChapterF.SourceCompletion.BinaryRee
open Tits.ExceptionalParabolics.FullRee
variable {K:Type*} [Group K] (q:Completion K)
  {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (c:Centralizers.Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
  {F:Subgroup G} (e:first≃*F) (f:K→*G)
  (hf:Function.Injective f) (hleft:∀a:first,f (q.left a)=(e a:G))
  (hz:(e modelZ:G)=c.z)
  (hfive:(zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
include hf hleft hz hfive

 theorem fixed_five_label_product (b:K) (hb:f b∈fixedFive B5 (sourceU e)) (hb1:f b≠1) :
    orderOf (q.left modelZ*(b*q.left modelZ*b⁻¹))=5 := by
  have hu:=source_inverter c B5 e hz hfive
  have huz:=PathTransport.source_fusion q c e f hleft hz
  have hcard:Nat.card (fixedFive B5 (sourceU e))=5:=
    (source_fixed_pair c B5 e hz hfive huz).1
  let a:fixedFive B5 (sourceU e):=⟨f b,hb⟩
  have ho:orderOf (f b)=5:=by
    have hd:=orderOf_dvd_natCard a
    rw [hcard] at hd
    rcases (Nat.dvd_prime (by decide:Nat.Prime 5)).mp hd with hh|hh
    · have he:a=1:=orderOf_eq_one_iff.mp hh
      exact False.elim (hb1 (congrArg Subtype.val he))
    · change orderOf (a:G)=5
      rw [orderOf_coe]
      exact hh
  have hz2:= (c.z_involution_of_card d.card_Z).2
  have hzInv:c.z⁻¹=c.z:=inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hz2)
  have hi:=base_inverts_fixed c B5 (sourceU e) hu.1 huz hu.2 (f b) hb
  have he:c.z*(f b*c.z*(f b)⁻¹)=((f b)⁻¹)^2:=by
    rw [pow_two,←hi,hzInv]
    group
  rw [←orderOf_injective f hf,map_mul,map_mul,map_mul,map_inv,hleft,hz,he,
    orderOf_pow' _ (by decide:2≠0),orderOf_inv,ho]
  decide

omit hz in
 theorem fixed_five_commutes_rotation (b:K) (hb:f b∈fixedFive B5 (sourceU e)) :
    Commute (q.left modelRotation) b := by
  apply (commute_map_iff hf).mp
  have hr:f (q.left modelRotation)∈B5Image B5:=by
    rw [hleft,←hfive]
    exact mem_map_of_mem _ (mem_zpowers modelRotation)
  exact (central_edge B5 (sourceU e) hr (f b) hb).symm
end CFSG.Quasithin.ChapterJ.RuSubgroup.ParabolicHexagon.SmallFromCommutingFives

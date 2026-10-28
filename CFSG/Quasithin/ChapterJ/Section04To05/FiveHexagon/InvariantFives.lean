module

public import Theory.SpecificGroups.SymmetricFive.CentralLiftPentagons
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.DiagonalCentralizer.Quotient
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SourceBaseOpposite

/-!
# The two I-invariant fives in the original centralizer factor

The literal Ru2 quotient restricts to an SL₂(5) factor with central kernel
of order two and image A₅. The original inverter is the square of the
marked order-four actor, so its S₅ image is an even involution. Its action
therefore normalizes at most two five-subgroups, by unique coprime lifting
and the concrete two-pentagon count. Every I-invariant five is among them.
All quotient and conjugation maps remain the actual original source maps.

Source: Aschbacher–Smith, the final paragraph before J.4.8, printed p.443.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Centralizers Centralizers.Choices MarkedInverter DiagonalCentralizer
open Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

private theorem source_inverter_quotient
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    ∃ uH:d.toTypeRuSetup.H, (uH:G)=sourceU e ∧
      orderOf (d.ru2.quotientMap uH)=2 ∧
      d.ru2.quotientMap uH∈alternatingGroup (Fin 5) := by
  obtain ⟨t,ht,ht2,ho,hs⟩ := exists_order_four_image c B5 e hz hfive
  refine ⟨t^2,ht2,?_,?_⟩
  · rw [map_pow,orderOf_pow,ho]
    decide
  · rw [map_pow,Equiv.Perm.mem_alternatingGroup,map_pow]
    exact Int.units_sq _

/-- The genuine original I has at most two invariant five-subgroups inside
its actual SL₂(5) centralizer factor. -/
theorem source_invariant_five_eq_or_eq
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (K:Subgroup G) (hK:K≤centralizer (sourceIz e:Set G))
    (hIK:sourceI e≤normalizer (K:Set G)) (hBK:B5Image B5≤K)
    (eK:K≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
    (A B C:Subgroup G) (hAK:A≤K) (hB'K:B≤K) (hCK:C≤K)
    (hA:Nat.card A=5) (hB:Nat.card B=5) (hC:Nat.card C=5)
    (hIA:sourceI e≤normalizer (A:Set G)) (hIB:sourceI e≤normalizer (B:Set G))
    (hIC:sourceI e≤normalizer (C:Set G)) (hne:A≠B) : C=A ∨ C=B := by
  have hKH := hK.trans (centralizer_le_H c e hz)
  let f := componentMap K hKH
  have hker := (componentMap_structure B5 K hKH hBK eK).1
  have hcop : (Nat.card f.ker).Coprime 5 := by
    rw [hker,Theory.SpecificGroups.SL2.PermutationFiveImage.card_center eK]
    decide
  have huI := (source_marks_mem c e hz).2
  let a:MulAut K := K.normalizerMonoidHom ⟨sourceU e,hIK huI⟩
  obtain ⟨uH,huH,huo,hue⟩ := source_inverter_quotient c B5 e hz hfive
  let v := d.ru2.quotientMap uH
  have heq (x:K) : f (a x)=v*f x*v⁻¹ := by
    change d.ru2.quotientMap ⟨sourceU e*(x:G)*(sourceU e)⁻¹,_⟩=
      d.ru2.quotientMap uH*d.ru2.quotientMap (inclusion hKH x)*(d.ru2.quotientMap uH)⁻¹
    rw [← map_inv,← map_mul,← map_mul]
    congr 1
    apply Subtype.ext
    change sourceU e*(x:G)*(sourceU e)⁻¹=(uH:G)*(x:G)*(uH:G)⁻¹
    rw [huH]
  have hinv (D:Subgroup G) (hDK:D≤K) (hID:sourceI e≤normalizer (D:Set G)) :
      (D.subgroupOf K).map a.toMonoidHom=D.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_map]
    have he : K.subtype.comp a.toMonoidHom=
        (MulAut.conj (sourceU e)).toMonoidHom.comp K.subtype := by
      apply MonoidHom.ext
      intro x
      rfl
    rw [he,← map_map,map_subgroupOf_eq_of_le hDK]
    exact mem_normalizer_iff_map_conj_eq.mp (hID huI)
  have hne' : A.subgroupOf K≠B.subgroupOf K := by
    intro hh
    have hm := congrArg (Subgroup.map K.subtype) hh
    rw [map_subgroupOf_eq_of_le hAK,map_subgroupOf_eq_of_le hB'K] at hm
    exact hne hm
  have hh := Theory.SpecificGroups.SymmetricFive.CentralLiftPentagons.invariant_five_eq_or_eq
    f hker.le hcop a v huo hue heq (A.subgroupOf K) (B.subgroupOf K) (C.subgroupOf K)
    ((Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv).trans hA)
    ((Nat.card_congr (subgroupOfEquivOfLe hB'K).toEquiv).trans hB)
    ((Nat.card_congr (subgroupOfEquivOfLe hCK).toEquiv).trans hC)
    (hinv A hAK hIA) (hinv B hB'K hIB) (hinv C hCK hIC) hne'
  have liftEq (D:Subgroup G) (hDK:D≤K) (hh:C.subgroupOf K=D.subgroupOf K) : C=D := by
    have hm := congrArg (Subgroup.map K.subtype) hh
    rwa [map_subgroupOf_eq_of_le hCK,map_subgroupOf_eq_of_le hDK] at hm
  exact hh.elim (fun h => Or.inl (liftEq A hAK h)) (fun h => Or.inr (liftEq B hB'K h))

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer

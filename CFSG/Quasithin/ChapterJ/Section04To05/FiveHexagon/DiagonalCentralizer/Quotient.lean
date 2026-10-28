module
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.DiagonalCentralizer.Kernel
public import Theory.SpecificGroups.SL2.PermutationFiveImage

/-!
# The literal quotient image of the diagonal-centralizer factors

The original fourth root of the inverter has order-four image in S₅, hence
odd sign. Any actual SL₂(5) subgroup containing B₅ has A₅ as its image, and
its kernel is its center of order two. All maps are restrictions of the
original Ru2 quotient map. Source: J.4.8 preparation, printed p.443.
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

private theorem Q_inf_normalizer_five_le_centralizer :
    d.toTypeRuSetup.Q ⊓ normalizer (B5Image B5:Set G) ≤ centralizer (B5Image B5:Set G) := by
  have hd : Disjoint d.toTypeRuSetup.Q (B5Image B5) := disjoint_of_coprime_natCard (by
    rw [d.ru2.card_Q d.card_Z,B5Image_card d.card_Z B5]; decide)
  rintro x ⟨hx,hn⟩ b hb
  have hBQ := d.ru2.six.normalized (map_subtype_le (B5 : Subgroup d.toTypeRuSetup.H) hb)
  have hQ : x*b*x⁻¹*b⁻¹∈d.toTypeRuSetup.Q := by
    have h := (mem_normalizer_iff.mp hBQ x⁻¹).mp (d.toTypeRuSetup.Q.inv_mem hx)
    simpa only [mul_assoc] using d.toTypeRuSetup.Q.mul_mem hx h
  have hB : x*b*x⁻¹*b⁻¹∈B5Image B5 :=
    (B5Image B5).mul_mem ((mem_normalizer_iff.mp hn b).mp hb) ((B5Image B5).inv_mem hb)
  have he : x*b*x⁻¹*b⁻¹=1 := disjoint_def.mp hd hQ hB
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp he)).symm

theorem inverter_not_Q
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    sourceU e∉d.toTypeRuSetup.Q := by
  obtain ⟨_,hinv⟩ := source_inverter c B5 e hz hfive
  intro huQ
  have hc := Q_inf_normalizer_five_le_centralizer B5 ⟨huQ,
    sourceI_le_normalizer B5 e hfive (source_marks_mem c e hz).2⟩
  let B := B5Image B5
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic B := isCyclic_of_prime_card (B5Image_card d.card_Z B5)
  obtain ⟨b,hb⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic B)
  have ho : orderOf (b:G)=5 := (orderOf_coe b).trans (hb.trans (B5Image_card d.card_Z B5))
  have hconj : sourceU e*(b:G)*(sourceU e)⁻¹=(b:G) :=
    mul_inv_eq_of_eq_mul (hc b b.property).symm
  have hi : (b:G)=(b:G)⁻¹ := hconj.symm.trans (hinv b b.property)
  have hp : (b:G)^2=1 := by
    calc (b:G)^2 = (b:G)*(b:G) := pow_two _
         _ = (b:G)⁻¹*(b:G) := congrArg (fun x:G => x*(b:G)) hi
         _ = 1 := inv_mul_cancel _
  have hh := orderOf_dvd_of_pow_eq_one hp
  rw [ho] at hh
  norm_num at hh

/-- The specified C4-by-C4 has an odd element in the literal S5 quotient. -/
theorem exists_order_four_image
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    ∃ t : d.toTypeRuSetup.H, (t:G)∈sourceI e ∧ (t:G)^2=sourceU e ∧
      orderOf (d.ru2.quotientMap t)=4 ∧ (d.ru2.quotientMap t).sign≠1 := by
  let q0 : first := ⟨q,sylow_le_first q_mem_sylow⟩
  let qG : G := e q0
  have hqI : qG∈sourceI e := mem_map_of_mem _ (mem_sup_right (mem_zpowers q))
  let t : d.toTypeRuSetup.H := ⟨qG,sourceI_le_H c e hz hqI⟩
  have hq2 : qG^2=sourceU e := by
    have hh : q0^2=modelU := Subtype.ext q_square
    simpa only [qG,sourceU,map_pow,coe_pow] using congrArg (fun a:F => (a:G)) (congrArg e hh)
  have hq4 : qG^4=1 := by
    rw [show qG^4=(qG^2)^2 by rw [← pow_mul],hq2]
    exact (source_involution_marks c e hz).1
  have h4 : (d.ru2.quotientMap t)^4=1 := by
    rw [← map_pow,show t^4=1 from Subtype.ext hq4,map_one]
  have h2 : (d.ru2.quotientMap t)^2≠1 := by
    intro he
    have hQ : t^2∈d.ru2.quotientMap.ker := by rw [MonoidHom.mem_ker,map_pow,he]
    rw [d.ru2.quotient_kernel] at hQ
    have hh : qG^2∈d.toTypeRuSetup.Q := hQ
    rw [hq2] at hh
    exact inverter_not_Q c B5 e hz hfive hh
  have h : ∀ g : Equiv.Perm (Fin 5), g^4=1 → g^2≠1 → g.sign≠1 := by decide +kernel
  exact ⟨t,hqI,hq2,orderOf_eq_four_of_fourth_power h4 h2,h _ h4 h2⟩

theorem exists_odd_image
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    ∃ t : d.toTypeRuSetup.H, (t:G)∈sourceI e ∧ (d.ru2.quotientMap t).sign≠1 := by
  obtain ⟨t,ht,_,_,hs⟩ := exists_order_four_image c B5 e hz hfive
  exact ⟨t,ht,hs⟩

def componentMap (K : Subgroup G) (hKH : K≤d.toTypeRuSetup.H) : K→*S5 :=
  d.ru2.quotientMap.comp (inclusion hKH)

/-- An actual SL2(5) containing the original B5 has precisely the A5 image. -/
theorem componentMap_structure (K : Subgroup G) (hKH : K≤d.toTypeRuSetup.H)
    (hBK : B5Image B5≤K) (eK : K≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :
    (componentMap K hKH).ker=center K ∧
      (componentMap K hKH).range=alternatingGroup (Fin 5) := by
  apply Theory.SpecificGroups.SL2.PermutationFiveImage.kernel_and_range eK
  intro he
  have hBQ : B5Image B5≤d.toTypeRuSetup.Q := by
    intro b hb
    have hk : (⟨b,hBK hb⟩:K)∈(componentMap K hKH).ker := by
      change componentMap K hKH ⟨b,hBK hb⟩=1
      rw [he]; rfl
    change d.ru2.quotientMap (⟨b,hKH (hBK hb)⟩:d.toTypeRuSetup.H)=1 at hk
    have hmem := (MonoidHom.mem_ker.mpr hk)
    rw [d.ru2.quotient_kernel] at hmem
    exact hmem
  have hd := card_dvd_of_le hBQ
  rw [B5Image_card d.card_Z B5,d.ru2.card_Q d.card_Z] at hd
  norm_num at hd

theorem componentMap_ker_map (K : Subgroup G) (hKH : K≤d.toTypeRuSetup.H) :
    (componentMap K hKH).ker.map K.subtype=K⊓d.toTypeRuSetup.Q := by
  ext x
  constructor
  · rintro ⟨k,hk,rfl⟩
    refine ⟨k.property,?_⟩
    change d.ru2.quotientMap (inclusion hKH k)=1 at hk
    have hmem := MonoidHom.mem_ker.mpr hk
    rw [d.ru2.quotient_kernel] at hmem
    exact hmem
  · rintro ⟨hxK,hxQ⟩
    refine ⟨⟨x,hxK⟩,?_,rfl⟩
    change d.ru2.quotientMap (⟨x,hKH hxK⟩:d.toTypeRuSetup.H)=1
    apply MonoidHom.mem_ker.mp
    rw [d.ru2.quotient_kernel]
    exact hxQ

theorem component_inf_Q_center (K : Subgroup G) (hKH : K≤d.toTypeRuSetup.H)
    (hBK : B5Image B5≤K) (eK : K≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :
    K⊓d.toTypeRuSetup.Q=(center K).map K.subtype ∧
      Nat.card (K⊓d.toTypeRuSetup.Q : Subgroup G)=2 := by
  have he : K⊓d.toTypeRuSetup.Q=(center K).map K.subtype := by
    rw [← componentMap_ker_map K hKH,(componentMap_structure B5 K hKH hBK eK).1]
  refine ⟨he,?_⟩
  rw [he,card_map_of_injective K.subtype_injective]
  exact Theory.SpecificGroups.SL2.PermutationFiveImage.card_center eK

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.DiagonalCentralizer

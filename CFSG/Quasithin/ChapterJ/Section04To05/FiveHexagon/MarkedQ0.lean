module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedDiagonal
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedReflection
public import CFSG.Quasithin.ChapterJ.Section04To05.Span.Definitions

/-!
# Placing the marked cyclic diagonal in the original central preimage Q₀

The order-four root q has square equal to the inverter u. Its original S₅
image therefore has order four and is odd. The diagonal already lies in
CQ≤HC and commutes with q. Since K centralizes HC modulo U, the odd q
and K together force the diagonal's H/U image central. This uses the original
quotient maps and does not assume the Q₀ placement. Source: J.4.7, p.442.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Subgroup
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
open Tits.ExceptionalParabolics.FullRee.LongRootPaths
open Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer
open Tits.ExceptionalParabolics.FullRee.LongRootPaths.RootRelations
open scoped commutatorElement
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

private def modelQ : first := ⟨q,sylow_le_first q_mem_sylow⟩

omit [Finite G] in
private theorem I_comm (a b : sourceI e) : a*b=b*a := by
  obtain ⟨f⟩ := sourceI_equiv e
  exact f.injective (by simp only [map_mul,mul_comm])

private theorem normalizing_Q_centralizes {x : G} (hx : x∈d.toTypeRuSetup.Q)
    (hn : x∈normalizer (B5Image B5:Set G)) : x∈G5 B5 := by
  have hd : Disjoint d.toTypeRuSetup.Q (B5Image B5) := disjoint_of_coprime_natCard (by
    rw [d.ru2.card_Q d.card_Z,B5Image_card d.card_Z B5]
    decide)
  intro b hb
  have hBQ := d.ru2.six.normalized (map_subtype_le (B5 : Subgroup d.toTypeRuSetup.H) hb)
  have hQ : x*b*x⁻¹*b⁻¹∈d.toTypeRuSetup.Q := by
    have h := (mem_normalizer_iff.mp hBQ x⁻¹).mp (d.toTypeRuSetup.Q.inv_mem hx)
    simpa only [mul_assoc] using d.toTypeRuSetup.Q.mul_mem hx h
  have hB : x*b*x⁻¹*b⁻¹∈B5Image B5 :=
    (B5Image B5).mul_mem ((mem_normalizer_iff.mp hn b).mp hb) ((B5Image B5).inv_mem hb)
  have he : x*b*x⁻¹*b⁻¹=1 := disjoint_def.mp hd hQ hB
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp he)).symm

private theorem sourceU_not_Q
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    sourceU e∉d.toTypeRuSetup.Q := by
  obtain ⟨hu,hinv⟩ := source_inverter c B5 e hz hfive
  have huI := (source_marks_mem c e hz).2
  have huN := sourceI_le_normalizer B5 e hfive huI
  intro huQ
  have hc := normalizing_Q_centralizes B5 huQ huN
  let B := B5Image B5
  let : IsCyclic B := isCyclic_of_prime_card (B5Image_card d.card_Z B5)
  obtain ⟨b,hb⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic B)
  have ho : orderOf (b:G)=5 := (orderOf_coe b).trans (hb.trans (B5Image_card d.card_Z B5))
  have hconj : sourceU e*(b:G)*(sourceU e)⁻¹=(b:G) :=
    mul_inv_eq_of_eq_mul (hc b b.property).symm
  have hi : (b:G)=(b:G)⁻¹ := hconj.symm.trans (hinv b b.property)
  have hpow : (b:G)^2=1 := by
    calc (b:G)^2 = (b:G)*(b:G) := pow_two _
         _ = (b:G)⁻¹*(b:G) := congrArg (fun y:G => y*(b:G)) hi
         _ = 1 := inv_mul_cancel _
  have hh := orderOf_dvd_of_pow_eq_one hpow
  rw [ho] at hh
  norm_num at hh

private theorem odd_four (g : S5) (h4 : g^4=1) (h2 : g^2≠1) :
    g.sign≠1 := by
  have h : ∀ g : Equiv.Perm (Fin 5), g^4=1 → g^2≠1 → g.sign≠1 := by decide +kernel
  exact h g h4 h2

private theorem HC_fixed_odd_le_Q0 (a t : d.toTypeRuSetup.H)
    (ha : (a:G)∈d.toTypeRuSetup.HC)
    (ht : (d.ru2.quotientMap t).sign≠1) (hc : t*a=a*t) : (a:G)∈Q₀ d := by
  apply (mem_Q₀ d a).mpr
  apply mem_center_iff.mpr
  intro g
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.H) g
  change hatMap d b*hatMap d a=hatMap d a*hatMap d b
  have hker : d.ru2.quotientMap.ker≤d.toTypeRuSetup.K.subgroupOf d.toTypeRuSetup.H := by
    rw [d.ru2.quotient_kernel]
    exact comap_mono d.Q_le_K
  have hpre : (alternatingGroup (Fin 5)).comap d.ru2.quotientMap =
      d.toTypeRuSetup.K.subgroupOf d.toTypeRuSetup.H := by
    rw [← d.toTypeRuSetup.quotientMap_K,comap_map_eq_self hker]
  have hK (k : d.toTypeRuSetup.H) (hk : (d.ru2.quotientMap k).sign=1) :
      Commute (hatMap d k) (hatMap d a) := by
    have hkK : (k:G)∈d.toTypeRuSetup.K := by
      have he : k∈(alternatingGroup (Fin 5)).comap d.ru2.quotientMap :=
        Equiv.Perm.mem_alternatingGroup.mpr hk
      have hh : k∈d.toTypeRuSetup.K.subgroupOf d.toTypeRuSetup.H := hpre ▸ he
      exact hh
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (hatMap_eq_one d _).mpr (d.HC_commutator_K_mem_U ⟨a,ha⟩ ⟨k,hkK⟩)
  by_cases hb : (d.ru2.quotientMap b).sign=1
  · exact (hK b hb).eq
  · have hbm : (d.ru2.quotientMap b).sign=-1 := (Int.units_eq_one_or _).resolve_left hb
    have htm : (d.ru2.quotientMap t).sign=-1 := (Int.units_eq_one_or _).resolve_left ht
    have hbt : (d.ru2.quotientMap (b*t⁻¹)).sign=1 := by
      rw [map_mul,map_inv,map_mul,map_inv,hbm,htm]
      decide
    have h1 := (hK (b*t⁻¹) hbt).eq
    have h2 : hatMap d t*hatMap d a=hatMap d a*hatMap d t := by
      simpa only [map_mul] using congrArg (hatMap d) hc
    have he : hatMap d b=hatMap d (b*t⁻¹)*hatMap d t := by rw [← map_mul]; simp
    rw [he]
    calc
      hatMap d (b*t⁻¹)*hatMap d t*hatMap d a =
          hatMap d (b*t⁻¹)*(hatMap d a*hatMap d t) := by rw [mul_assoc,h2]
      _ = hatMap d a*(hatMap d (b*t⁻¹)*hatMap d t) := by rw [← mul_assoc,h1,mul_assoc]

/-- The literal cyclic diagonal belongs to the original Q₀, derived from
its genuine odd-root action on the original six-space quotient. -/
theorem sourceIz_le_Q0
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    sourceIz e≤Q₀ d := by
  let qG : G := e modelQ
  have hqI : qG∈sourceI e := mem_map_of_mem _ (mem_sup_right (mem_zpowers q))
  have hqH := sourceI_le_H c e hz hqI
  let qH : d.toTypeRuSetup.H := ⟨qG,hqH⟩
  have hq2 : qG^2=sourceU e := by
    have hh : modelQ^2=modelU := Subtype.ext q_square
    simpa only [qG,sourceU,map_pow,coe_pow] using congrArg (fun a:F => (a:G)) (congrArg e hh)
  have hq4 : qG^4=1 := by
    rw [show qG^4=(qG^2)^2 by rw [← pow_mul],hq2]
    exact (source_involution_marks c e hz).1
  have hodd : (d.ru2.quotientMap qH).sign≠1 := by
    apply odd_four _
    · rw [← map_pow,show qH^4=1 from Subtype.ext hq4,map_one]
    · intro he
      have hQ : qH^2∈d.ru2.quotientMap.ker := by
        rw [MonoidHom.mem_ker,map_pow,he]
      rw [d.ru2.quotient_kernel] at hQ
      have hh : qG^2∈d.toTypeRuSetup.Q := hQ
      rw [hq2] at hh
      exact sourceU_not_Q c B5 e hz hfive hh
  intro a ha
  have haCQ := sourceIz_le_CQ c B5 e hz hfive ha
  have haHC := (five_centralizer_le_HC B5) haCQ
  let aH : d.toTypeRuSetup.H := ⟨a,(show d.toTypeRuSetup.HC≤d.toTypeRuSetup.H from inf_le_left) haHC⟩
  apply HC_fixed_odd_le_Q0 aH qH haHC hodd
  exact Subtype.ext (show qG*a=a*qG from
    congrArg Subtype.val (I_comm e ⟨qG,hqI⟩ ⟨a,sourceIz_le_I e ha⟩))

/-- The source cyclic diagonal is exactly the original Q₀ intersection,
with both factors retained through the original endpoint map. -/
theorem sourceIz_eq_Q0_inf_I
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    sourceIz e=Q₀ d⊓sourceI e := by
  have hle : sourceIz e≤Q₀ d⊓sourceI e :=
    le_inf (sourceIz_le_Q0 c B5 e hz hfive) (sourceIz_le_I e)
  have hCQ : Q₀ d⊓sourceI e≤CQ B5 := by
    rintro x ⟨hx0,hxI⟩
    have hxQ := Q₀_le_Q d hx0
    exact ⟨hxQ,normalizing_Q_centralizes B5 hxQ (sourceI_le_normalizer B5 e hfive hxI)⟩
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  obtain ⟨f⟩ := q.quaternion
  have hne : Nat.card (Q₀ d⊓sourceI e : Subgroup G)≠8 := by
    intro h8
    have he : Q₀ d⊓sourceI e=CQ B5 :=
      eq_of_le_of_card_ge hCQ (by rw [h8,CQ_card B5 q])
    have hCQI : CQ B5≤sourceI e := he ▸ inf_le_right
    have hn : ¬ ∀ a b:QuaternionGroup 2,a*b=b*a := by decide +kernel
    apply hn
    intro a b
    apply f.symm.injective
    have hc : f.symm a*f.symm b=f.symm b*f.symm a := by
      apply Subtype.ext
      exact (show (f.symm a:G)*(f.symm b:G)=(f.symm b:G)*(f.symm a:G) from
        congrArg Subtype.val (I_comm e
          ⟨(f.symm a:G),hCQI (f.symm a).property⟩
          ⟨(f.symm b:G),hCQI (f.symm b).property⟩))
    simpa only [map_mul] using hc
  have hd : Nat.card (Q₀ d⊓sourceI e : Subgroup G)∣8 := CQ_card B5 q ▸ card_dvd_of_le hCQ
  have hdiv := Nat.mem_divisors.mpr ⟨hd,(by decide : 8≠0)⟩
  have hds : Nat.divisors 8={1,2,4,8} := by decide
  rw [hds] at hdiv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hdiv
  apply eq_of_le_of_card_ge hle
  rw [sourceIz_card e]
  omega

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer

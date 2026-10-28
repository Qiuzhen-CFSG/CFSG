module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenCentralTransvections
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenPointCoreSeparation
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.DistinctPointCentralFour

/-!
# Simultaneous commuting lifts at two original orthogonal points

The two central-four actors commute by the original point-core geometry.
Separating the two actual core hyperplanes supplies kernel corrections that
remove both squares while leaving the opposite actor fixed. The corrected
involutions therefore commute and retain their original quotient cosets and
all conjugation operators on the original elementary sixteen.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

omit [Finite G] in
private theorem corrected_order (A : Subgroup G) [IsElementaryAbelian 2 A]
    (x a c : G) (hx : x∈A) (ha : a∈A) (hc4 : orderOf c=4)
    (hc2 : c^2=x) (hmove : c*a*c⁻¹=x*a) : orderOf (a*c)=2 := by
  have ha2 := elemPow_eq_one_of_isElementaryAbelian (p:=2) a ha
  have hx2 := elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx
  have hs2 : (a*c)^2=1 := calc
    (a*c)^2=a*(c*a*c⁻¹)*c^2 := by simp only [pow_two]; group
    _=a*(x*a)*x := by rw [hmove,hc2]
    _=x*x := by
      rw [←mul_assoc a x a,setLike_mul_comm ha hx,mul_assoc x a a,←pow_two,ha2,mul_one]
    _=1 := by simpa only [pow_two] using hx2
  have hs1 : a*c≠1 := by
    intro he
    have hc : c=a⁻¹ := by
      calc
        c=a⁻¹*(a*c) := by group
        _=a⁻¹ := by rw [he,mul_one]
    have hcp := elemPow_eq_one_of_isElementaryAbelian (p:=2) c (hc ▸ A.inv_mem ha)
    have hd := orderOf_dvd_of_pow_eq_one hcp
    rw [hc4] at hd
    norm_num at hd
  exact orderOf_eq_prime hs2 hs1

omit [Finite G] in
private theorem corrected_action (A : Subgroup G) [IsElementaryAbelian 2 A]
    (a c : G) (ha : a∈A) (hc : c∈normalizer (A:Set G)) (v : G) (hv : v∈A) :
    (a*c)*v*(a*c)⁻¹=c*v*c⁻¹ := by
  have hm : c*v*c⁻¹∈A := (mem_normalizer_iff.mp hc v).mp hv
  calc
    (a*c)*v*(a*c)⁻¹=a*(c*v*c⁻¹)*a⁻¹ := by group
    _=(c*v*c⁻¹)*a*a⁻¹ := by rw [setLike_mul_comm ha hm]
    _=c*v*c⁻¹ := mul_inv_cancel_right _ _

/-- Orthogonal distinct points yield simultaneous commuting involutory
representatives of their original point-core actors in the same kernel cosets. -/
theorem TypeAt.sixteen_orthogonal_involutory_lifts (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A=16)
    (hCA : centralizer (A:Set G)=A)
    (hpure : ∀ x∈A,x≠1 → IsConj x z)
    (hpoints : ∀ x∈A,x≠1 →
      Nat.card (A⊓(involutionCentralizer x).pCoreIn 2:Subgroup G)=8)
    (x y : G) (hx : x∈A) (hy : y∈A) (hx1 : x≠1) (hy1 : y≠1)
    (hxy : x≠y) (horth : y∈(involutionCentralizer x).pCoreIn 2) :
    ∃ c d a b : G, orderOf c=4 ∧ orderOf d=4 ∧ c^2=x ∧ d^2=y ∧
      c∈(center ((involutionCentralizer x).pCoreIn 2)).map
        ((involutionCentralizer x).pCoreIn 2).subtype ∧
      d∈(center ((involutionCentralizer y).pCoreIn 2)).map
        ((involutionCentralizer y).pCoreIn 2).subtype ∧ Commute c d ∧
      a∈A ∧ a∈(involutionCentralizer y).pCoreIn 2 ∧ a∉(involutionCentralizer x).pCoreIn 2 ∧
      b∈A ∧ b∈(involutionCentralizer x).pCoreIn 2 ∧ b∉(involutionCentralizer y).pCoreIn 2 ∧
      orderOf (a*c)=2 ∧ orderOf (b*d)=2 ∧ Commute (a*c) (b*d) ∧
      ∃ (hcN : c∈normalizer (A:Set G)) (hdN : d∈normalizer (A:Set G))
        (hsN : a*c∈normalizer (A:Set G)) (htN : b*d∈normalizer (A:Set G)),
        (QuotientGroup.mk (⟨a*c,hsN⟩:normalizer (A:Set G)) :
          normalizer (A:Set G) ⧸ A.subgroupOf (normalizer (A:Set G)))=
          QuotientGroup.mk (⟨c,hcN⟩:normalizer (A:Set G)) ∧
        (QuotientGroup.mk (⟨b*d,htN⟩:normalizer (A:Set G)) :
          normalizer (A:Set G) ⧸ A.subgroupOf (normalizer (A:Set G)))=
          QuotientGroup.mk (⟨d,hdN⟩:normalizer (A:Set G)) ∧
        (∀ v∈A,(a*c)*v*(a*c)⁻¹=c*v*c⁻¹) ∧
        (∀ v∈A,(b*d)*v*(b*d)⁻¹=d*v*d⁻¹) := by
  obtain ⟨c,hc4,hc2,hcZ,_,hcN,_,hcfix,hcmove⟩ :=
    h.sixteen_central_point_transvection A hA hCA hpure hpoints x hx hx1
  obtain ⟨d,hd4,hd2,hdZ,_,hdN,_,hdfix,hdmove⟩ :=
    h.sixteen_central_point_transvection A hA hCA hpure hpoints y hy hy1
  obtain ⟨X,hxT⟩ := h.exists_typeAt_of_isConj x (hpure x hx hx1)
  obtain ⟨Y,hyT⟩ := h.exists_typeAt_of_isConj y (hpure y hy hy1)
  have horth' : x∈(involutionCentralizer y).pCoreIn 2 :=
    (h.conjugate_point_core_reciprocal x y (hpure x hx hx1) (hpure y hy hy1)).mp horth
  have hcy : c∈involutionCentralizer y := mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp (hcfix y ⟨hy,horth⟩))
  have hdx : d∈involutionCentralizer x := mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp (hdfix x ⟨hx,horth'⟩))
  have hcd := distinct_point_central_four_commute hxT hyT hxy c d hc4 hd4 hc2 hd2 hcZ hdZ hcy hdx
  obtain ⟨a,ha,haY,haX⟩ := h.sixteen_point_core_separator A hA hpure hpoints x y hx hy hx1 hy1 hxy
  obtain ⟨b,hb,hbX,hbY⟩ := h.sixteen_point_core_separator A hA hpure hpoints y x hy hx hy1 hx1 hxy.symm
  have hs2 := corrected_order A x a c hx ha hc4 hc2 (hcmove a ha haX)
  have ht2 := corrected_order A y b d hy hb hd4 hd2 (hdmove b hb hbY)
  have hab : Commute a b := setLike_mul_comm ha hb
  have had : Commute a d := (mul_inv_eq_iff_eq_mul.mp (hdfix a ⟨ha,haY⟩)).symm
  have hcb : Commute c b := mul_inv_eq_iff_eq_mul.mp (hcfix b ⟨hb,hbX⟩)
  have hst : Commute (a*c) (b*d) := (hab.mul_right had).mul_left (hcb.mul_right hcd)
  have hsN : a*c∈normalizer (A:Set G) := (normalizer (A:Set G)).mul_mem (A.le_normalizer ha) hcN
  have htN : b*d∈normalizer (A:Set G) := (normalizer (A:Set G)).mul_mem (A.le_normalizer hb) hdN
  have same_coset (a c : G) (ha : a∈A) (hcN : c∈normalizer (A:Set G))
      (hsN : a*c∈normalizer (A:Set G)) :
      (QuotientGroup.mk (⟨a*c,hsN⟩:normalizer (A:Set G)) :
        normalizer (A:Set G) ⧸ A.subgroupOf (normalizer (A:Set G)))=
        QuotientGroup.mk (⟨c,hcN⟩:normalizer (A:Set G)) := by
    let q := QuotientGroup.mk' (A.subgroupOf (normalizer (A:Set G)))
    have hqa : q ⟨a,A.le_normalizer ha⟩=1 := (QuotientGroup.eq_one_iff _).mpr ha
    change q ((⟨a,A.le_normalizer ha⟩:normalizer (A:Set G))*⟨c,hcN⟩)=q ⟨c,hcN⟩
    rw [map_mul,hqa,one_mul]
  exact ⟨c,d,a,b,hc4,hd4,hc2,hd2,hcZ,hdZ,hcd,ha,haY,haX,hb,hbX,hbY,hs2,ht2,hst,
    hcN,hdN,hsN,htN,same_coset a c ha hcN hsN,same_coset b d hb hdN htN,
    corrected_action A a c ha hcN,corrected_action A b d hb hdN⟩

end CFSG.Quasithin.HigmanSims

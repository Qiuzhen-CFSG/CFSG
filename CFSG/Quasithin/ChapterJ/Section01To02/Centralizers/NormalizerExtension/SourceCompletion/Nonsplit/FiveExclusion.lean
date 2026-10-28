module
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Five
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.Lifting

/-!
# The fixed five-element obstruction to z-fusion

The actual centralizer of a Sylow five-subgroup of H has order 1000.
If an element centralizing a five-element of C_G(B) were conjugate to z,
that five-element would transport into H. Its centralizer would then contain
the transported B of order three, contradicting the order 1000.
This uses the completed source five-centralizer theorem with the literal maps.

Source: Aschbacher–Smith J.2.7(6–7), printed p.436 (PDF p.447).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

include c in
public theorem five_centralizer_card_source (P : Sylow 5 d.toTypeRuSetup.H) :
    Nat.card (G5 P)=1000 := by
  obtain ⟨q⟩ := c.fiveQuaternionData_source P
  rw [c.G5_card P d.card_Z q, SourceCompletion.five_oddPart_card c P]

public theorem not_z_fused_of_fixed_cubic_five_source (x y : G)
    (hyGB : y∈c.GB) (hy5 : orderOf y=5) (hxy : Commute x y) : ¬IsConj x c.z := by
  intro hx
  obtain ⟨g,hg⟩ := isConj_iff.mp hx
  let e := MulAut.conj g
  have eyH : e y ∈ d.toTypeRuSetup.H := by
    rw [c.H_eq_centralizer_z,mem_centralizer_singleton_iff,←hg]
    exact (hxy.map e.toMonoidHom).symm.eq
  let yH : d.toTypeRuSetup.H := ⟨e y,eyH⟩
  have hyH : orderOf yH=5 := by
    exact (Subgroup.orderOf_coe yH).symm.trans ((orderOf_injective e.toMonoidHom e.injective y).trans hy5)
  have hp : IsPGroup 5 (zpowers yH) := IsPGroup.of_card (n:=1) (by rw [Nat.card_zpowers,hyH];rfl)
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have heq : (zpowers y).map e.toMonoidHom = B5Image P := by
    rw [e.toMonoidHom.map_zpowers]
    apply eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      exact mem_map_of_mem d.toTypeRuSetup.H.subtype (hP (mem_zpowers yH))
    · rw [Nat.card_zpowers,orderOf_injective e.toMonoidHom e.injective,hy5,
        B5Image_card d.card_Z P]
  have hBcent : c.B ≤ centralizer ((zpowers y : Subgroup G):Set G) := by
    rw [zpowers_eq_closure,centralizer_closure]
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (hyGB b hb)
  have hd := card_dvd_of_le hBcent
  have hcard : Nat.card (centralizer ((zpowers y : Subgroup G):Set G)) = 1000 := by
    have hcent : (centralizer ((zpowers y : Subgroup G):Set G)).map e.toMonoidHom = G5 P := by
      rw [Theory.Quasithin.map_centralizer,heq]
    have hc := card_map_of_injective (f := e.toMonoidHom) (K := centralizer ((zpowers y : Subgroup G):Set G)) e.injective
    rw [hcent,c.five_centralizer_card_source P] at hc
    exact hc.symm
  rw [SourceCompletion.B_card c,hcard] at hd
  norm_num at hd



end CFSG.Quasithin.ChapterJ.Centralizers.Choices

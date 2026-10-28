module
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.ConjugateCore
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.SourceCoordinates
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.WeakClosure
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# The actual weak-closure witness in 13.9.10

A conjugate of z in the first dihedral factor centralizes the S4 factor.
Its four-core therefore lies in the conjugate B∩Q. Together they generate
that order-eight intersection. Their centralizer inside the local product has
at least sixteen elements and hence is the conjugate B, lying in N_G(B).
Weak closure contradicts the marked conjugate being outside B.

All orders, quotient containment and fusion transport are derived from the
original source configuration; only the actual local splitting data remain
inputs, supplied independently by the natural five-point module.
Source: Aschbacher--Smith, 13.9.10, printed p.973.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
open scoped IsMulCommutative
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

omit [Finite G] in
private theorem fourCore_card (X:Subgroup G) (e:X≃*S4) : Nat.card (X.pCoreIn 2)=4 := by
  rw [pCoreIn,card_map_of_injective X.subtype_injective,Nat.card_congr ((pCore 2 X).equivMapOfInjective e.toMonoidHom e.injective).toEquiv,
    pCore_map_iso,←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq,
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card]

omit [Finite G] in
private theorem fourCore_commutative (X:Subgroup G) (e:X≃*S4) : IsMulCommutative (X.pCoreIn 2) := by
  let V:=pCore 2 X
  have he:V.map e.toMonoidHom=Theory.SpecificGroups.SymmetricSix.DuadCalculation.core := by
    rw [pCore_map_iso,Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
  let f:V≃*Theory.SpecificGroups.SymmetricSix.DuadCalculation.core :=
    (V.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr he)
  have hv:IsMulCommutative V:=⟨⟨fun x y=>f.injective (by rw [map_mul,map_mul,mul_comm])⟩⟩
  let :=hv
  exact Subgroup.map_isMulCommutative (f:=X.subtype) (H:=V)

omit [Finite G] in
private theorem dihedral_involution_centralizer_card (R:Subgroup G) (e:R≃*D8)
    (a:R) (ha:orderOf a=2) : 4≤Nat.card (centralizer ({a}:Set R)) := by
  have hc:Nat.card (centralizer ({a}:Set R))=Nat.card (centralizer ({e a}:Set D8)) :=
    Nat.card_congr (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e a).toEquiv
  rw [hc]
  have ho:orderOf (e a)=2:=(orderOf_injective e.toMonoidHom e.injective a).trans ha
  let inst (a:D8) : DecidablePred (·∈centralizer ({a}:Set D8)) := fun x=>
    decidable_of_iff (x*a=a*x) mem_centralizer_singleton_iff.symm
  have hh:∀a:D8,a^2=1→a≠1→4≤Fintype.card (centralizer ({a}:Set D8)) := by decide +kernel
  rw [Nat.card_eq_fintype_card]
  exact hh (e a) (by rw [←ho];exact pow_orderOf_eq_one _) (by intro h;rw [h,orderOf_one] at ho;omega)

/-- The actual local product witness contradicts weak closure of B. -/
theorem false_of_alignment_split_witness
    {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (g:G) (R X:Subgroup G) (eR:R≃*D8) (eX:X≃*S4)
    (hdisj:Disjoint R X) (hcomm:R≤centralizer (X:Set G))
    (hRK:R≤normalizer (m.B:Set G)) (hXK:X≤normalizer (m.B:Set G))
    (haR:g*m.z*g⁻¹∈R) (haB:g*m.z*g⁻¹∉m.B)
    (hVB:X.pCoreIn 2≤m.B)
    (hfusion:∀x∈X.pCoreIn 2,x≠1→IsConj m.t x) : False := by
  let a:=g*m.z*g⁻¹
  let V:=X.pCoreIn 2
  have ha2:orderOf a=2:=((MulAut.conj g).orderOf_eq m.z).trans m.z_order
  have hVX:V≤X:=pCoreIn_le 2 X
  have hXC:X≤centralizer ({a}:Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hcomm haR) x hx)
  have hVI:V≤(m.B⊓m.core).map (MulAut.conj g).toMonoidHom :=
    m.symmetricFour_core_le_conjugate_intersection hG g X eX hXC hfusion
  have haI:a∈(m.B⊓m.core).map (MulAut.conj g).toMonoidHom :=
    mem_map_of_mem _ ⟨m.z_mem_B,m.z_mem_core⟩
  have hLV:Disjoint (zpowers a) V := by
    apply disjoint_def.mpr
    intro x hx hV
    classical
    have hcases:x=1∨x=a := by
      rw [mem_zpowers_iff_mem_range_orderOf] at hx
      obtain ⟨i,hi,he⟩:=Finset.mem_image.mp hx
      have hi2:i<2:=by simpa only [Finset.mem_range,ha2] using hi
      have hh:i=0∨i=1:=by omega
      rcases hh with hh|hh
      · left;simpa only [hh,pow_zero] using he.symm
      · right;simpa only [hh,pow_one] using he.symm
    rcases hcases with h|h
    · exact h
    · have haV:a∈m.B:=h ▸ hVB hV
      exact (haB haV).elim
  have hLcomm:zpowers a≤centralizer (V:Set G) :=
    (zpowers_le.mpr haR).trans (hcomm.trans (centralizer_le hVX))
  have hUcard:Nat.card (zpowers a⊔V:Subgroup G)=8 := by
    obtain ⟨e,he⟩:=exists_mulEquiv_prod_sup_of_disjoint_of_commuting (zpowers a) V hLV hLcomm
    rw [←Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_zpowers,ha2,fourCore_card X eX]
  have hU : zpowers a⊔V=(m.B⊓m.core).map (MulAut.conj g).toMonoidHom := by
    apply eq_of_le_of_card_ge (sup_le (zpowers_le.mpr haI) hVI)
    rw [card_map_of_injective (MulAut.conj g).injective,m.card_B_inf_core (hG.evenCharacteristic d.T),hUcard]
  let D0:=R⊓centralizer ({a}:Set G)
  let D:=D0⊔V
  have hD0R:D0≤R:=inf_le_left
  have hD0V:Disjoint D0 V:=hdisj.mono hD0R hVX
  have hD0comm:D0≤centralizer (V:Set G):=hD0R.trans (hcomm.trans (centralizer_le hVX))
  have hDcard:16≤Nat.card D := by
    obtain ⟨e,he⟩:=exists_mulEquiv_prod_sup_of_disjoint_of_commuting D0 V hD0V hD0comm
    have hD0card:4≤Nat.card D0 := by
      have he:(centralizer ({(⟨a,haR⟩:R)}:Set R)).map R.subtype=D0 :=
        map_subtype_centralizer_singleton _ _
      rw [←he,card_map_of_injective R.subtype_injective]
      exact dihedral_involution_centralizer_card R eR ⟨a,haR⟩ ((orderOf_coe _).symm.trans ha2)
    change 16≤Nat.card (D0⊔V:Subgroup G)
    rw [←Nat.card_congr e.toEquiv,Nat.card_prod,fourCore_card X eX]
    omega
  have hDC:D≤centralizer ((m.B⊓m.core).map (MulAut.conj g).toMonoidHom:Set G) := by
    rw [←hU]
    apply le_centralizer_iff.mpr
    apply sup_le
    · apply zpowers_le.mpr
      apply mem_centralizer_iff.mpr
      intro x hx
      have hn:D≤centralizer ({a}:Set G):=sup_le inf_le_right (hVX.trans hXC)
      exact mem_centralizer_singleton_iff.mp (hn hx)
    · apply le_centralizer_iff.mp
      exact sup_le hD0comm (le_centralizer_iff_isMulCommutative.mpr (fourCore_commutative X eX))
  have hDC':D≤m.B.map (MulAut.conj g).toMonoidHom := by
    have hh:=FusionAlignment.centralizer_conjugate_intersection m.B m.core
      (m.centralizer_B_inf_core (hG.evenCharacteristic d.T)) g
    change centralizer ((m.B.map (MulAut.conj g).toMonoidHom⊓m.core.map (MulAut.conj g).toMonoidHom:Subgroup G):Set G)=_ at hh
    rw [←map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective] at hh
    rwa [hh] at hDC
  have hBD:D=m.B.map (MulAut.conj g).toMonoidHom := by
    apply eq_of_le_of_card_ge hDC'
    rw [card_map_of_injective (MulAut.conj g).injective,m.card_elementaryGroup false false]
    exact hDcard
  have hDK:D≤normalizer (m.B:Set G):=sup_le (hD0R.trans hRK) (hVX.trans hXK)
  have hfix:=d.T.conjugate_eq_of_le_normalizer_of_weakly_closed m.B
    (m.elementaryGroup_le_sylow false false) (m.diagonal_weakly_closed false) g (hBD ▸ hDK)
  exact haB (hfix ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom m.z_mem_B)
end CFSG.Quasithin.Chapter13.Section09.Marking

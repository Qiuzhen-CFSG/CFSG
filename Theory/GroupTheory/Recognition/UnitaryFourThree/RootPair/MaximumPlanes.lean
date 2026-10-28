module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.BinarySylow

/-!
# Large elementary subgroups of the original Sylow lie in R

An actor outside R has fixed quotient plane equal to the original core
factor. If an elementary subgroup of order at least16 met that coset,
its intersection with R would have order at least8 and would centralize
the actor. Adjoining E would then fill the noncommutative order16 factor
with a commutative group, a contradiction. This avoids a large finite
census of the order128 Sylow subgroup.

Source: Aschbacher, *Sporadic Groups* (1994),45.5(3), printed p.244.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace RootPair
variable (P : RootPair z)

theorem N_normalizes_R (h : IsType z) : P.N≤normalizer (P.R:Set G) := by
  rw [P.R_eq_centralizer_E h]
  exact normalizer_le_normalizer_centralizer P.E

/-- The part of R fixed by an actor outside R lies in the original core factor. -/
theorem centralizer_in_R_le_leftCore (h : IsType z) (a:G) (ha : a∈P.T) (haR : a∉P.R) :
    P.R⊓centralizer a≤P.leftCore := by
  have hn : P.R≤normalizer (core z:Set G) :=
    (P.R_le_double_centralizer.trans inf_le_left).trans CentralizerHypothesis.centralizer_normalizes_core
  have hp : a∈(P.R:Set G)*(core z:Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right P.R (core z) hn]
    exact ha
  obtain ⟨r,hr,q,hq,rfl⟩ := hp
  have hqA : q∉P.leftCore := by
    intro hqa
    exact haR (P.R.mul_mem hr (mem_sup_left hqa))
  intro x hx
  apply (P.reflection_fixed_coset_iff h q hq hqA x hx.1).mp
  have hcomm : x*(r*q)=(r*q)*x := mem_centralizer_singleton_iff.mp hx.2
  have he : ⁅q,x⁆=r⁻¹*⁅x,r⁆*r := by
    have hh := congrArg (fun y:G=>r⁻¹*y*q⁻¹*x⁻¹) hcomm
    simp only [commutatorElement_def] at *
    calc
      q*x*q⁻¹*x⁻¹ = r⁻¹*(x*(r*q))*q⁻¹*x⁻¹ := by rw [hcomm]; group
      _ = r⁻¹*(x*r*x⁻¹*r⁻¹)*r := by group
  rw [he]
  have hc : ⁅x,r⁆∈P.E := P.R_commutator_le_E h (commutator_mem_commutator hx.1 hr)
  have hri : r⁻¹∈P.N := (P.N).inv_mem (P.T_le_N h (mem_sup_left hr))
  simpa only [inv_inv] using (mem_normalizer_iff.mp hri _).mp hc

theorem leftCore_not_commutative (h : IsType z) : ¬IsMulCommutative P.leftCore := by
  obtain ⟨a,b,ha,hb,_,_,hs,_⟩ := P.exists_left_frame h
  intro hc
  let := hc
  have he : b*a=a*b := congrArg Subtype.val
    ((IsMulCommutative.is_comm (M:=P.leftCore)).comm ⟨b,hb⟩ ⟨a,ha⟩)
  have hz1 : z=1 := mul_left_cancel (by simpa only [mul_one] using hs.symm.trans he)
  have hi := h.involution
  simp [hz1] at hi

/-- Every elementary subgroup of T of order at least sixteen is already in R. -/
theorem large_elementary_le_R (h : IsType z) (V:Subgroup G) (hVT : V≤P.T)
    [IsElementaryAbelian 2 V] (hV : 16≤Nat.card V) : V≤P.R := by
  by_contra hnV
  obtain ⟨a,ha,haR⟩ := SetLike.not_le_iff_exists.mp hnV
  let D:=V⊓P.R
  have hDC : D≤centralizer a := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      ((IsMulCommutative.is_comm (M:=V)).comm ⟨x,hx.1⟩ ⟨a,ha⟩))
  have hDA : D≤P.leftCore := (le_inf inf_le_right hDC).trans
    (P.centralizer_in_R_le_leftCore h a (hVT ha) haR)
  have hDn : V≤normalizer (P.R:Set G) := hVT.trans ((P.T_le_N h).trans (P.N_normalizes_R h))
  have hcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes P.R V hDn
  rw [inf_comm,sup_comm,P.R_card h] at hcard
  have hjoin : Nat.card (V⊔P.R:Subgroup G)≤128 := by
    have hh := Nat.card_le_card_of_injective (inclusion (sup_le hVT (show P.R≤P.T from le_sup_left)))
      (inclusion_injective _)
    rwa [P.T_card h] at hh
  have hD8 : 8≤Nat.card D := by
    change 64*Nat.card V=Nat.card D*Nat.card (V⊔P.R:Subgroup G) at hcard
    nlinarith
  have hDElt : D⊓P.E≠P.E := by
    intro he
    have hEC : P.E≤centralizer a := he ▸ (inf_le_left.trans hDC)
    have haC : a∈Subgroup.centralizer (P.E:Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hEC hx)
    exact haR ((P.R_eq_centralizer_E h).ge haC)
  have hDE2 : Nat.card (D⊓P.E:Subgroup G)≤2 := by
    have hd : Nat.card (D⊓P.E:Subgroup G)∣4 := by
      simpa only [P.E_card h] using card_dvd_of_le (show D⊓P.E≤P.E from inf_le_right)
    have hn4 : Nat.card (D⊓P.E:Subgroup G)≠4 := by
      intro hc
      apply hDElt
      exact eq_of_le_of_card_ge inf_le_right (by rw [hc,P.E_card h])
    have hle := Nat.le_of_dvd (by decide : 0<4) hd
    have hn3 : Nat.card (D⊓P.E:Subgroup G)≠3 := by
      intro hc
      rw [hc] at hd
      norm_num at hd
    omega
  have hEC : P.E≤Subgroup.centralizer (D:Set G) := by
    intro e he d hd
    exact (P.centralizer_R_eq_E h).ge he d hd.2
  have hEn : P.E≤normalizer (D:Set G) := hEC.trans (centralizer_le_normalizer _)
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes D P.E hEn
  rw [P.E_card h] at hprod
  have hsupA : D⊔P.E≤P.leftCore := sup_le hDA (P.E_le_leftCore h)
  have hsup16 : Nat.card (D⊔P.E:Subgroup G)≤16 := by
    have hh := Nat.card_le_card_of_injective (inclusion hsupA) (inclusion_injective hsupA)
    rwa [P.leftCore_card h] at hh
  have heq : D⊔P.E=P.leftCore := eq_of_le_of_card_ge hsupA (by
    rw [P.leftCore_card h]
    nlinarith)
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective
    (inclusion (show D≤V from inf_le_left)) (inclusion_injective _)
  let : IsElementaryAbelian 2 P.E := P.E_elementary h
  have hab : IsElementaryAbelian 2 (D⊔P.E:Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hEC
  rw [heq] at hab
  let := hab
  exact P.leftCore_not_commutative h inferInstance

end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree

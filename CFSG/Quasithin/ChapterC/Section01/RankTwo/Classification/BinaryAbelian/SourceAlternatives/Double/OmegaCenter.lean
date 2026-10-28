module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.Reduction
public import Theory.GroupTheory.SylowCentralizerComplement
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Correcting Sylow-fixed elements in the doubled MS branch

The self-centralizing two-core puts each Sylow-fixed element in O₂(J).
Its displacement by the component therefore lies in the actual commutator
core. Averaging over the odd number of component Sylow cosets gives a fixed
representative modulo this elementary core. When the component-fixed core
is trivial, that correction is unique; normality of the component makes the
correction fixed by the whole original Sylow subgroup.

This supplies the omega-center lifting step in Aschbacher–Smith C.1.34(2),
combined manuscript (1 March 2004), printed p.137. The original-group
consumer in `MarkedMS.LinearThree.AbelianSourceDouble` discharges the
exponent and fixed-kernel hypotheses from its order-64 source quotient.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}

/-- Unique central corrections preserve the literal Sylow centralizer. -/
theorem Input.core_sylow_fixed_correction (h : Input κ L R)
    (he : IsElementaryAbelian 2 (commutatorCore L)) (hf : coreFixed L = ⊥)
    (S : Sylow 2 J) (z : J) (hz : z ∈ centralizer (S : Set J)) :
    ∃ q ∈ commutatorCore L ⊓ centralizer (S : Set J),
      q⁻¹ * z ∈ centralizer (L : Set J) := by
  let := he
  let := h.component_normal
  let D := commutatorCore L
  have hDN : D.Normal := inferInstance
  have hzN : z ∈ pCore 2 J := h.core_selfCentralizing
    (centralizer_le (pCore_isPGroup.le_sylow_of_normal S) hz)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal L
  obtain ⟨v,hv,hvc⟩ := fixed_coset_of_sylow L D
    (by rw [normalizer_eq_top]; exact le_top)
    (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv) P z
    (fun l hl => by
      change ⁅l,z⁆ ∈ ⁅pCore 2 J,L⁆
      rw [commutator_comm]
      exact commutator_mem_commutator hl hzN)
    (fun l hl => hz l (show l ∈ (S : Subgroup J).subgroupOf L from hP ▸ hl))
  let q : J := v⁻¹
  have hq : q ∈ D := D.inv_mem hv
  have hc : q⁻¹ * z ∈ centralizer (L : Set J) := by simpa only [q, inv_inv] using hvc
  refine ⟨q,⟨hq,?_⟩,hc⟩
  intro s hs
  let q' : J := s * q * s⁻¹
  let c : J := q⁻¹ * z
  let c' : J := s * c * s⁻¹
  have hq' : q' ∈ D := hDN.conj_mem q hq s
  have hc' : c' ∈ centralizer (L : Set J) :=
    (inferInstance : (centralizer (L : Set J)).Normal).conj_mem c hc s
  have hprod : q' * c' = q * c := by
    calc
      q' * c' = s * (q * c) * s⁻¹ := by dsimp [q',c']; group
      _ = s * z * s⁻¹ := by simp only [c,mul_inv_cancel_left]
      _ = z := by rw [hz s hs,mul_inv_cancel_right]
      _ = q * c := (mul_inv_cancel_left q z).symm
  have hd : q⁻¹ * q' = c * c'⁻¹ := by
    calc
      q⁻¹ * q' = q⁻¹ * (q' * c') * c'⁻¹ := by group
      _ = q⁻¹ * (q * c) * c'⁻¹ := by rw [hprod]
      _ = c * c'⁻¹ := by group
  have hfixed : (⟨q⁻¹ * q', D.mul_mem (D.inv_mem hq) hq'⟩ : D) ∈ coreFixed L := by
    change q⁻¹ * q' ∈ centralizer (L : Set J)
    rw [hd]
    exact (centralizer (L : Set J)).mul_mem hc ((centralizer _).inv_mem hc')
  have hone : q⁻¹ * q' = 1 := congrArg Subtype.val (show
      (⟨q⁻¹ * q', D.mul_mem (D.inv_mem hq) hq'⟩ : D) ∈ (⊥ : Subgroup D) from hf ▸ hfixed)
  have heq : q' = q := (inv_mul_eq_one.mp hone).symm
  exact (mul_inv_eq_iff_eq_mul.mp heq)

end CFSG.Quasithin.ChapterC.BinaryMS

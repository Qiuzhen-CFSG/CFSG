module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head
public import Theory.GroupTheory.SylowCentralizerComplement
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Sylow-fixed corrections in the center of the original MS core

An element centralizing a Sylow subgroup centralizes the ambient two-core
and lies in it by characteristic two. Its component commutators therefore
lie in the center of the actual commutator core. When that center is binary
elementary, odd-index averaging gives a component-fixed representative.
If the center has no component-fixed points, uniqueness makes the correction
fixed by the entire original Sylow subgroup.

The distance-four natural center supplies these two hypotheses. The literal
SmallMSPair application is in LinearThree.DistanceFourOriginalAction. This
is the omega-center lifting step toward C.1.34(3)'s radical inequality;
qt-rank-two-ms93 retains its remaining parabolic argument and final assembly.
Source: Aschbacher--Smith C.1.34(3), printed pp.136--137, and the final remark
on cases (11)--(13) of Meierfrankenfeld--Stellmacher (1993), printed p.831.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}

/-- Unique central corrections preserve the original Sylow centralizer. -/
theorem Input.center_sylow_fixed_correction (h : Input κ L R)
    (he : IsElementaryAbelian 2 (center (commutatorCore L)))
    (hf : (center (commutatorCore L)).map (commutatorCore L).subtype ⊓
      centralizer (L : Set J) = ⊥)
    (S : Sylow 2 J) (z : J) (hz : z ∈ centralizer (S : Set J)) :
    ∃ q ∈ (center (commutatorCore L)).map (commutatorCore L).subtype ⊓
      centralizer (S : Set J), q⁻¹ * z ∈ centralizer (L : Set J) := by
  let := he
  let := h.component_normal
  let Q := commutatorCore L
  let D := (center Q).map Q.subtype
  have hQN : Q.Normal := inferInstance
  have hDN : D.Normal := inferInstance
  have hQE : Q ≤ pCore 2 J := commutator_le_left _ _
  have hzE : z ∈ centralizer (pCore 2 J : Set J) :=
    centralizer_le (pCore_isPGroup.le_sylow_of_normal S) hz
  have hzN : z ∈ pCore 2 J := h.core_selfCentralizing hzE
  have heD : IsElementaryAbelian 2 D := IsElementaryAbelian.map Q.subtype
  let := heD
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal L
  obtain ⟨v,hv,hvc⟩ := fixed_coset_of_sylow L D
    (by rw [normalizer_eq_top]; exact le_top)
    (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv) P z
    (fun l hl => by
      have hcQ : ⁅l,z⁆ ∈ Q := by
        change ⁅l,z⁆ ∈ ⁅pCore 2 J,L⁆
        rw [commutator_comm]
        exact commutator_mem_commutator hl hzN
      have hcE : ⁅l,z⁆ ∈ centralizer (pCore 2 J : Set J) := by
        exact (centralizer (pCore 2 J : Set J)).mul_mem
          ((inferInstance : (centralizer (pCore 2 J : Set J)).Normal).conj_mem z hzE l)
          ((centralizer _).inv_mem hzE)
      exact ⟨⟨⁅l,z⁆,hcQ⟩,mem_center_iff.mpr
        (fun x => Subtype.ext (hcE x (hQE x.property))),rfl⟩)
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
  have hone : q⁻¹ * q' = 1 := by
    apply show q⁻¹ * q' ∈ (⊥ : Subgroup J) → q⁻¹ * q' = 1 from id
    rw [← hf]
    refine ⟨D.mul_mem (D.inv_mem hq) hq',?_⟩
    rw [hd]
    exact (centralizer _).mul_mem hc ((centralizer _).inv_mem hc')
  have heq : q' = q := (inv_mul_eq_one.mp hone).symm
  exact mul_inv_eq_iff_eq_mul.mp heq
end CFSG.Quasithin.ChapterC.BinaryMS

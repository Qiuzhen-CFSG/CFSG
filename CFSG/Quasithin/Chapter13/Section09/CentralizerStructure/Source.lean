module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.QuotientRecognition
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.Overgroups
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.AmbientFusion
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.CoreOvergroups
public import Theory.GroupTheory.ThreeIndexTwoOvergroups
import all CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.Overgroups
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.CoreConjugate
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.LocalCentralizer
/-!
# The original centralizer structure in quasithin 13.9.8

The native wreath coordinates construct Q, its quaternion factors, and its
three overgroups in the original Sylow. The preceding ambient fusion
results construct PairData and prevent t from fusing with z. These inputs
prove Q normal and identify the literal quotient C_G(z)/Q with S₃ × C₂.

Its 2-core has order 64 and moves a quaternion factor. The three-overgroup
argument excludes the factor normalizer, and weak closure excludes AQ;
therefore O₂(C_G(z)) = BQ. Weak closure of B now gives B normal in C_G(z).
The final source theorem retains only the genuine preceding strict-growth
statement 13.9.5, together with the original simple QTKE hypothesis.

The internal import of Overgroups unfolds its source weak-closure predicate
without changing that earlier module's public boundary.
Source: Aschbacher–Smith, 13.9.8, printed p.972 (PDF p.989).
-/
public section
namespace CFSG.Quasithin.Chapter13.Section09
open Subgroup CentralizerStructure
variable {G : Type*} [Group G] [Finite G] {d : Configuration G}

private theorem three_overgroups {p : PairData d} (q : CoreData p)
    [(q.Q.subgroupOf p.C).Normal] (E1 E2 E3 E : Subgroup G)
    (h1 : q.Q ≤ E1) (h2 : q.Q ≤ E2) (h3 : q.Q ≤ E3) (hE : q.Q ≤ E)
    (h1T : E1 ≤ (d.T : Subgroup G)) (h2T : E2 ≤ (d.T : Subgroup G))
    (h3T : E3 ≤ (d.T : Subgroup G)) (hET : E ≤ (d.T : Subgroup G))
    (hc1 : Nat.card E1 = 64) (hc2 : Nat.card E2 = 64)
    (hc3 : Nat.card E3 = 64) (hcE : Nat.card E = 64)
    (hne12 : E1 ≠ E2) (hne13 : E1 ≠ E3) (hne23 : E2 ≠ E3) :
    E = E1 ∨ E = E2 ∨ E = E3 := by
  let T : Subgroup G := d.T
  let N := q.Q.subgroupOf T
  have hnC : p.C ≤ normalizer (q.Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer q.le_C).mp inferInstance
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer q.le_T).mpr (p.z_central.trans hnC)
  have hncard : Nat.card N = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe q.le_T).toEquiv).trans q.card
  have htcard : Nat.card T = 128 := d.card_sylow
  have hquot : Nat.card (T ⧸ N) = 4 := by
    have hh := card_eq_card_quotient_mul_card_subgroup N
    rw [hncard,htcard] at hh
    omega
  have hi (A : Subgroup G) (hQA : q.Q ≤ A) (hAT : A ≤ T) (hcard : Nat.card A = 64) :
      N.relIndex (A.subgroupOf T) = 2 := by
    have hNA : N ≤ A.subgroupOf T := comap_mono hQA
    have hh := (N.subgroupOf (A.subgroupOf T)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hNA).toEquiv,hncard,
      Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv,hcard] at hh
    change 32 * N.relIndex (A.subgroupOf T) = 64 at hh
    omega
  have he (A B : Subgroup G) (hAT : A ≤ T) (hBT : B ≤ T) :
      A.subgroupOf T = B.subgroupOf T ↔ A = B := by
    constructor
    · intro hh
      have hm := congrArg (Subgroup.map T.subtype) hh
      simpa only [map_subgroupOf_eq_of_le hAT,map_subgroupOf_eq_of_le hBT] using hm
    · rintro rfl; rfl
  rcases eq_one_of_three_overgroups_of_quotient_card_four N hquot
      (E1.subgroupOf T) (E2.subgroupOf T) (E3.subgroupOf T) (E.subgroupOf T)
      (comap_mono h1) (comap_mono h2) (comap_mono h3) (comap_mono hE)
      (hi E1 h1 h1T hc1) (hi E2 h2 h2T hc2) (hi E3 h3 h3T hc3) (hi E hE hET hcE)
      (fun hh => hne12 ((he E1 E2 h1T h2T).mp hh))
      (fun hh => hne13 ((he E1 E3 h1T h3T).mp hh))
      (fun hh => hne23 ((he E2 E3 h2T h3T).mp hh)) with hh | hh | hh
  · exact Or.inl ((he E E1 hET h1T).mp hh)
  · exact Or.inr (Or.inl ((he E E2 hET h2T).mp hh))
  · exact Or.inr (Or.inr ((he E E3 hET h3T).mp hh))

namespace Marking
variable (m : Marking d)

/-- The original local conjugate and factor movement identify the literal quotient. -/
theorem centralizer_quotient_s3_c2 (hE : IsEvenCharacteristicAt d.T)
    (hgrowth : (d.T : Subgroup G) < centralizer ({m.z} : Set G)) :
    letI : (m.core.subgroupOf (centralizer ({m.z} : Set G))).Normal := m.marked_core_normal hE
    Nonempty (((centralizer ({m.z} : Set G)) ⧸ m.core.subgroupOf (centralizer ({m.z} : Set G))) ≃*
      (Equiv.Perm (Fin 3) × BinaryFourPlus.C2)) := by
  let p := m.pairData
  let q := m.coreData p rfl rfl
  let : (q.Q.subgroupOf p.C).Normal := m.marked_core_normal hE
  have hfactor : ∃ g : G, g ∈ p.C ∧
      g ∉ normalizer (q.factors.left.map q.Q.subtype : Set G) := by
    classical
    by_contra! hn
    exact m.diagonal_not_normalizes_left p rfl rfl true
      (fun x hx => hn x (p.z_central (m.elementaryGroup_le_sylow true true hx)))
  obtain ⟨a,haQ,haZ,hza⟩ := m.exists_core_conjugate_z
  obtain ⟨e,_⟩ := q.quotient_equiv_s3_c2_of_factor_moved m.pairData_closure hE
    (m.coreData_hyperplane_fixers p rfl rfl) (m.coreData_self_centralizer p rfl rfl)
    hgrowth m.not_isConj_t_z a haQ haZ hza.symm hfactor
  exact ⟨e⟩

private theorem twoCore_eq_B_sup_of_marked_conjugate (hE : IsEvenCharacteristicAt d.T)
    (hgrowth : (d.T : Subgroup G) < m.pairData.C)
    (hCM : m.pairData.C ⊓ d.M = (d.T : Subgroup G))
    (a : G) (haQ : a ∈ m.core) (haZ : a ∉ zpowers m.z) (haz : IsConj a m.z) :
    m.pairData.C.pCoreIn 2 = m.B ⊔ m.core := by
  let p := m.pairData
  let q := m.coreData p rfl rfl
  let : (q.Q.subgroupOf p.C).Normal := m.marked_core_normal hE
  have hfactor : ∃ g : G, g ∈ p.C ∧
      g ∉ normalizer (q.factors.left.map q.Q.subtype : Set G) := by
    classical
    by_contra! hn
    exact m.diagonal_not_normalizes_left p rfl rfl true
      (fun x hx => hn x (p.z_central (m.elementaryGroup_le_sylow true true hx)))
  obtain ⟨hc,hn⟩ := q.twoCore_not_le_factor_normalizer m.pairData_closure hE
    (m.coreData_hyperplane_fixers p rfl rfl) (m.coreData_self_centralizer p rfl rfl)
    hgrowth m.not_isConj_t_z a haQ haZ haz hfactor
  have hQC : p.C ≤ normalizer (q.Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer q.le_C).mp inferInstance
  have hQN : q.Q ≤ p.C.pCoreIn 2 := le_pCoreIn_of_normalizes q.isPGroup q.le_C hQC
  have hNT : p.C.pCoreIn 2 ≤ (d.T : Subgroup G) := by
    have hh := pCoreIn_le_sylow p.C (d.T.subtype p.z_central)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le p.z_central] at hh
  obtain ⟨hQ0,h0T,hc0,hcA,hcB,h0A,h0B,hAB⟩ := m.three_core_overgroups
  have hnoA : ¬m.elementaryGroup true true ≤ p.C.pCoreIn 2 :=
    p.A_not_le_core _ (m.diagonal_weakly_closed true) m.normalizer_A hCM hgrowth
  rcases three_overgroups q (m.coreOvergroup 0) (m.elementaryGroup true true ⊔ m.core)
      (m.B ⊔ m.core) (p.C.pCoreIn 2) hQ0 le_sup_right le_sup_right hQN h0T
      (sup_le (m.elementaryGroup_le_sylow true true) q.le_T)
      (sup_le (m.elementaryGroup_le_sylow false false) q.le_T) hNT
      hc0 hcA hcB hc h0A h0B hAB with h0 | hA | hB
  · exact False.elim (hn (by rw [h0,m.coreOvergroup_zero p rfl rfl]; exact inf_le_right))
  · exact False.elim (hnoA (by rw [hA]; exact le_sup_left))
  · exact hB

/-- The three native overgroups identify the actual ambient two-core. -/
theorem twoCore_eq_B_sup (hE : IsEvenCharacteristicAt d.T)
    (hgrowth : (d.T : Subgroup G) < centralizer ({m.z} : Set G)) :
    (centralizer ({m.z} : Set G)).pCoreIn 2 = m.B ⊔ m.core := by
  obtain ⟨a,haQ,haZ,hza⟩ := m.exists_core_conjugate_z
  exact m.twoCore_eq_B_sup_of_marked_conjugate hE hgrowth m.local_centralizer_z a haQ haZ hza.symm

/-- B is normal in the literal z-centralizer, which lies in N_G(B). -/
theorem B_normal (hE : IsEvenCharacteristicAt d.T)
    (hgrowth : (d.T : Subgroup G) < centralizer ({m.z} : Set G)) :
    (m.B.subgroupOf (centralizer ({m.z} : Set G))).Normal ∧
      centralizer ({m.z} : Set G) ≤ normalizer (m.B : Set G) :=
  m.pairData.B_normal_of_sup_eq_core m.B m.core (m.diagonal_weakly_closed false)
    (m.twoCore_eq_B_sup hE hgrowth).symm

end Marking

/-- Source 13.9.8, with all marked coordinate, fusion, and square-action
inputs constructed. Strict centralizer growth is exactly the preceding 13.9.5
input retained for its independent source owner. -/
theorem source13_9_8 {K : GroupClass} (hG : IsSimpleQTKE K G)
    (d : Configuration G) (m : Marking d)
    (hgrowth : (d.T : Subgroup G) < centralizer ({m.z} : Set G)) :
    let C := centralizer ({m.z} : Set G)
    let N := m.core.subgroupOf C
    letI : N.Normal := m.marked_core_normal (hG.evenCharacteristic d.T)
    N.Normal ∧ Nonempty ((C ⧸ N) ≃* (Equiv.Perm (Fin 3) × BinaryFourPlus.C2)) ∧
      (m.B.subgroupOf C).Normal ∧ C ≤ normalizer (m.B : Set G) ∧
      C.pCoreIn 2 = m.B ⊔ m.core ∧ Group.IsSolvable C := by
  dsimp only
  have hE := hG.evenCharacteristic d.T
  exact ⟨m.marked_core_normal hE,m.centralizer_quotient_s3_c2 hE hgrowth,
    (m.B_normal hE hgrowth).1,(m.B_normal hE hgrowth).2,
    m.twoCore_eq_B_sup hE hgrowth,m.marked_centralizer_z_solvable hE⟩

end CFSG.Quasithin.Chapter13.Section09

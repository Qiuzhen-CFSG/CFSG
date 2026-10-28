module
public import CFSG.Quasithin.Chapter5.Section03CentralizerExceptional
public import Theory.GroupTheory.PCoreCentralQuotientImage
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The normal closure in the exceptional linear centralizer

A Sylow-normal elementary four-group containing a central involution has
Sylow-central image of order two in the central quotient. Characteristic
two descends to that quotient. The elementary normal-closure lemma then
places its conjugate span in the quotient two-core, and two-core lifting
puts the original normal closure in the original two-core. Its image
modulo the same central involution is elementary abelian.

This is the B.2.14 step used in Aschbacher--Smith §5.3.7, printed p.660
(`refs/quasithin.pdf`). The actual prepared linear row supplies the groups
in the Chapter6 companion; no normal-closure containment is assumed.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter5.Section03LinearSource
variable {G : Type*} [Group G] [Finite G]

/-- The normal closure of a Sylow-normal four-group containing a central
involution lies in the two-core and is elementary modulo that involution. -/
theorem four_normalClosure (T : Sylow 2 G) (Z C : Subgroup G) [C.Normal]
    [IsElementaryAbelian 2 Z]
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hn : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hZ : Nat.card Z = 4) (hC : Nat.card C = 2)
    (hCZ : C ≤ Z) (hc : C ≤ center G) :
    normalClosure (Z : Set G) ≤ pCore 2 G ∧
      IsElementaryAbelian 2 ((normalClosure (Z : Set G)).map (QuotientGroup.mk' C)) := by
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.of_card (n := 1) (by simpa using hC)
  have hZbar : Nat.card (Z.map q) = 2 := by
    have hh := (C.subgroupOf Z).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hCZ).toEquiv, hC, hZ] at hh
    change 2 * C.relIndex Z = 4 at hh
    have hi : C.relIndex Z = Nat.card (Z.map q) := by
      simpa only [q, QuotientGroup.ker_mk'] using (relIndex_ker Z q)
    omega
  have hnbar : (T : Subgroup G).map q ≤ normalizer (Z.map q : Set (G ⧸ C)) :=
    (map_mono hn).trans (Z.le_normalizer_map q)
  have hzcentral : Z.map q ≤ centralizer ((T : Subgroup G).map q : Set (G ⧸ C)) :=
    le_centralizer_iff.mp (hnbar.trans (normalizer_le_centralizer_of_card_two _ hZbar))
  let : IsElementaryAbelian 2 (Z.map q) := IsElementaryAbelian.map q
  have hcharbar := q.centralizer_pCore_le_of_surjective_centralKernel hq
    (by simpa only [q, QuotientGroup.ker_mk'] using hc) hchar
  obtain ⟨hWR, hWE⟩ := Section03CentralizerExceptional.quotient_normal_closure_elementary
    ((T : Subgroup G).map q) (pCore 2 (G ⧸ C)) (Z.map q)
    (pCore_isPGroup.le_sylow_of_normal (T.mapSurjective (f := q) hq)) hcharbar hzcentral
  have hm : (normalClosure (Z : Set G)).map q = normalClosure (Z.map q : Set (G ⧸ C)) :=
    map_normalClosure _ q hq
  rw [← hm] at hWR hWE
  refine ⟨?_, hWE⟩
  have hh := map_le_iff_le_comap.mp hWR
  rwa [q.comap_pCore_of_ker_isPGroup hq hk] at hh
end CFSG.Quasithin.Chapter5.Section03LinearSource

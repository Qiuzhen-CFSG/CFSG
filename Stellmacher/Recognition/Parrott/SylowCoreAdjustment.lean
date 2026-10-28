module

public import Stellmacher.Recognition.Parrott.SylowCoreGeometry
public import Stellmacher.Recognition.Parrott.SylowCoreAdjustmentWords

/-!
# Parrott's core coordinate adjustment

Starting with a frame through (10) and the five central coset alternatives,
choose the corrected a and c from the word calculation. The elementary
basis is preserved because a changes only by t. To preserve the core,
recover v,t,z,u,w from the new generators using b², [a,b], [d,t], [a,d],
and c². This recovers the correction factors and hence the old generators.
Thus all subgroup equalities refer to the original E,F,J,T.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.679, equations (11)–(15).
-/

open Subgroup Tits
namespace Stellmacher.Recognition.ParrottSylowInitialData
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private theorem comm_mem (K : Subgroup G) {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    parrottCommutator x y ∈ K :=
  K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hx) (K.inv_mem hy)) hx) hy

private theorem adjusted_elementary (f : ParrottSylowInitialData n) {caseTwo : Bool}
    (k : CoreAdjustedCoordinates f caseTwo) :
    closure ({z,n.t,n.v,f.u,k.a} : Set G) = e.F := by
  rw [← f.elementary_basis]
  rcases k.a_eq with ha | ha
  · rw [ha]
  rw [ha]
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact (mul_mem_cancel_right (subset_closure (by simp : n.t ∈
          ({z,n.t,n.v,f.u,f.a*n.t} : Set G)))).mp (subset_closure (by simp))

private theorem adjusted_core (f : ParrottSylowInitialData n) {caseTwo : Bool}
    (k : CoreAdjustedCoordinates f caseTwo) :
    closure ({k.a,f.b,k.c,f.d} : Set G) =
      (pCore 2 (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype := by
  let H := centralizer ({z} : Set G)
  let J := (pCore 2 H).map H.subtype
  let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
  let K := closure ({k.a,f.b,k.c,f.d} : Set G)
  have hEJ : E ≤ J := by
    rintro g ⟨y, hy, rfl⟩
    exact ⟨y, y.property, rfl⟩
  have htJ : n.t ∈ J := hEJ (f.basis_mem_derived _ (by simp))
  have hRJ : closure ({f.w,n.v,n.t,f.u} : Set G) ≤ J := by
    apply (closure_le _).mpr
    intro g hg
    apply hEJ
    apply f.basis_mem_derived
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    tauto
  have haK : k.a ∈ K := subset_closure (by simp)
  have hbK : f.b ∈ K := subset_closure (by simp)
  have hcK : k.c ∈ K := subset_closure (by simp)
  have hdK : f.d ∈ K := subset_closure (by simp)
  have hvK : n.v ∈ K := f.eq03_b ▸ K.pow_mem hbK 2
  have htK : n.t ∈ K := k.ab ▸ comm_mem K haK hbK
  have hzK : z ∈ K := f.eq03_dt ▸ comm_mem K hdK htK
  have huK : f.u ∈ K := by
    have had := comm_mem K haK hdK
    rw [k.ad] at had
    cases caseTwo
    · exact had
    · exact (K.mul_mem_cancel_right hvK).mp had
  have hwK : f.w ∈ K := by
    have hcc := K.pow_mem hcK 2
    rw [k.cc] at hcc
    cases caseTwo
    · exact (K.mul_mem_cancel_right huK).mp hcc
    · exact hcc
  have hRK : closure ({f.w,n.v,n.t,f.u} : Set G) ≤ K := by
    apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> assumption
  obtain ⟨r, hr, hcr⟩ := k.c_eq
  have haOld : f.a ∈ K := by
    rcases k.a_eq with ha | ha
    · rwa [ha] at haK
    · rw [ha] at haK
      exact (K.mul_mem_cancel_right htK).mp haK
  have hcOld : f.c ∈ K := by
    rw [hcr] at hcK
    exact (K.mul_mem_cancel_right (hRK hr)).mp hcK
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · rcases k.a_eq with ha | ha
      · rw [ha]; exact f.generators_mem_core _ (by simp)
      · rw [ha]; exact mul_mem (f.generators_mem_core _ (by simp)) htJ
    · exact f.generators_mem_core _ (by simp)
    · rw [hcr]; exact mul_mem (f.generators_mem_core _ (by simp)) (hRJ hr)
    · exact f.generators_mem_core _ (by simp)
  · rw [← f.core_generators]
    apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> assumption

/-- Remove the central errors in (11)–(15), preserving the supplied action,
elementary subgroup, and core. Only a and c change, by the adjustments on
Parrott's printed p.679. -/
public theorem exists_core_relations_of_coset_alternatives [Finite G]
    (f : ParrottSylowInitialData n) (h : ParrottCentralizerHypotheses z)
    (caseTwo : Bool) (hc : f.CoreCosetAlternatives caseTwo) :
    ∃ g : ParrottSylowInitialData n,
      g.CoreRelations caseTwo ∧
      g.u = f.u ∧ g.w = f.w ∧ g.x = f.x ∧ g.b = f.b ∧ g.d = f.d ∧
      (g.a = f.a ∨ g.a = f.a*n.t) ∧
      ∃ r ∈ closure ({f.w,n.v,n.t,f.u} : Set G), g.c = f.c*r := by
  obtain ⟨k⟩ := exists_core_adjusted_coordinates f h caseTwo hc
  let g : ParrottSylowInitialData n := {
    toParrottSylowActionData := f.toParrottSylowActionData
    a := k.a
    b := f.b
    c := k.c
    d := f.d
    elementary_basis := adjusted_elementary f k
    core_generators := adjusted_core f k
    comm_bt := f.comm_bt
    d_sq := f.d_sq
    eq02_bw := f.eq02_bw
    eq02_aw := k.aw
    eq02_bu := f.eq02_bu
    eq03_db := f.eq03_db
    eq03_dt := f.eq03_dt
    eq03_b := f.eq03_b
    eq05_ab := k.ab
    eq07_dw := f.eq07_dw
    eq08_du := f.eq08_du
    eq09_cu := k.cu
    eq09_cw := k.cw
    eq10_ct := k.ct
    eq10_cv := k.cv
    ax_alternative := k.ax }
  exact ⟨g, ⟨k.ad,k.ac,k.cc,k.cd,k.bc⟩,
    rfl,rfl,rfl,rfl,rfl,k.a_eq,k.c_eq⟩

end Stellmacher.Recognition.ParrottSylowInitialData

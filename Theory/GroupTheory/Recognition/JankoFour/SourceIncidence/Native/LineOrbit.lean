module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.LineOrbit.Checks
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.LineOrbit.Counts
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.LineOrbit.Roots
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.OrbitTransport

/-!
# The five actual native line orbitals

The checked forest transports each entry of the existing exhaustive trio
catalogue from one of five representatives. The representatives satisfy
exactly their literal source labels, including both Golay radical tests.
Equivariance therefore proves the unique-label partition and transitivity of
the first-trio stabilizer. The checked colour-fibre counts give the five
valencies. Full M24 transitivity moves the first trio to any prescribed one.

Source: Aschbacher–Segev (1991), (3.4), applied in (5.4), pp.594,600.
-/

public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeLineOrbit
open SourceCycleBase.Native

theorem exists_transport (i : Fin 3795) : ∃ g : trioStabilizer standardTrio,
    (g : M24) • rootLine (node i).root = FarOrbit.entry i := by
  generalize hn : (node i).depth = n
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    have hc := all_edges i
    change (if (node i).depth = 0 then _ else _) at hc
    by_cases hz : (node i).depth = 0
    · rw [if_pos hz] at hc
      exact ⟨1,by rw [Subgroup.coe_one,one_smul]; exact congrArg FarOrbit.entry hc.symm⟩
    · rw [if_neg hz] at hc
      obtain ⟨g,hg⟩ := ih (node (node i).parent).depth (by omega) (node i).parent rfl
      refine ⟨nativeGenerator (node i).generator * g,?_⟩
      rw [Subgroup.coe_mul,mul_smul,←hc.2.1,hg]
      apply line_parts_injective
      change (nativeGenerator (node i).generator : M24) • (FarOrbit.entry (node i).parent).parts = _
      rw [FarOrbit.entry_parts,FarOrbit.entry_parts]
      exact FarOrbit.parts_transport _ _ _ hc.2.2

theorem delta_smul_iff (g : M24) (i : Fin 5) (l m : Line) :
    Delta i (g • l) (g • m) ↔ Delta i l m := by
  constructor
  · intro hh
    simpa only [inv_smul_smul] using NativeOrbitals.delta_transport g⁻¹ i _ _ hh
  · exact NativeOrbitals.delta_transport g i l m

theorem entry_delta_iff (i : Fin 5) (j : Fin 3795) :
    Delta i standardTrio (FarOrbit.entry j) ↔ i = (node j).root := by
  obtain ⟨g,hg⟩ := exists_transport j
  have hs : (g : M24) • standardTrio = standardTrio := line_parts_injective g.property
  have hh := delta_smul_iff (g : M24) i standardTrio (rootLine (node j).root)
  rw [hs,hg,root_delta_iff] at hh
  exact hh

/-- All five source predicates partition the native lines at each line. -/
theorem partition (l m : Line) : ∃! i : Fin 5, Delta i l m := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq M24 standardTrio l
  obtain ⟨j,hj⟩ := FarOrbit.entry_surjective (g⁻¹ • m)
  have he : m = g • FarOrbit.entry j := by rw [hj,smul_inv_smul]
  rw [he]
  simp only [delta_smul_iff,entry_delta_iff]
  exact existsUnique_eq

private theorem standard_transitive (i : Fin 5) (l m : Line)
    (hl : Delta i standardTrio l) (hm : Delta i standardTrio m) :
    ∃ g : M24, g • standardTrio = standardTrio ∧ g • l = m := by
  obtain ⟨j,rfl⟩ := FarOrbit.entry_surjective l
  obtain ⟨k,rfl⟩ := FarOrbit.entry_surjective m
  obtain ⟨a,ha⟩ := exists_transport j
  obtain ⟨b,hb⟩ := exists_transport k
  have hj := (entry_delta_iff i j).mp hl
  have hk := (entry_delta_iff i k).mp hm
  refine ⟨((b*a⁻¹ : trioStabilizer standardTrio) : M24),
    line_parts_injective (b*a⁻¹).property,?_⟩
  rw [Subgroup.coe_mul,Subgroup.coe_inv,mul_smul,←ha,inv_smul_smul,←hj, hk]
  exact hb

/-- The stabilizer of the literal first trio is transitive on each native label. -/
theorem transitive (l k m : Line) (i : Fin 5) (hk : Delta i l k) (hm : Delta i l m) :
    ∃ g : M24, g • l = l ∧ g • k = m := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq M24 standardTrio l
  have hk' : Delta i standardTrio (g⁻¹ • k) := by
    simpa only [inv_smul_smul] using NativeOrbitals.delta_transport g⁻¹ i _ _ hk
  have hm' : Delta i standardTrio (g⁻¹ • m) := by
    simpa only [inv_smul_smul] using NativeOrbitals.delta_transport g⁻¹ i _ _ hm
  obtain ⟨b,hb,hb'⟩ := standard_transitive i _ _ hk' hm'
  refine ⟨g*b*g⁻¹,?_,?_⟩
  · simp only [mul_smul,inv_smul_smul,hb]
  · simp only [mul_smul,hb',smul_inv_smul]

/-- The native valencies in the order of the actual five source predicates. -/
theorem valency (l : Line) (i : Fin 5) :
    {m | Delta i l m}.ncard = (![1,42,56,1008,2688] : Fin 5 → ℕ) i := by
  classical
  let e : Fin 3795 ≃ Line :=
    Equiv.ofBijective FarOrbit.entry ⟨FarOrbit.entry_injective,FarOrbit.entry_surjective⟩
  have standard : {m | Delta i standardTrio m}.ncard =
      (![1,42,56,1008,2688] : Fin 5 → ℕ) i := by
    rw [←Nat.card_coe_set_eq]
    let f := e.subtypeEquiv (p := fun j => (node j).root = i)
      (q := fun m => Delta i standardTrio m)
      (fun j => (entry_delta_iff i j).trans eq_comm |>.symm)
    exact (Nat.card_congr f).symm.trans (fibre_card i)
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq M24 standardTrio l
  rw [←Nat.card_coe_set_eq,←standard,←Nat.card_coe_set_eq]
  exact (Nat.card_congr ((MulAction.toPerm g).subtypeEquiv
    (p := fun m => Delta i standardTrio m)
    (q := fun m => Delta i (g • standardTrio) m)
    (fun m => (delta_smul_iff g i standardTrio m).symm))).symm

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeLineOrbit

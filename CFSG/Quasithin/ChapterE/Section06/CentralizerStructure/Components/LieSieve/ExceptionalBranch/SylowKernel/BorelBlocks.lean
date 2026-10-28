module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.SylowKernel.Reduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.LocalSubgroups
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.Overgroup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.OrbitFactors
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.ConjugateDecomposition

/-!
# E.6.7 on the exceptional Borel-orbit overgroup

The actual overgroup B ⊔ Q has characteristic two and is solvable.
Applying the universally quantified E.6.7 input gives its full decomposition,
including the Thompson commutators, set product, and action conclusions.
Solvability excludes the nonsolvable quotient models, so all blocks are
A₃ blocks; the non-Borel intersection makes the family nonempty.

The intrinsic orbit-factor theorem puts a Q-conjugate of B in a block.
Conjugating the complete decomposition back places B itself in an A₃ block,
which constructs the published `BorelBlockWitness` without changing its
interface. The separate kernel comparison also applies directly to any
Q-conjugate, since Q centralizes V pointwise. No block placement or action
bound is assumed in the construction; the universal E.6.7 input stays explicit.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7–8,
printed pp.246–248 (PDF pp.257–259).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V U L : Subgroup G}

open InvariantSubspaces.BlockSelection

/-- Apply the complete universal E.6.7 input to the actual Borel-orbit overgroup. -/
theorem overgroup_decomposition
    (input : E67Input T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    Nonempty (E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V U
      ((normalizer (S : Set L)).map L.subtype ⊔ sylowCentralizer (T : Subgroup G) V)) := by
  apply input U hU _ le_sup_right
    (sup_le ((map_subtype_le _).trans hL.1)
      (inf_le_right.trans (Subgroup.centralizer_le hU.1)))
  exact overgroup_characteristicTwo hU hL hm S hS

/-- Solvable chi-zero blocks have alternating-three type. -/
theorem alternating_three_of_solvable {X : Type*} [Group X] [Group.IsSolvable X]
    (hx : ChapterC.IsChiZeroBlock X) : ChapterC.IsAlternatingBlock X 3 := by
  rcases hx with ⟨n, hn, hshort, F, _, _, hF, hpsl, _⟩ | h3 | h5
  · obtain ⟨E, _, _, hE, ⟨e⟩⟩ := hpsl
    let : Finite X := hshort.finite
    let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) :=
      GorensteinWalter.psl2_isPerfect_of_card_gt_three E (by
        rw [hE]
        have hh : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
        omega)
    let : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact (Group.IsPerfect.not_isSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E)
      inferInstance).elim
  · exact h3
  · obtain ⟨e⟩ := h5.2.2.quotient_iso
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance).elim

/-- Every block in the chosen overgroup has type A₃. -/
theorem decomposition_alternating_three
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V U
      ((normalizer (S : Set L)).map L.subtype ⊔ sylowCentralizer (T : Subgroup G) V))
    (i : Fin d.count) : ChapterC.IsAlternatingBlock (d.block i) 3 := by
  let := overgroup_solvable hU hL hm S hS
  let : Group.IsSolvable (d.block i) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective (d.le i))
  exact alternating_three_of_solvable (d.type i)

/-- The decomposition is nonempty because the Borel is outside M. -/
theorem decomposition_count_pos
    (hm : ClassicalGroup.IsPSL L 2 4)
    (hLM : L ⊓ M = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V U
      ((normalizer (S : Set L)).map L.subtype ⊔ sylowCentralizer (T : Subgroup G) V)) :
    0 < d.count := by
  by_contra! hz
  have he : d.count = 0 := Nat.eq_zero_of_le_zero hz
  have hblocks : (⨆ i, d.block i) = ⊥ := by
    apply le_bot_iff.mp
    apply iSup_le
    intro i
    exact (Nat.not_lt_zero i.val (he ▸ i.isLt)).elim
  have hd := d.generated
  rw [hblocks, sup_bot_eq] at hd
  exact borel_not_le hm hLM S hS
    (le_sup_left.trans (hd.le.trans inf_le_right))

omit [Finite G] in
private theorem fixedSpace_map_of_pointwise_fixed (V B : Subgroup G) (e : G ≃* G)
    (hfix : ∀ v ∈ V, e v = v) :
    V ⊓ centralizer (B.map e.toMonoidHom : Set G) = V ⊓ centralizer (B : Set G) := by
  ext v
  constructor
  · rintro ⟨hv, hc⟩
    refine ⟨hv, ?_⟩
    intro b hb
    apply e.injective
    simpa only [map_mul, hfix v hv] using hc (e b) (mem_map_of_mem e.toMonoidHom hb)
  · rintro ⟨hv, hc⟩
    refine ⟨hv, ?_⟩
    rintro b ⟨a, ha, rfl⟩
    change e a * v = v * e a
    simpa only [map_mul, hfix v hv] using congrArg e (hc a ha)

variable {K : GroupClass} {D : Subgroup G}

/-- Every Q-conjugate of the Borel detects the original component action kernel.
This gives the exact comparison needed if the factor argument returns an orbit member. -/
theorem fixedSpace_conjugate_borel
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (q : G) (hq : q ∈ sylowCentralizer (T : Subgroup G) V) :
    V ⊓ centralizer (((normalizer (S : Set L)).map L.subtype).map
      (MulAut.conj q).toMonoidHom : Set G) = V ⊓ centralizer (L : Set G) := by
  rw [fixedSpace_map_of_pointwise_fixed V _ (MulAut.conj q) (by
    intro v hv
    change q * v * q⁻¹ = v
    rw [← mem_centralizer_iff.mp hq.2 v hv]
    simp)]
  apply fixedSpace_eq_borel hm (component_normalized_by_V h hU hL) S
  intro v hv x
  have hx : ((x : L) : G) ∈ L ⊓ sylowCentralizer (T : Subgroup G) V :=
    hS ▸ mem_map_of_mem L.subtype x.property
  rw [mem_centralizer_iff.mp hx.2.2 v hv]
  simp

/-- Concrete placement of a Q-conjugate gives the same kernel inclusion as
literal Borel containment; there is no assumed action bound. -/
theorem block_fixedSpace_le_component
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (q : G) (hq : q ∈ sylowCentralizer (T : Subgroup G) V)
    (hBD : ((normalizer (S : Set L)).map L.subtype).map (MulAut.conj q).toMonoidHom ≤ D) :
    V ⊓ centralizer (D : Set G) ≤ V ⊓ centralizer (L : Set G) := by
  rw [← fixedSpace_conjugate_borel h hU hL hm S hS q hq]
  exact inf_le_inf_left V (Subgroup.centralizer_le hBD)


/-- The exceptional Borel lies in an A₃ block of a complete E.6.7
decomposition of its characteristic-two overgroup. Only the genuine universal
E.6.7 input is assumed; all overgroup and block-placement data are constructed. -/
theorem nonempty_borelBlockWitness
    (h : HypothesisE61 K T M V) (input : E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4)
    (hLM : L ⊓ M = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    Nonempty (BorelBlockWitness T M V U L S) := by
  let B := (normalizer (S : Set L)).map L.subtype
  let Q := sylowCentralizer (T : Subgroup G) V
  let H := B ⊔ Q
  have hQC : Q ≤ centralizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hU.1)
  have hHC : H ≤ centralizer (U : Set G) :=
    sup_le ((map_subtype_le _).trans hL.1) hQC
  have hchar : HasCharacteristicTwo H := overgroup_characteristicTwo hU hL hm S hS
  let : Group.IsSolvable H := overgroup_solvable hU hL hm S hS
  obtain ⟨d⟩ := overgroup_decomposition input hU hL hm S hS
  let i : Fin d.count := ⟨0, decomposition_count_pos hm hLM S hS d⟩
  have hthree := decomposition_alternating_three hU hL hm S hS d
  obtain ⟨q, hq, hBD⟩ := exists_conjugate_borel_le hL hm hQC
    (T.isPGroup'.to_le inf_le_left) S hS (d.block i) (d.le i) (d.subnormal i) (hthree i)
  let e := MulAut.conj q⁻¹
  have hQ : Q.map e.toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (Q.le_normalizer (Q.inv_mem hq))
  have hM : M.map e.toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (M.inv_mem (h.sylow_le hq.1)))
  have hV : V.map e.toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp
      (centralizer_le_normalizer (V : Set G) ((centralizer (V : Set G)).inv_mem hq.2))
  have hH : H.map e.toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer ((show Q ≤ H from le_sup_right) (Q.inv_mem hq)))
  obtain ⟨d', j, hj⟩ := exists_conjugate_decomposition d hthree e hQ hM hV hH i
  refine ⟨{
    overgroup := H
    contains_Q := le_sup_right
    centralizes_U := hHC
    characteristicTwo := hchar
    decomposition := d'
    index := j
    alternating := decomposition_alternating_three hU hL hm S hS d' j
    borel_le := ?_
  }⟩
  rw [hj]
  have hh := map_mono (f := e.toMonoidHom) hBD
  have he : e.toMonoidHom.comp (MulAut.conj q).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [e, MulAut.conj_apply, mul_assoc]
  rwa [map_map, he, map_id] at hh

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks

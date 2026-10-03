module

public import Theory.SpecificGroups.Tits.AtlasPermutations

/-!
# A proper nonsolvable subgroup in the ATLAS permutation image

Put `a = atlasA`, `b = atlasB`, and `c = a*b*a*b*a*b⁻¹*a`. The subgroup
`⟨b,c⟩` fixes letter 1596, while `a` moves it. A concrete commutator identity
shows that `b` belongs to every term of this subgroup's derived series.
Thus no subgroup orders or simplicity results are needed.

The permutations come from `refs/original/n-group-global/atlas-tits-p1600-{a,b}.g`;
the subgroup is `H1` in `atlas-tits-presentation.M`. GAP was used only to find
the conjugating words. The permutation laws, fixed points, nonidentity, and
commutator identity are all checked by Lean's kernel. No relationship with
Parrott's ten-generator presentation is asserted here.
-/

namespace Tits

open scoped commutatorElement

/-- The second generator of the ATLAS subgroup `H1`. -/
@[expose] public def atlasC : Equiv.Perm (Fin 1600) :=
  atlasA * atlasB * atlasA * atlasB * atlasA * atlasB⁻¹ * atlasA

/-- The nonsolvable subgroup used as a witness inside the ATLAS image. -/
@[expose] public def atlasWitness : Subgroup (Equiv.Perm (Fin 1600)) :=
  Subgroup.closure {atlasB, atlasC}

private def conjugator {G : Type*} [Group G] (b c : G) : G :=
  b ^ 2 * c * (b⁻¹ * c⁻¹) ^ 2 * b⁻¹ * c * b * c⁻¹ * b⁻¹

private def transporter {G : Type*} [Group G] (b c : G) : G :=
  c * b⁻¹ * c⁻¹ * b⁻¹ * c⁻¹ * b * c * b * c⁻¹

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem certificate :
    atlasB = transporter atlasB atlasC *
      ⁅atlasB⁻¹, (conjugator atlasB atlasC)⁻¹ * atlasB⁻¹ *
        conjugator atlasB atlasC⁆ * (transporter atlasB atlasC)⁻¹ := by
  apply Equiv.ext
  decide +kernel

private theorem b_ne_one : atlasB ≠ 1 := by
  intro h
  have h0 := congrArg (fun f : Equiv.Perm (Fin 1600) => f 0) h
  have : atlasB 0 ≠ (1 : Equiv.Perm (Fin 1600)) 0 := by decide
  exact this h0

private theorem b_mem : atlasB ∈ atlasWitness :=
  Subgroup.subset_closure (Set.mem_insert _ _)

private theorem c_mem : atlasC ∈ atlasWitness :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- The ATLAS witness is nonsolvable, certified by a recurring derived-series element. -/
public theorem not_isSolvable_atlasWitness : ¬ Group.IsSolvable atlasWitness := by
  let b : atlasWitness := ⟨atlasB, b_mem⟩
  let c : atlasWitness := ⟨atlasC, c_mem⟩
  let g := conjugator b c
  let t := transporter b c
  have hkey : b = t * ⁅b⁻¹, g⁻¹ * b⁻¹ * g⁆ * t⁻¹ :=
    Subtype.ext certificate
  have hne : b ≠ 1 := fun h => b_ne_one (congrArg Subtype.val h)
  apply not_isSolvable_of_mem_derivedSeries hne
  intro n
  induction n with
  | zero => exact Subgroup.mem_top b
  | succ n ih =>
    have hi := (derivedSeries atlasWitness n).inv_mem ih
    have hc : g⁻¹ * b⁻¹ * g ∈ derivedSeries atlasWitness n := by
      simpa only [inv_inv] using (derivedSeries_normal atlasWitness n).conj_mem _ hi g⁻¹
    rw [hkey]
    exact (derivedSeries_normal atlasWitness (n + 1)).conj_mem _
      (Subgroup.commutator_mem_commutator hi hc) t

/-- Every subgroup containing the ATLAS generators contains the witness. -/
public theorem atlasWitness_le {K : Subgroup (Equiv.Perm (Fin 1600))}
    (ha : atlasA ∈ K) (hb : atlasB ∈ K) : atlasWitness ≤ K := by
  apply (Subgroup.closure_le K).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact hb
  · rw [Set.mem_singleton_iff] at hx
    subst x
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem
      ha hb) ha) hb) ha) (K.inv_mem hb)) ha

/-- The first ATLAS generator moves a point fixed by the witness subgroup. -/
public theorem atlasA_not_mem_atlasWitness : atlasA ∉ atlasWitness := by
  let S := MulAction.stabilizer (Equiv.Perm (Fin 1600)) (1596 : Fin 1600)
  have hfix : atlasWitness ≤ S := by
    apply (Subgroup.closure_le S).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · change atlasB 1596 = 1596
      decide +kernel
    · rw [Set.mem_singleton_iff] at hx
      subst x
      change atlasC 1596 = 1596
      decide +kernel
  intro ha
  have hm := hfix ha
  change atlasA 1596 = 1596 at hm
  have hn : atlasA 1596 ≠ 1596 := by decide
  exact hn hm

/-- The witness is proper inside every subgroup containing both ATLAS generators. -/
public theorem atlasWitness_lt {K : Subgroup (Equiv.Perm (Fin 1600))}
    (ha : atlasA ∈ K) (hb : atlasB ∈ K) : atlasWitness < K := by
  apply lt_of_le_of_ne (atlasWitness_le ha hb)
  intro h
  exact atlasA_not_mem_atlasWitness (h.symm ▸ ha)

end Tits

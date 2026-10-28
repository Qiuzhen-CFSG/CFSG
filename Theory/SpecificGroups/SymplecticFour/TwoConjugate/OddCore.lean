module
public import Theory.GroupTheory.OddCoreElementaryTwoCentralizers
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.NonrootCentralizer
public import Theory.SpecificGroups.SymplecticFour.InvolutionTypes
/-!
# Odd cores of central symplectic pairs without root elements

A nonidentity element of the central root plane that is not a root element
has both parameters nonzero. Its full centralizer is therefore the marked
unipotent subgroup. For a noncyclic elementary subgroup of that plane,
the three-centralizer generation theorem eliminates the odd core of every
containing subgroup. The final theorem applies this to the literal pair
formed with the opposition matrix.

Source: Aschbacher--Smith E.2.7, printed p.220, the odd-core step in the
branch without root involutions. Pair recognition remains separate.
-/
public section
open Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
open InvolutionTypes
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A nonroot central element has the full marked unipotent centralizer. -/
theorem centralizer_eq_unipotent_of_nonroot_central
    {v : Sp F} (hv : v ∈ (CentralRootGeometry.parameter (F := F)).range)
    (hv1 : v ≠ 1) (hnr : ¬IsRootElement v) :
    centralizer ({v} : Set (Sp F)) = unipotent := by
  obtain ⟨⟨s,t⟩,rfl⟩ := hv
  simp only [CentralRootGeometry.parameter_apply]
  change centralizer ({upper s.toAdd t.toAdd} : Set (Sp F)) = _
  have hs : s.toAdd ≠ 0 := by
    intro he
    have ht : t.toAdd ≠ 0 := by
      intro hf
      exact hv1 (by simp [CentralRootGeometry.parameter_apply,he,hf,
        RootSubgroup.element_zero])
    apply hnr
    refine ⟨1,4,t.toAdd,ht,?_⟩
    simp [CentralRootGeometry.parameter_apply,he,RootSubgroup.element_zero]
  have ht : t.toAdd ≠ 0 := by
    intro he
    apply hnr
    refine ⟨1,0,s.toAdd,hs,?_⟩
    simp [CentralRootGeometry.parameter_apply,he,RootSubgroup.element_zero]
  exact centralizer_upper_eq_unipotent _ _ hs ht

/-- A noncyclic elementary subgroup without root elements detects the odd core
of every literal containing subgroup. -/
theorem subgroup_oddCore_eq_bot_of_nonroot_central
    {n : ℕ} (hF : Nat.card F = 2^n) (I V : Subgroup (Sp F))
    [IsElementaryAbelian 2 V] (hVI : V ≤ I) (hr : 2 < Nat.card V)
    (hc : V ≤ (CentralRootGeometry.parameter (F := F)).range)
    (hnr : ∀ v ∈ V, ¬IsRootElement v) : pPrimeCore 2 I = ⊥ := by
  let : IsElementaryAbelian 2 (V.subgroupOf I) :=
    IsElementaryAbelian.subgroupOf hVI
  apply pPrimeCore_eq_bot_of_noncyclic_elementary_centralizers (V.subgroupOf I)
  · rwa [Nat.card_congr (subgroupOfEquivOfLe hVI).toEquiv]
  · intro v hv hv1
    have he : centralizer ({v} : Set I) =
        (unipotent (F := F)).subgroupOf I := by
      ext x
      rw [mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
        ← centralizer_eq_unipotent_of_nonroot_central (hc hv)
          (fun h => hv1 (Subtype.ext h)) (hnr v hv),
        mem_centralizer_singleton_iff, ← Subtype.coe_inj]
      rfl
    rw [he]
    exact (isPGroup_unipotent hF).comap_subtype

/-- The actual opposition pair has trivial odd core in the no-root branch. -/
theorem oppositePair_oddCore_eq_bot_of_nonroot_central
    {n : ℕ} (hF : Nat.card F = 2^n) (V : Subgroup (Sp F))
    [IsElementaryAbelian 2 V] (hr : 2 < Nat.card V)
    (hc : V ≤ (CentralRootGeometry.parameter (F := F)).range)
    (hnr : ∀ v ∈ oppositePair V, ¬IsRootElement v) :
    pPrimeCore 2 (oppositePair V) = ⊥ :=
  subgroup_oddCore_eq_bot_of_nonroot_central hF (oppositePair V) V
    le_sup_left hr hc (fun v hv => hnr v
      ((show V ≤ oppositePair V from le_sup_left) hv))

end Theory.SpecificGroups.SymplecticFour.TwoConjugate

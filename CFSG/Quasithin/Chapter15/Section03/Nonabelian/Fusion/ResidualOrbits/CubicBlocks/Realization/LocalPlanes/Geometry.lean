module
public import Theory.ElementaryAbelian.Join
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.LocalProduct
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.Splitting

/-!
# Aligning the actual local planes with the natural quotient summands

The square formula says that an involution has a pure upper coordinate.
A subgroup contained in the union of two subgroups lies in one of them.
Thus each elementary local plane lies over one natural summand. The planes
cannot choose the same summand: the commutator formula would make two
noncommuting reflections in the actual local product commute. This constructs
a permutation of the labels, without choosing a preferred product equivalence.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.54(4)
and the first paragraph of 15.3.61(2), printed pp.1146 and 1150.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization

variable {G : Type*} [Group G] {I Y P V : Subgroup G}
  {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
  [(V.subgroupOf P).Normal]

/-- An actual square-one element has a pure natural-summand coordinate. -/
theorem square_one_upper_pure (d : LayerActions I Y P V hIP hIV)
    (hf : PairingFormula d) (x : P) (hx : (x : G) ^ 2 = 1) :
    upperMap d x ∈ naturalSummand 0 ∨ upperMap d x ∈ naturalSummand 1 := by
  obtain ⟨hm, he⟩ := hf.square x
  have h1 : (⟨(x : G) ^ 2, hm⟩ : V) = 1 := Subtype.ext hx
  rw [h1, map_one] at he
  have hz : Matrix.vecMulVec (upperMap d x).1.toAdd (upperMap d x).2.toAdd = 0 :=
    congrArg Multiplicative.toAdd he.symm
  have pure : ∀ w : SumVector, Matrix.vecMulVec w.1.toAdd w.2.toAdd = 0 →
      w ∈ naturalSummand 0 ∨ w ∈ naturalSummand 1 := by
    simp_rw [mem_naturalSummand_iff]
    decide +kernel
  exact pure _ hz

/-- An elementary subgroup lies over one whole summand, not a mixture of them. -/
theorem elementary_le_one_summand (d : LayerActions I Y P V hIP hIV)
    (hf : PairingFormula d) (A : Subgroup G) (hAP : A ≤ P)
    [IsElementaryAbelian 2 A] : ∃ j : Fin 2, A ≤ summandPreimage d j := by
  have hu : (A : Set G) ⊆ (summandPreimage d 0 : Set G) ∪ summandPreimage d 1 := by
    intro x hx
    have hp := square_one_upper_pure d hf ⟨x, hAP hx⟩
      (elemPow_eq_one_of_isElementaryAbelian x hx)
    exact hp.imp ((mem_summandPreimage d 0 ⟨x, hAP hx⟩).mpr)
      ((mem_summandPreimage d 1 ⟨x, hAP hx⟩).mpr)
  exact (SubgroupClass.subset_union.mp hu).elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)

/-- The pairing vanishes between vectors in the same natural summand. -/
theorem commute_of_same_summand (d : LayerActions I Y P V hIP hIV)
    (hf : PairingFormula d) (j : Fin 2) (x y : P)
    (hx : upperMap d x ∈ naturalSummand j) (hy : upperMap d y ∈ naturalSummand j) :
    Commute (x : G) (y : G) := by
  have zero : ∀ (j : Fin 2) (u v : SumVector),
      u ∈ naturalSummand j → v ∈ naturalSummand j →
      Matrix.vecMulVec u.1.toAdd v.2.toAdd + Matrix.vecMulVec v.1.toAdd u.2.toAdd = 0 := by
    intro j u v hu hv
    fin_cases j <;> simp [mem_naturalSummand_iff] at hu hv
    · simp [hu, hv]
    · simp [hu, hv]
  obtain ⟨hm, he⟩ := hf.commutator x y
  rw [zero j _ _ hx hy] at he
  have he1 : (⟨(x : G) * y * (x : G)⁻¹ * (y : G)⁻¹, hm⟩ : V) = 1 :=
    d.lowerCoordinates.injective (he.trans (map_one d.lowerCoordinates).symm)
  have hc := congrArg Subtype.val he1
  exact mul_inv_eq_one.mp (by
    simpa only [mul_inv_rev, mul_assoc, Subgroup.coe_one] using hc)

/-- The two actual E32 planes determine a permutation of the natural summands.
The local equivalence is allowed to interchange the planes. -/
theorem exists_plane_permutation (d : LayerActions I Y P V hIP hIV)
    (hf : PairingFormula d) (L : Subgroup G) (hLP : L ≤ P)
    (e : L ≃* CentralProductModel) :
    ∃ σ : Equiv.Perm (Fin 2), ∀ i, localPlane L e i ≤ summandPreimage d (σ i) := by
  classical
  have hex (i : Fin 2) : ∃ j : Fin 2, localPlane L e i ≤ summandPreimage d j := by
    let := localPlane_elementary L e i
    exact elementary_le_one_summand d hf _ ((localPlane_le L e i).trans hLP)
  choose f h using hex
  have hne : f 0 ≠ f 1 := by
    intro he
    let x : L := e.symm (1, DihedralGroup.sr 0)
    let y : L := e.symm (1, DihedralGroup.sr 1)
    have hm (m : CentralProductModel) (hm2 : m ^ 2 = 1) :
        (e.symm m : G) ∈ summandPreimage d (f 0) := by
      rcases centralProductModel_two_plane_cover m hm2 with h0 | h1
      · exact h 0 (mem_map.mpr ⟨m, h0, rfl⟩)
      · rw [he]
        exact h 1 (mem_map.mpr ⟨m, h1, rfl⟩)
    have hc := commute_of_same_summand d hf (f 0) ⟨x, hLP x.property⟩ ⟨y, hLP y.property⟩
      ((mem_summandPreimage d (f 0) _).mp (hm _ (by decide +kernel)))
      ((mem_summandPreimage d (f 0) _).mp (hm _ (by decide +kernel)))
    have hcL : x * y = y * x := Subtype.ext hc.eq
    have hcM := congrArg e hcL
    simp only [map_mul, x, y, e.apply_symm_apply] at hcM
    exact (by decide +kernel :
      (1, DihedralGroup.sr 0) * (1, DihedralGroup.sr 1) ≠
        ((1, DihedralGroup.sr 1) * (1, DihedralGroup.sr 0) : CentralProductModel)) hcM
  have hi : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hne he).elim
    · exact (hne he.symm).elim
    · rfl
  exact ⟨Equiv.ofBijective f ⟨hi, Finite.surjective_of_injective hi⟩, h⟩

omit [(V.subgroupOf P).Normal] in
/-- Each model plane is maximal among elementary subgroups of the local product. -/
theorem localPlane_maximal_elementary [Finite G] (L : Subgroup G)
    (e : L ≃* CentralProductModel) (i : Fin 2) (B : Subgroup G)
    (hAB : localPlane L e i ≤ B) (hBL : B ≤ L) [IsElementaryAbelian 2 B] :
    B = localPlane L e i := by
  have hu : (B : Set G) ⊆ (localPlane L e 0 : Set G) ∪ localPlane L e 1 := by
    intro x hx
    by_cases h1 : x = 1
    · exact Or.inl (h1 ▸ (localPlane L e 0).one_mem)
    · exact localPlane_cover L e x (hBL hx)
        (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) h1)
  obtain hB | hB := SubgroupClass.subset_union.mp hu
  · have he : localPlane L e i = localPlane L e 0 :=
      eq_of_le_of_card_ge (hAB.trans hB) (by rw [localPlane_card, localPlane_card])
    exact le_antisymm (he ▸ hB) hAB
  · have he : localPlane L e i = localPlane L e 1 :=
      eq_of_le_of_card_ge (hAB.trans hB) (by rw [localPlane_card, localPlane_card])
    exact le_antisymm (he ▸ hB) hAB

/-- The source central subgroup V is contained in both actual planes. -/
theorem lower_le_localPlane [Finite G] (d : LayerActions I Y P V hIP hIV)
    (L : Subgroup G) (hLP : L ≤ P) (hVL : V ≤ L)
    (hcentral : V ≤ centralizer (P : Set G)) (e : L ≃* CentralProductModel) (i : Fin 2) :
    V ≤ localPlane L e i := by
  let := d.elementary_lower
  let := localPlane_elementary L e i
  have hc : V ≤ centralizer (localPlane L e i : Set G) :=
    hcentral.trans (centralizer_le ((localPlane_le L e i).trans hLP))
  let := IsElementaryAbelian.sup_of_le_centralizer (p := 2) hc
  have he := localPlane_maximal_elementary L e i (localPlane L e i ⊔ V) le_sup_left
    (sup_le (localPlane_le L e i) hVL)
  exact he ▸ le_sup_right

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization

module
public import Stellmacher.SectionOne.OneSevenModuleProduct
public import Stellmacher.SectionOne.SL2ProductSylowCoordinates
public import Stellmacher.SectionOne.OneSevenFactorOpposite

/-!
# Simultaneous opposite Sylows in a product of one-seven factors

Let E be a normal internal product of one-seven factors and let J be its
intersection with an ambient Sylow 2-subgroup. There is one element x of E
such that J and its x-conjugate generate E, while their fixed spaces span
the entire elementary abelian module. This includes the empty factor family.
The result supplies the simultaneous group/module choice in the proof of
Stellmacher (2.3), Journal of Algebra 190 (1997), p.20, using (1.7) and the
factor structure supplied in (2.2); see refs/latex/stellmacher-n-group.tex.

Choose an opposite involution subgroup in every SL2(2) factor, with the two
fixed lines spanning that factor's four-element support. The canonical
product homomorphism combines the chosen conjugators: conjugation on a
single-coordinate element is exactly conjugation by its own coordinate.
Thus the two global Sylow subgroups generate every factor. Distinct factors
fix each other's supports, so each local fixed line is fixed by the full
corresponding Sylow subgroup. The support decomposition, together with the
common E-fixed complement, then gives the whole module as the join of the
two fixed spaces. Normality of E is used for the exact Sylow coordinates.
-/

namespace Stellmacher.SectionOne
universe u

private theorem simultaneous_factor_conjugator
    {G I : Type*} [Group G] [Fintype I]
    (D : I → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ a b : G, a ∈ D i → b ∈ D j → Commute a b)
    (x : ∀ i, D i) :
    ∃ g ∈ (⨆ i, D i), ∀ i, ∀ d ∈ D i,
      g * d * g⁻¹ = (x i : G) * d * (x i : G)⁻¹ := by
  classical
  let f : (∀ i, D i) →* G := Subgroup.noncommPiCoprod hcomm
  refine ⟨f x, ?_, ?_⟩
  · rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm)]
    exact ⟨x, rfl⟩
  · intro i d hd
    let d' : D i := ⟨d, hd⟩
    have hsingle : f (Pi.mulSingle i d') = d := Subgroup.noncommPiCoprod_mulSingle i d'
    rw [← hsingle, ← map_inv, ← map_mul, ← map_mul]
    have hpi : x * Pi.mulSingle i d' * x⁻¹ =
        Pi.mulSingle i (x i * d' * (x i)⁻¹) := by
      funext j
      by_cases hji : j = i
      · subst j; simp
      · simp [Pi.mulSingle_eq_of_ne hji]
    rw [hpi, Subgroup.noncommPiCoprod_mulSingle]
    rw [hsingle]
    rfl

private theorem support_fixed_le_fixed_iSup
    {G V I : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    (D Q : I → Subgroup G) (U : I → Subgroup V)
    (hQD : ∀ i, Q i ≤ D i)
    (hcross : ∀ i j, i ≠ j → U i ≤ FixedPoints.subgroup (D j) V)
    (i : I) :
    U i ⊓ FixedPoints.subgroup (Q i) V ≤
      FixedPoints.subgroup (⨆ j, Q j : Subgroup G) V := by
  intro v hv
  have hfix : (⨆ j, Q j) ≤ fixingSubgroup G ({v} : Set V) := by
    refine iSup_le fun j => ?_
    intro q hq
    rw [mem_fixingSubgroup_iff]
    intro w hw
    have hwv := Set.mem_singleton_iff.mp hw
    subst w
    by_cases hji : j = i
    · subst j
      exact (FixedPoints.mem_subgroup (M := Q i) (a := v)).mp hv.2 ⟨q, hq⟩
    · exact (FixedPoints.mem_subgroup (M := D j) (a := v)).mp
        (hcross i j (Ne.symm hji) hv.1) ⟨q, hQD j hq⟩
  rw [FixedPoints.mem_subgroup]
  intro q
  exact (mem_fixingSubgroup_iff (M := G)).mp (hfix q.property) v (Set.mem_singleton v)

private theorem opposite_of_coordinates
    {G V I : Type*} [Group G] [Group V] [MulDistribMulAction G V] [Fintype I]
    (D Q : I → Subgroup G) (U : I → Subgroup V)
    (E J : Subgroup G) (hE : E = ⨆ i, D i) (hJ : J = ⨆ i, Q i)
    (hQD : ∀ i, Q i ≤ D i)
    (hcomm : Pairwise fun i j => ∀ a b : G, a ∈ D i → b ∈ D j → Commute a b)
    (hcross : ∀ i j, i ≠ j → U i ≤ FixedPoints.subgroup (D j) V)
    (hmodule : FixedPoints.subgroup E V ⊔ (⨆ i, U i) = ⊤)
    (x : ∀ i, D i)
    (hgen : ∀ i, D i = Q i ⊔ (Q i).conjBy (x i))
    (hspan : ∀ i, U i ≤ (U i ⊓ FixedPoints.subgroup (Q i) V) ⊔
      (U i ⊓ FixedPoints.subgroup ((Q i).conjBy (x i)) V)) :
    ∃ g ∈ E, E = J ⊔ J.conjBy g ∧
      FixedPoints.subgroup J V ⊔ FixedPoints.subgroup (J.conjBy g) V = ⊤ := by
  classical
  obtain ⟨g, hg, hconj⟩ := simultaneous_factor_conjugator D hcomm x
  have hgE : g ∈ E := hE ▸ hg
  have hQg (i : I) : (Q i).conjBy g = (Q i).conjBy (x i) := by
    apply le_antisymm
    · rintro z ⟨q, hq, rfl⟩
      exact Subgroup.mem_map.mpr ⟨q, hq, (hconj i q (hQD i hq)).symm⟩
    · rintro z ⟨q, hq, rfl⟩
      exact Subgroup.mem_map.mpr ⟨q, hq, hconj i q (hQD i hq)⟩
  have hJg : J.conjBy g = ⨆ i, (Q i).conjBy g := by
    simp only [Subgroup.conjBy, hJ, Subgroup.map_iSup]
  have hQgle (i : I) : (Q i).conjBy g ≤ D i := by
    rw [hQg]
    rintro z ⟨q, hq, rfl⟩
    exact (D i).mul_mem ((D i).mul_mem (x i).property (hQD i hq))
      ((D i).inv_mem (x i).property)
  have hJE : J ≤ E := by
    rw [hJ, hE]
    exact iSup_mono hQD
  have hJgE : J.conjBy g ≤ E := by
    rw [hJg, hE]
    exact iSup_mono hQgle
  refine ⟨g, hgE, ?_, ?_⟩
  · apply le_antisymm
    · rw [hE]
      refine iSup_le fun i => ?_
      rw [hgen i, ← hQg]
      apply sup_le
      · exact (show Q i ≤ J by rw [hJ]; exact le_iSup Q i).trans le_sup_left
      · exact (show (Q i).conjBy g ≤ J.conjBy g by
          rw [hJg]; exact le_iSup (fun j => (Q j).conjBy g) i).trans le_sup_right
    · exact sup_le hJE hJgE
  · apply top_unique
    rw [← hmodule]
    apply sup_le
    · apply le_trans ?_ le_sup_left
      intro v hv
      rw [FixedPoints.mem_subgroup] at hv ⊢
      exact fun j => hv ⟨j, hJE j.property⟩
    · refine iSup_le fun i => ?_
      apply (hspan i).trans
      apply sup_le_sup
      · rw [hJ]
        exact support_fixed_le_fixed_iSup D Q U hQD hcross i
      · rw [← hQg, hJg]
        exact support_fixed_le_fixed_iSup D (fun j => (Q j).conjBy g) U hQgle hcross i

public theorem oneSevenFactor_exists_opposite_sylow
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (E : Subgroup G) (hEnormal : E.Normal)
    (F : Finset (Subgroup G)) (hprod : IsInternalDirectProduct E F)
    (hF : ∀ D ∈ F, IsOneSevenFactor (V := V) D) :
    ∃ x ∈ E, E = ((S : Subgroup G) ⊓ E) ⊔ ((S : Subgroup G) ⊓ E).conjBy x ∧
      FixedPoints.subgroup (((S : Subgroup G) ⊓ E) : Subgroup G) V ⊔
        FixedPoints.subgroup (((S : Subgroup G) ⊓ E).conjBy x) V = ⊤ := by
  classical
  let I := {D : Subgroup G // D ∈ F}
  let n := Fintype.card I
  let eI : Fin n ≃ I := (Fintype.equivFin I).symm
  let D : Fin n → Subgroup G := fun i => (eI i).val
  let Q : Fin n → Subgroup G := fun i => (S : Subgroup G) ⊓ D i
  let U : Fin n → Subgroup V := fun i => commutatorAction (D i) V
  have hDi (i : Fin n) : D i ∈ F := (eI i).property
  have hinj : Function.Injective D := by
    intro i j hij
    exact eI.injective (Subtype.ext hij)
  have hgenE : E = ⨆ i : Fin n, D i := by
    rw [hprod.1]
    apply le_antisymm
    · apply iSup_le
      intro K
      obtain ⟨i, rfl⟩ := eI.surjective K
      exact le_iSup D i
    · exact iSup_le fun i => le_iSup (fun K : I => (K : Subgroup G)) (eI i)
  obtain ⟨_, hJcoord, _, hQcard⟩ := sl2_product_sylow_coordinates S E hEnormal F
    hprod (fun D hD => (hF D hD).1)
  have hgenJ : (S : Subgroup G) ⊓ E = ⨆ i, Q i := by
    rw [hJcoord]
    apply le_antisymm
    · apply iSup_le
      intro K
      obtain ⟨i, rfl⟩ := eI.surjective K
      exact le_iSup Q i
    · exact iSup_le fun i => le_iSup
        (fun K : I => (S : Subgroup G) ⊓ (K : Subgroup G)) (eI i)
  have hcomm : Pairwise fun i j => ∀ a b : G, a ∈ D i → b ∈ D j → Commute a b := by
    intro i j hij a b ha hb
    exact hprod.2.2.2 (D i) (hDi i) (D j) (hDi j) (fun heq => hij (hinj heq))
      a ha b hb
  have hcross : ∀ i j, i ≠ j → U i ≤ FixedPoints.subgroup (D j) V := by
    intro i j hij
    exact oneSevenFactor_commutatorAction_le_fixedPoints h
      (D j) (D i) (hF _ (hDi j)) (hF _ (hDi i))
      (fun heq => hij (hinj heq.symm))
  have hmod := oneSevenFactor_module_product h D (fun i => hF _ (hDi i)) hinj E hgenE
  have hmodule : FixedPoints.subgroup E V ⊔ (⨆ i, U i) = ⊤ := by
    have hg := hmod.1.symm
    rw [iSup_option] at hg
    exact hg
  have hex (i : Fin n) := oneSevenFactor_exists_opposite h (D i) (Q i)
    (hF _ (hDi i)) inf_le_right
    (hQcard (D i) (hDi i))
  choose x hx hgen hspan using hex
  exact opposite_of_coordinates D Q U E ((S : Subgroup G) ⊓ E) hgenE hgenJ
    (fun _ => inf_le_right) hcomm hcross hmodule (fun i => ⟨x i, hx i⟩) hgen hspan

end Stellmacher.SectionOne


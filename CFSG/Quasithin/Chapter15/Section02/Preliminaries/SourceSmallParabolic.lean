module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallChiefKernel
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaWreathExclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralCubicExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.MarkedFiveUniqueness
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.CubicActionUniqueness
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonProper

/-!
# Small chosen actions: residual and chief-factor assembly

The proper choice has the natural Omega action, and every dihedral marking has
parameter two. A literal rank-one residual witness supplies residual uniqueness
and the ambient normalizer bound. The two faithful chief factors then reduce
each H-star quotient to four concrete groups. Existing Omega and cubic arguments
leave the marked-five wreath exclusion and the single symmetric-group exclusions
explicit. The whole-action rows similarly assemble maximal-overgroup uniqueness
from the remaining Omega argument.

These are conditional assembly theorems: the independent source premises in
15.2.1, 15.2.4--7 and the last exclusions of 15.2.8 remain to be proved.
Source: Aschbacher--Smith, original 15.2.1--8, printed pp.1104--1110.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- The proper source choice necessarily has the natural Omega action. -/
theorem ChosenSmallSource.omega_of_proper
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hne : V ≠ localModule T M) :
    letI := h.prepared.elementary
    SourceCases.Omega (imageRepresentation M V h.prepared.normalized) := by
  have : IsElementaryAbelian 2 (localModule T M) :=
    localModule_elementary_from_source h.ambient T
      ⟨Chapter1.mem_H_of_isTwoLocal h.maximal.1.1.1, h.maximal.1.2⟩
  have : IsElementaryAbelian 2 V := h.prepared.elementary
  have hn : M ≤ normalizer (V : Set G) := h.prepared.normalized
  have hc : V = localModule T M ∨
      ∃ U : Submodule (ZMod 2) (Additive (localModule T M)),
        SourceCases.Proper T M Mc (localModule T M)
          (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) U ∧
        V = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map (localModule T M).subtype := h.chosen
  change SourceCases.Omega (imageRepresentation M V hn)
  clear h
  rcases hc with he | ⟨U,hU,rfl⟩
  · exact (hne he).elim
  · exact hU.chosen_omega T M Mc (localModule T M)
      (le_normalizer_conjugateSpanBy _ _) U hn


/-- The dimension parameter in any dihedral marking of the chosen module is two. -/
theorem ChosenSmallSource.marking_dimension
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    letI := h.prepared.elementary
    ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)) (p m : ℕ),
      DihedralMarking l p m → m = 2 := by
  let := h.prepared.elementary
  intro l p m hd
  have hdim := hd.dimension
  have hfour := h.finrank_eq_four
  omega

/-- Residual uniqueness follows from the actual rank-one subgroup Y₁ ≤ Y. -/
theorem SmallResidualWitness.residual_unique
    {T : Sylow 2 G} {M Mc V Y₁ : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) :
    maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M} := by
  let := h.prepared.elementary
  have hYM : h.residual ≤ M :=
    source_caseIIResidual_le T h.maximal.1.2 (map_subtype_le _)
  apply Set.Subset.antisymm
  · intro N hN
    have hn : N ∈ maximalTwoLocalOvergroups (Y₁ ⊔ (T : Subgroup G)) :=
      ⟨hN.1,(sup_le_sup_right hw.le_residual (T : Subgroup G)).trans hN.2⟩
    rwa [hw.unique] at hn
  · apply Set.singleton_subset_iff.mpr
    exact ⟨h.maximal.1.1,sup_le hYM h.maximal.1.2⟩

/-- The witness also supplies the original ambient normalizer bound of 15.2.7(i). -/
theorem SmallResidualWitness.twoPerfect_normalizer
    {T : Sylow 2 G} {M Mc V Y₁ X : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁)
    (hXM : X ≤ M ⊓ Subgroup.centralizer (V : Set G))
    (hX : IsPPerfect 2 X) (hne : X ≠ ⊥)
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G)) :
    normalizer (X : Set G) ≤ M := by
  let := h.prepared.elementary
  exact source_chosen_twoPerfect_normalizer_of_residual_unique h.ambient T h.maximal.1
    h.partner h.prepared hw.residual_unique hXM hX hne hTX

/-- The Omega and cubic rows discharge all but the marked-five part of 15.2.4. -/
theorem ChosenSmallSource.HStar_not_symmetricFive_wreath_of_marked_five
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hfive : letI := h.prepared.elementary
      ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
        DihedralMarking l 5 2 → ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
          ¬ Nonempty ((H ⧸ pCore 2 H) ≃*
            RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))) := by
  let := h.prepared.elementary
  rcases h.small with ⟨l,p,m,hpm,hd⟩ | ho
  · have hm : m = 2 := h.marking_dimension l p m hd
    subst m
    rcases (primeDimensionOptions_iff p 2).mp hpm with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact source_dihedral_cubic_HStar_not_symmetricFive_wreath h.ambient T h.empty
        h.maximal h.centralizing h.partner h.many h.prepared l hpm hd hH
    · exact hfive l hd H hH
  · exact source_omega_chosen_HStar_not_symmetricFive_wreath h.ambient T h.empty
      h.maximal h.centralizing h.partner h.many h.prepared ho hH

/-- Assembly of 15.2.8 after its actual residual and three exclusion arguments.
The source theorem still owes these explicit premises. -/
theorem ChosenSmallSource.HStar_wreath_of_exclusions
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hfive : letI := h.prepared.elementary
      ∀ (l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype)),
        DihedralMarking l 5 2 → ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
          ¬ Nonempty ((H ⧸ pCore 2 H) ≃*
            RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hthree : ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)))
    (hfiveSingle : ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  rcases h.HStar_small_quotient_of_residual_unique hunique hH with h3 | hwr | h5 | h5wr
  · exact (hthree h3).elim
  · exact hwr
  · exact (hfiveSingle h5).elim
  · exact (h.HStar_not_symmetricFive_wreath_of_marked_five hfive hH h5wr).elim

/-- The non-Omega rows of 15.2.5 are already proved; only its actual Omega
comparison argument remains after the whole-action classification. -/
theorem ChosenSmallSource.maximal_overgroups_of_action_alternatives
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hprior : SmallSourcePrior T M V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (homega : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized) →
        maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc}) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} := by
  let := h.prepared.elementary
  rcases h.small with ⟨l,p,m,hpm,hd⟩ | ho
  · have hm : m = 2 := h.marking_dimension l p m hd
    subst m
    rcases (primeDimensionOptions_iff p 2).mp hpm with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · rcases ha with ⟨_,⟨e⟩⟩ | ⟨_,⟨e⟩⟩ | ho | ⟨⟨e⟩,_,_⟩
      · exact h.prepared.maximal_overgroups_of_symmetric_three_action h.ambient T
          h.empty h.maximal h.centralizing h.partner e
      · exact h.prepared.maximal_overgroups_of_symmetric_three_cubic_action h.ambient T
          h.empty h.maximal h.centralizing h.partner h.different e
      · exact homega ho
      · have hc3 := Nat.card_congr hd.dihedral.some.toEquiv
        have hc5 := Nat.card_congr e.toEquiv
        rw [DihedralGroup.nat_card] at hc3 hc5
        omega
    · exact h.prepared.maximal_overgroups_of_marked_five h.ambient T h.empty h.maximal
        h.many h.centralizing h.partner l hd hprior.global_residual
  · exact homega ho

end CFSG.Quasithin.Chapter15.Section02

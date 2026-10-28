module
public import CFSG.Quasithin.Chapter14.Section02.ProperQuasisimpleSource
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SmallAlternating

/-!
# Early exclusion of the small alternating containing rows

The original completion has a full Sylow S and a selected local component
K₁ properly contained in its canonical residual L. The small alternating
case of A.3.12 forces equality if L is A₅, A₆, or the actual perfect central
three-cover of A₆. Transporting along L∩X ≃ L preserves both the center
and its literal quotient map, giving the contradiction before any paired
three-rank or later maximal-local placement is needed.

The action consumer unpacks the actual six-point alternating action from
1.1.5 into its group or central-cover model. It retains the marked
permutation and automorphism as inputs; no action classification is assumed.
Source: Aschbacher--Smith 14.2.15, printed pp.985--986; A.3.12 and 1.1.5(3).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

private theorem small_alternating_model_transport
    {A D : Type*} [Group A] [Group D] (d : D ≃* A)
    (h : IsAlternating A 5 ∨ IsAlternating A 6 ∨ IsAlternatingCover A 6) :
    IsAlternating D 5 ∨ IsAlternating D 6 ∨ IsAlternatingCover D 6 := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨d.trans e⟩
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inl ⟨d.trans e⟩)
  · obtain ⟨hq,hz,⟨e⟩⟩ := h
    let := hq
    have hc : (center D).map d.toMonoidHom = center A := by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr d ⟨x,hx⟩).property
      · intro x hx
        exact ⟨d.symm x, ((centerCongr d).symm ⟨x,hx⟩).property, d.apply_symm_apply x⟩
    exact Or.inr (Or.inr ⟨IsQuasisimple.of_mulEquiv d.symm,
      hz.map ((centerCongr d).trans ·),
      ⟨(QuotientGroup.congr _ _ d hc).trans e⟩⟩)

/-- Original 14.2.15 excludes A₅, A₆ and the genuine perfect central three-cover
as containing components, without a paired-residual or later-local premise. -/
theorem source_proper_completion_small_alternating_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    ¬(IsAlternating L 5 ∨ IsAlternating L 6 ∨ IsAlternatingCover L 6) := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  change ¬(IsAlternating L 5 ∨ IsAlternating L 6 ∨ IsAlternatingCover L 6)
  intro hmodel
  have hcorea : X.pCoreIn 2 ≠ ⊥ := fun hh =>
    hcore (((pCore 2 X).map_eq_bot_iff_of_injective X.subtype_injective).mp hh)
  have hs := source_proper_completion_sylow hG T hempty hM hu hmany hcard e H hH
    K S hST hi hN hplacement hcore
  obtain ⟨hL,hKL,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcorea hs
  have hKC : K ≤ centralizer (centralInvolutions T : Set G) :=
    (le_sup_left.trans_eq hgen).trans
      (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hne : K ≠ L := fun he =>
    source_proper_completion_component_noncentral hG T hempty hM hu hmany hcard e
      H hH K S hST hgen hK hSN hcorea hs (he.ge.trans hKC)
  have hKX : K ≤ X := le_sup_left.trans le_sup_left
  have hSX : S ≤ X := le_sup_right
  obtain ⟨P,hP⟩ := hs
  have hPS : (P : Subgroup X) = S.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSX]
  have hKP : K.subgroupOf X ∈ Chapter1.L X P := by
    rw [hPS]
    exact (Chapter1.mem_LIn_iff_subgroupOf hSX hKX).mp ⟨hKX,hK⟩
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_small_alternating_containing_component
    P hKP.1 hL.2 (comap_mono hKL)
    (small_alternating_model_transport (subgroupOfEquivOfLe hL.1) hmodel)
  apply hne
  have he' := congrArg (Subgroup.map X.subtype) he
  rwa [map_subgroupOf_eq_of_le hKX,map_subgroupOf_eq_of_le hL.1] at he'

/-- The actual six-constructor action supplies the required A₆ or 3.A₆ model.
The transposition condition is unnecessary for this earlier non-enlargement cut. -/
theorem source_proper_completion_six_action_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    ∀ (α : MulAut L) (σ : Equiv.Perm (Fin 6)), ¬ AlternatingAction α 6 σ := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  change ∀ (α : MulAut L) (σ : Equiv.Perm (Fin 6)), ¬ AlternatingAction α 6 σ
  intro α σ ha
  apply source_proper_completion_small_alternating_exclusion hG T hempty hM hu hmany
    hcard e H hH K S hST hi hN hplacement hgen hK hSN hcore
  rcases ha with ⟨f,_⟩ | ⟨hq,hz,f,_⟩
  · exact Or.inr (Or.inl ⟨f⟩)
  · exact Or.inr (Or.inr ⟨hq,hz,⟨f⟩⟩)

end CFSG.Quasithin.Chapter14.Section02

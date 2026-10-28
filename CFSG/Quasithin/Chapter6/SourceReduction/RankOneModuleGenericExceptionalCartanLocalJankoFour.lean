module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalLinearExclusion
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityActualPair
public import Theory.SpecificGroups.Janko4.Model.Cardinality

/-!
# The whole residual in the normal J₄ containing row

A moved seed in the original Cartan escape has quotient PSL₂(4).
Its two distinct Sylow conjugates give a square of the simple quotient
order dividing the containing solvable-radical quotient order. That
quotient is a quotient of the containing two-core quotient. Consequently
25 divides the latter order, which excludes movement whenever its order
has only one factor five, in particular for the actual J₄ carrier.

This identifies the original seed with the whole residual without
identifying the two-core with the solvable radical of the container.
The final sieve retains all preceding exclusions and the same component.
It does not yet prove that the residual quotient is A₅ in the J₄ row,
or exclude the action of the entire intersected Cartan on that residual.
Those obligations remain in the local Cartan classification.

Source: Aschbacher--Smith 1.2.8 and 5.1.12--13, printed pp.506--507,
635--637, refs/quasithin.pdf. The concrete J₄ order retains its ATLAS
attribution through the imported cardinality theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

private theorem radical_quotient_card_dvd_twoCore (X : Type*) [Group X] [Finite X] :
    Nat.card (X ⧸ solvableRadical X) ∣ Nat.card (X ⧸ pCore 2 X) := by
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  have hle : pCore 2 X ≤ solvableRadical X :=
    le_solvableRadical _ inferInstance inferInstance
  let f := QuotientGroup.map (pCore 2 X) (solvableRadical X) (MonoidHom.id X) hle
  apply card_dvd_of_surjective f
  intro z
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (solvableRadical X) z
  exact ⟨QuotientGroup.mk' (pCore 2 X) x,rfl⟩

/-- The original moved A₅ pair forces two factors of five in the containing
intrinsic two-core quotient. Thus the actual seed is fixed when 25 is absent. -/
theorem seed_eq_residual_of_normal_twentyFive_free_container
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) [C.Normal] (hKC : K ≤ C.map Y.subtype)
    (h25 : ¬ 25 ∣ Nat.card (C ⧸ pCore 2 C)) : K = residual H := by
  by_contra hmoved
  have hm := moved_seed_linear_four_of_escape hG hK hKT horbit hmoved hY hescape
  have hmove : K < conjugateSpanBy K (T : Subgroup G) := by
    rw [conjugateSpanBy_eq_iSup_conj]
    change K < componentOrbit K (T : Subgroup G)
    exact lt_of_le_of_ne (le_componentOrbit K _) (fun he => hmoved (he.trans horbit))
  have hrad := Chapter1.Section02.MovedMaximality.moved_local_radical_eq_core hG T hK hmove
  let X := C.map Y.subtype
  have hYn : Y ≤ normalizer (X : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using
      (inferInstance : C.Normal)
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    (show (T : Subgroup G) ≤ H by rw [←hKT]; exact le_sup_right).trans (hY.2.trans hYn)
  have hd := Chapter1.Section02.MovedMaximality.actual_pair_square_dvd T hK.1 hKC hTX hmove
  rw [hrad] at hd
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  have hcard : Nat.card (K ⧸ pCore 2 K) = 60 := by
    rw [Nat.card_congr (e.trans e5).toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  rw [hcard] at hd
  let a := C.equivMapOfInjective Y.subtype Y.subtype_injective
  have hCX : Nat.card (X ⧸ pCore 2 X) = Nat.card (C ⧸ pCore 2 C) :=
    (Nat.card_congr (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).toEquiv).symm
  exact h25 ((by decide : 25 ∣ 60^2).trans
    (hd.trans ((radical_quotient_card_dvd_twoCore X).trans (dvd_of_eq hCX))))
/-- In a normal genuine J₄ container, the original E.2.2 seed is the whole
residual. Neither a residual A₅ mark nor a module model is assumed. -/
theorem seed_eq_residual_of_normal_jankoFour_container
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) [C.Normal] (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model)) : K = residual H := by
  apply seed_eq_residual_of_normal_twentyFive_free_container hG hK hKT horbit
    hY hescape C hKC
  rw [Nat.card_congr hm.some.toEquiv,Janko4.Cardinality.model_card]
  norm_num

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The original sieve retains all preceding exclusions and identifies its
seed with the entire original residual in the genuine normal J₄ row. -/
theorem localCartan_escape_seed_jankoFour_residual_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
            ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
            IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)) ∧
        (Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) → K = residual H) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd⟩ :=
    localCartan_escape_seed_no_odd_ternary h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd,?_⟩
  let := hCn
  exact LocalSieve.seed_eq_residual_of_normal_jankoFour_container h.qtke hKL hKT hR
    hY hescape C hKC

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

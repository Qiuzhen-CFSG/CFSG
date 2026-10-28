module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Basic
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceOmega
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersThompsonSourceAction

/-!
# LocalAnalysisCentralizersThompsonSourceOmega at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersThompsonSourceOmega`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender

open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

namespace Setup.NaturalCoordinates

variable (E : S.NaturalCoordinates)

private theorem natural_mem_fixed_iff_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : Subgroup G) (hAN : A ≤ normalizer (V : Set G)) (v : V) :
    evenWordsEquivNatural (E.coordinates v).toAdd ∈
      fixedSpace (BinaryPermutation.naturalRepresentation (Fin 7))
        ((A.subgroupOf (normalizer (V : Set G))).map
          (E.sourceNormalizerModel_at structural).permutation) ↔
      (v : G) ∈ centralizer (A : Set G) := by
  let D := E.sourceNormalizerModel_at structural
  constructor
  · intro hv a ha
    have hfix := hv ⟨D.permutation ⟨a,hAN ha⟩,
      mem_map_of_mem D.permutation (show (⟨a,hAN ha⟩ : normalizer (V : Set G)) ∈
        A.subgroupOf (normalizer (V : Set G)) from ha)⟩
    change BinaryPermutation.naturalRepresentation (Fin 7) (D.permutation ⟨a,hAN ha⟩)
      (evenWordsEquivNatural (E.coordinates v).toAdd) = _ at hfix
    rw [← evenWordsEquivNatural_equivariant] at hfix
    have he := D.equivariant ⟨a,hAN ha⟩ v
    have hh := E.coordinates.injective (Multiplicative.toAdd.injective
      (he.trans (evenWordsEquivNatural.injective hfix)))
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)
  · intro hv b
    obtain ⟨a,ha,hab⟩ := b.property
    change BinaryPermutation.naturalRepresentation (Fin 7) (b : Equiv.Perm (Fin 7))
      (evenWordsEquivNatural (E.coordinates v).toAdd) = _
    rw [← hab]
    have hh : V.normalizerMonoidHom a v = v := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hv a ha)
    have he := D.equivariant a v
    rw [hh] at he
    exact (evenWordsEquivNatural_equivariant _ _).symm.trans
      (congrArg evenWordsEquivNatural he.symm)

theorem maxElementary_card_eq_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
    (hne : (A.subgroupOf (normalizer (V : Set G))).map
      (E.sourceNormalizerModel_at structural).permutation ≠ ⊥) :
    Nat.card V = Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) *
      Nat.card ((A.subgroupOf (normalizer (V : Set G))).map
        (E.sourceNormalizerModel_at structural).permutation) := by
  let B := (A.subgroupOf (normalizer (V : Set G))).map
    (E.sourceNormalizerModel_at structural).permutation
  let σ := BinaryPermutation.naturalRepresentation (Fin 7)
  have hAN : A ≤ normalizer (V : Set G) :=
    hA.1.trans (((structural L S.hypothesis).2.2 V S.chosen).1)
  let e : V ≃ BinaryPermutation.natural (Fin 7) :=
    E.coordinates.toEquiv.trans ((Multiplicative.toAdd : Multiplicative EvenWord ≃ EvenWord).trans
      evenWordsEquivNatural.toEquiv)
  let c : (V ⊓ centralizer (A : Set G) : Subgroup G) ≃ fixedSpace σ B := {
    toFun := fun v => ⟨e ⟨v,v.property.1⟩,
      (E.natural_mem_fixed_iff_at structural A hAN _).mpr v.property.2⟩
    invFun := fun w => ⟨e.symm w,(e.symm w).property,
      (E.natural_mem_fixed_iff_at structural A hAN _).mp (by
        change e (e.symm w) ∈ fixedSpace σ B
        rw [e.apply_symm_apply]
        exact w.property)⟩
    left_inv := fun v => Subtype.ext (congrArg (fun x : V => (x : G))
      (e.symm_apply_apply ⟨v,v.property.1⟩))
    right_inv := fun w => Subtype.ext (e.apply_symm_apply w) }
  have hb := E.maxElementary_image_bestOffender_at structural A hA hne
  let : IsElementaryAbelian 2 B := hb.1.2
  have hd := natural_bestOffender_fixedCodim_eq_rank B hb
  have hdim := fixedCodim_add_finrank σ B
  rw [hd] at hdim
  have hcB : Nat.card B = 2 ^ rank B := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
    rw [rank,hn,Nat.log_pow (by decide)]
  rw [Nat.card_congr e, Nat.card_congr c, hcB,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := BinaryPermutation.natural (Fin 7)),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace σ B), Nat.card_zmod,← pow_add,
    Nat.add_comm,hdim]

theorem card_image_eq_centralizer_index_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : Subgroup G) (hAN : A ≤ normalizer (V : Set G)) :
    Nat.card ((A.subgroupOf (normalizer (V : Set G))).map
      (E.sourceNormalizerModel_at structural).permutation) =
      (centralizer (V : Set G)).relIndex A := by
  let N := normalizer (V : Set G)
  let D := E.sourceNormalizerModel_at structural
  have hk : D.permutation.ker = (centralizer (V : Set G)).subgroupOf N := by
    rw [normalizerModel_kernel D]
    ext n
    constructor
    · intro hn v hv
      exact congrArg (fun x : N => (x : G)) (hn ⟨v,V.le_normalizer hv⟩ hv)
    · intro hn v hv
      exact Subtype.ext (hn v hv)
  rw [← relIndex_ker,hk,relIndex_subgroupOf hAN]

theorem core_omega_eq_sup_fixed_maxElementary_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
    (hne : (A.subgroupOf (normalizer (V : Set G))).map
      (E.sourceNormalizerModel_at structural).permutation ≠ ⊥) :
    omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
      V ⊔ (omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓
        centralizer (A : Set G)) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let U := omegaCenterIn Q
  let C := A ⊓ centralizer (V : Set G)
  let : IsElementaryAbelian 2 V := S.chosen.elementary
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (show C ≤ A from inf_le_left)
  have hAN : A ≤ normalizer (V : Set G) :=
    hA.1.trans (((structural L S.hypothesis).2.2 V S.chosen).1)
  let : IsElementaryAbelian 2 (V ⊓ centralizer (A : Set G) : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have hCV : V ⊓ centralizer (A : Set G) = V ⊓ A := by
    apply le_antisymm
      (le_inf inf_le_left (maxElementary_contains_elementary_centralizer _ A _ hA
        (inf_le_left.trans S.chosen.le_sylow) inf_le_right))
    exact le_inf inf_le_left (inf_le_right.trans (le_centralizer A))
  have hVC : V ⊓ C = V ⊓ A := by
    apply le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans (le_centralizer V)))
  have hcard := E.maxElementary_card_eq_at structural A hA hne
  rw [E.card_image_eq_centralizer_index_at structural A hAN,hCV] at hcard
  have hCA : Nat.card C * (centralizer (V : Set G)).relIndex A = Nat.card A := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (centralizer (V : Set G) ⊓ A) A
      bot_le inf_le_right
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right] at hh
    simpa only [inf_comm,C] using hh
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes V C
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  rw [hVC,hcard] at hprod
  have hBcard : Nat.card (V ⊔ C : Subgroup G) = Nat.card A := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (V ⊓ A : Subgroup G)))
    calc
      Nat.card (V ⊓ A : Subgroup G) * Nat.card (V ⊔ C : Subgroup G) =
          (Nat.card (V ⊓ A : Subgroup G) *
            (centralizer (V : Set G)).relIndex A) * Nat.card C := hprod.symm
      _ = Nat.card (V ⊓ A : Subgroup G) *
          (Nat.card C * (centralizer (V : Set G)).relIndex A) := by ac_rfl
      _ = Nat.card (V ⊓ A : Subgroup G) * Nat.card A := by rw [hCA]
  have hBT : V ⊔ C ≤ (T : Subgroup G) :=
    sup_le S.chosen.le_sylow (inf_le_left.trans hA.1)
  have hBe : IsElementaryAbelian 2 (V ⊔ C : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  have hB : V ⊔ C ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) :=
    ⟨hBT,hBe,fun D hDT hDe => hBcard.symm ▸ hA.2.2 D hDT hDe⟩
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hCQ : C ≤ Q := by
    change C ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [← RecognitionSource.chosen_sylow_centralizer_eq_core_at S.hypothesis S.chosen structural]
    exact le_inf (inf_le_left.trans hA.1) inf_le_right
  have hUC : U ≤ centralizer (C : Set G) := by
    intro u hu
    exact centralizer_le hCQ ((mem_omegaCenterIn_iff _ _).mp hu).2.1
  have hUT : U ≤ (T : Subgroup G) :=
    fun u hu => hQT ((mem_omegaCenterIn_iff Q u).mp hu).1
  have hUB : U ≤ V ⊔ C :=
    maxElementary_contains_elementary_centralizer _ _ U hB hUT
      (le_centralizer_iff.mpr (sup_le
        ((chosen_le_core_omega (S := S)).trans (le_centralizer U))
        (le_centralizer_iff.mp hUC)))
  apply le_antisymm _ (sup_le (chosen_le_core_omega (S := S)) inf_le_left)
  intro u hu
  have hm : u ∈ (V : Set G) * (C : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left V C
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))]
    exact hUB hu
  obtain ⟨v,hv,c,hc,rfl⟩ := hm
  have hcU : c ∈ U := by
    have hh := U.mul_mem (U.inv_mem ((chosen_le_core_omega (S := S)) hv)) hu
    simpa only [inv_mul_cancel_left] using hh
  exact mul_mem_sup hv ⟨hcU,le_centralizer A hc.1⟩

theorem core_omega_maxElementary_splitting_of_weight_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      BinarySevenCode.weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    ∃ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G),
      (A.subgroupOf (normalizer (V : Set G))).map
        (E.sourceNormalizerModel_at structural).permutation ≠ ⊥ ∧
      omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
        V ⊔ (omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓
          centralizer (A : Set G)) := by
  classical
  have hg := E.thompson_generation_of_weight_six_at structural escape hsix
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G),
      ¬ A ≤ centralizer (V : Set G) := by
    by_contra! hn
    exact E.thompson_not_centralizes_of_generation hg (sSup_le hn)
  obtain ⟨A,hA,hne⟩ := hex
  have hn : (A.subgroupOf (normalizer (V : Set G))).map
      (E.sourceNormalizerModel_at structural).permutation ≠ ⊥ := by
    intro hz
    have hc := (Subgroup.map_eq_bot_iff _).mp hz
    rw [normalizerModel_kernel] at hc
    apply hne
    intro a ha v hv
    have hAN := hA.1.trans (((structural L S.hypothesis).2.2 V S.chosen).1)
    exact congrArg (fun x : normalizer (V : Set G) => (x : G))
      (hc (show (⟨a,hAN ha⟩ : normalizer (V : Set G)) ∈
        A.subgroupOf (normalizer (V : Set G)) from ha) ⟨v,V.le_normalizer hv⟩ hv)
  exact ⟨A,hA,hn,E.core_omega_eq_sup_fixed_maxElementary_at structural A hA hn⟩

end Setup.NaturalCoordinates

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven


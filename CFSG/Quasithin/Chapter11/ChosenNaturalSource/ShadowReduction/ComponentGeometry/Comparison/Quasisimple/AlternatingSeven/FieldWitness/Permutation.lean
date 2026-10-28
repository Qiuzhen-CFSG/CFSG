module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Transposition
public import Theory.SpecificGroups.AlternatingSeven.TranspositionCore
public import Theory.Alternating.Aut
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Theory.GroupTheory.InvolutionCentralizerControl
/-!
# The five-letter seed and its outer transposition

The perfect subgroup of order sixty in the centralizer of (45) is its
commutator subgroup, the alternating group on the other five letters.
The transposition (01) normalizes it and acts outerly, by the faithful
conjugation identification Aut(A5) = S5.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/
public noncomputable section
open Subgroup Equiv Equiv.Perm
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Permutation
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
abbrev S5 := Perm (Fin 5)
@[expose] def fiveHom : S5 →* S7 :=
  (MulAut.conj (swap (4 : Fin 7) 6)).toMonoidHom.comp
    ((permCongrHom (finSumFinEquiv : Fin 5 ⊕ Fin 2 ≃ Fin 7)).toMonoidHom.comp
      ((sumCongrHom (Fin 5) (Fin 2)).comp (MonoidHom.inl S5 (Perm (Fin 2)))))
theorem fiveHom_injective : Function.Injective fiveHom :=
  (MulAut.conj _).injective.comp ((permCongrHom finSumFinEquiv).injective.comp
    (sumCongrHom_injective.comp (fun _ _ h => congrArg Prod.fst h)))
@[expose] def five : Subgroup S7 := (alternatingGroup (Fin 5)).map fiveHom
theorem five_card : Nat.card five = 60 := by
  rw [five,card_map_of_injective fiveHom_injective,nat_card_alternatingGroup]
  norm_num [Nat.factorial]
instance five_perfect : Group.IsPerfect five := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.map _

theorem fiveHom_swap : fiveHom (swap 0 1) = swap01 := by
  ext i
  fin_cases i <;> decide

theorem five_le_centralizer : five ≤ centralizer ({swap45} : Set S7) := by
  rintro _ ⟨a,ha,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  exact (by decide +kernel : ∀ a : S5, fiveHom a * swap45 = swap45 * fiveHom a) a

theorem centralizer_commutator_card :
    Nat.card (commutator (centralizer ({swap45} : Set S7))) = 60 := by
  obtain ⟨e⟩ := _root_.AlternatingSeven.TranspositionCore.transposition_centralizer_equiv
    (MulEquiv.refl S7) swap45 (show swap45.IsSwap from ⟨4,5,by decide,rfl⟩)
  rw [←card_map_of_injective (f := e.toMonoidHom) e.injective (K := commutator _),map_commutator_eq,
    MonoidHom.range_eq_top.mpr e.surjective]
  rw [show (⊤ : Subgroup (S5 × Perm (Fin 2))) =
    (⊤ : Subgroup S5).prod (⊤ : Subgroup (Perm (Fin 2))) by ext; simp,
    commutator_prod_prod,←commutator_def,←commutator_def,
    alternatingGroup.commutator_perm_eq (by norm_num)]
  have hsmall : commutator (Perm (Fin 2)) = ⊥ := by
    apply (commutator_eq_bot_iff _).mpr
    exact ⟨⟨by decide +kernel⟩⟩
  rw [hsmall,Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,nat_card_alternatingGroup,
    card_bot]
  norm_num [Nat.factorial]

theorem perfect_eq_five (B : Subgroup S7) [Group.IsPerfect B]
    (hB : B ≤ centralizer ({swap45} : Set S7)) (hc : Nat.card B = 60) : B = five := by
  let C := centralizer ({swap45} : Set S7)
  let K := (commutator C).map C.subtype
  have hle (A : Subgroup S7) [Group.IsPerfect A] (hA : A ≤ C) : A ≤ K := by
    rw [←A.commutator_eq_self,show K = ⁅C,C⁆ from map_subtype_commutator C]
    exact commutator_mono hA hA
  have hcK : Nat.card K = 60 := by
    rw [card_map_of_injective C.subtype_injective]
    exact centralizer_commutator_card
  exact (eq_of_le_of_card_ge (hle B hB) (by omega)).trans
    (eq_of_le_of_card_ge (hle five five_le_centralizer) (by rw [five_card,hcK])).symm

theorem swap01_normalizes : swap01 ∈ normalizer (five : Set S7) := by
  rw [←fiveHom_swap]
  exact le_normalizer_map fiveHom (mem_map_of_mem fiveHom
    (show swap (0 : Fin 5) 1 ∈ normalizer (alternatingGroup (Fin 5) : Set S5) by
      rw [normalizer_eq_top]; trivial))

theorem swap01_not_inner : ¬ ∃ b : five,
    five.normalizerMonoidHom ⟨swap01,swap01_normalizes⟩ = MulAut.conj b := by
  rintro ⟨b,hb⟩
  obtain ⟨c,hc,hcb⟩ := b.property
  have he : (MulAut.conjNormal (swap (0 : Fin 5) 1) : MulAut (alternatingGroup (Fin 5))) =
      MulAut.conj ⟨c,hc⟩ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply fiveHom_injective
    have hh := congrArg (fun a : MulAut five => (a ⟨fiveHom x,mem_map_of_mem fiveHom x.property⟩).val) hb
    change swap01 * fiveHom x * swap01⁻¹ = b.val * fiveHom x * b.val⁻¹ at hh
    simpa only [MulAut.conj_apply,Subgroup.coe_mul,Subgroup.coe_inv,
      map_mul,map_inv,fiveHom_swap,hcb,MulAut.conjNormal_apply] using hh
  have hinj := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by decide) (by decide)).injective
  have heq : swap (0 : Fin 5) 1 = c := hinj (he.trans MulAut.conjNormal_val.symm)
  have hs := Perm.mem_alternatingGroup.mp hc
  rw [←heq,Perm.sign_swap (by decide)] at hs
  exact (by decide : (-1 : ℤˣ) ≠ 1) hs

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Permutation

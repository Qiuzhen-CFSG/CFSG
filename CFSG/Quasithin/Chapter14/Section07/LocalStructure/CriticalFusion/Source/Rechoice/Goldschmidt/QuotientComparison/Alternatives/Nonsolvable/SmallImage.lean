module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Preparation
public import Theory.SpecificGroups.PermutationThreePrimeCore

/-!
# Faithful images of the original small subnormal subgroup

The literal map I/O₂(I) → I/O₃′(I) has three-prime kernel. Each of S₃,
SL₃(2), and A₅ has trivial three-prime core, so the map restricts to an
isomorphism on the given subgroup. We retain that original subgroup,
subnormality and compatibility on elements. When its SL₃(2) image fills
the bang quotient, its original equivalence supplies both recognition
outputs; no independent PSL₂(7) identification is needed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 14.7.70, printed pp.1074–1075 (PDF pp.1091–1092), and F.6.11.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable

/-- The three actual models supplied by the small subnormal witness. -/
def SmallModel (D : Type*) [Group D] : Prop :=
  Nonempty (D ≃* Equiv.Perm (Fin 3)) ∨
  Nonempty (D ≃* Matrix.PSL3Two.SL) ∨
  Nonempty (D ≃* alternatingGroup (Fin 5))

theorem SmallModel.of_equiv {A B : Type*} [Group A] [Group B]
    (h : SmallModel B) (e : A ≃* B) : SmallModel A := by
  rcases h with ha | ha | ha <;> obtain ⟨a⟩ := ha
  · exact Or.inl ⟨e.trans a⟩
  · exact Or.inr (Or.inl ⟨e.trans a⟩)
  · exact Or.inr (Or.inr ⟨e.trans a⟩)

theorem SmallModel.threePrimeCore {D : Type*} [Group D] [Finite D]
    (h : SmallModel D) : pPrimeCore 3 D = ⊥ := by
  rcases h with he | he | he <;> obtain ⟨e⟩ := he
  · exact pPrimeCore_eq_bot_of_equiv e Theory.SpecificGroups.symmetricThree_threePrimeCore
  · let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup D := (e.trans Matrix.PSL3Two.equiv).isSimpleGroup
    apply pPrimeCore_eq_bot_of_simple
    rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_SL]
    decide
  · let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup D := e.isSimpleGroup
    apply pPrimeCore_eq_bot_of_simple
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]

/-- Any homomorphism with three-prime kernel is faithful on a small model. -/
theorem SmallModel.injective {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (hf : Nat.Coprime 3 (Nat.card f.ker))
    (K : Subgroup A) (hK : SmallModel K) : Function.Injective (f.subgroupMap K) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_bot_iff.mp
  rw [← hK.threePrimeCore]
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  rw [ker_subgroupMap]
  exact hf.of_dvd_right (card_comap_dvd_of_injective _ _ K.subtype_injective)

open Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (c : CriticalPath (L := L) F)

/-- The literal projection from I/O₂(I) to I/O₃′(I). -/
def plusToBang : ((I c) ⧸ pCore 2 (I c)) →* ((I c) ⧸ pPrimeCore 3 (I c)) :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    simpa only [Subgroup.comap_id] using (ChapterF.twoCore_le_primeToThreeCore (G := I c)))

theorem plusToBang_mk (x : I c) :
    plusToBang c (plusMap c x) = bangMap c x := rfl

theorem plusToBang_surjective : Function.Surjective (plusToBang c) :=
  QuotientGroup.map_surjective_of_surjective _ _ _ (QuotientGroup.mk_surjective) _

theorem plusToBang_kernel_coprime : Nat.Coprime 3 (Nat.card (plusToBang c).ker) := by
  rw [plusToBang, QuotientGroup.ker_map]
  exact pPrimeCore_coprime_card.of_dvd_right (card_map_dvd _ _)

/-- This isomorphism uses the original quotient projection on every element. -/
def smallImageEquiv (K : Subgroup ((I c) ⧸ pCore 2 (I c))) (hK : SmallModel K) :
    K ≃* K.map (plusToBang c) :=
  MulEquiv.ofBijective ((plusToBang c).subgroupMap K)
    ⟨hK.injective (plusToBang c) (plusToBang_kernel_coprime c) K,
      (plusToBang c).subgroupMap_surjective K⟩

theorem smallImageEquiv_apply (K : Subgroup ((I c) ⧸ pCore 2 (I c)))
    (hK : SmallModel K) (x : K) :
    (smallImageEquiv c K hK x : (I c) ⧸ pPrimeCore 3 (I c)) =
      plusToBang c x := rfl

/-- Retain the original witness and its faithful subnormal image simultaneously. -/
theorem retained_small_image (small : SmallSubnormal c) :
    ∃ K : Subgroup ((I c) ⧸ pCore 2 (I c)), K.IsSubnormal ∧ SmallModel K ∧
      (K.map (plusToBang c)).IsSubnormal ∧ SmallModel (K.map (plusToBang c)) := by
  obtain ⟨K, hK, hm⟩ := small
  exact ⟨K, hK, hm, hK.map (plusToBang_surjective c),
    SmallModel.of_equiv hm (smallImageEquiv c K hm).symm⟩

/-- Recognition from the full faithful image reuses the original small subgroup. -/
theorem recognition_of_image_eq_top
    (K : Subgroup ((I c) ⧸ pCore 2 (I c))) (hK : K.IsSubnormal)
    (e : K ≃* Matrix.PSL3Two.SL) (ht : K.map (plusToBang c) = ⊤) :
    Nonempty (BangRecognition c) := by
  let a : K ≃* ((I c) ⧸ pPrimeCore 3 (I c)) :=
    (smallImageEquiv c K (Or.inr (Or.inl ⟨e⟩))).trans
      ((MulEquiv.subgroupCongr ht).trans topEquiv)
  exact ⟨⟨a.symm.trans (e.trans Matrix.PSL3Two.equiv), K, hK,
    e.trans Matrix.PSL3Two.equiv⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable

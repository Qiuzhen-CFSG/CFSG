module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.BenderNormalizers
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting
public import Theory.GroupTheory.SylowNormalizerElementaryJoin

/-!
# Residual preservation in two binary rank-one factors

The solvable Sylow overgroup lies in the product of the two actual Borels.
Its Sylow is normal, so the lower two-core bound makes the specified
interval subgroup equal to that entire Sylow. The Borel quotient is abelian;
the cubic plane has full three-rank and hence its join with the Sylow is
characteristic in the Sylow normalizer. Thus the original join, and its
two-residual, are preserved. No choice of a model-family tag replaces the
actual product isomorphism.

Source: Aschbacher--Smith 10.2.5, printed p.748, the binary rank-one case
of (*). The original-enlargement application is BinaryThreeAction/Even.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow
variable {Q : Type*} [Group Q] [Finite Q]
/-- The binary rank-one Borel has abelian quotient by its Sylow radical. -/
theorem binary_normalizer_commutator {n : ℕ}
    (hm : ClassicalGroup.IsPSL Q 2 (2^n)) (hn : 0 < n) (S : Sylow 2 Q) :
    ⁅normalizer (S : Set Q),normalizer (S : Set Q)⁆ ≤ (S : Subgroup Q) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hf := ChapterF.Source.rankOneSylowFacts_psl2 F n hn hF R
  have hh := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    (hf.quotient_commutative R)
  have hmap := map_mono (f := (ChapterF.Source.sylowNormalizer R).subtype) hh
  change (_root_.commutator (normalizer (R : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)))).map
    (normalizer (R : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))).subtype ≤
    ((R : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).subgroupOf
      (normalizer (R : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)))).map
      (normalizer (R : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))).subtype at hmap
  rw [(normalizer (R : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))).map_subtype_commutator,
    subgroupOf_map_subtype] at hmap
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  change (⁅normalizer ((S : Subgroup Q) : Set Q),normalizer ((S : Subgroup Q) : Set Q)⁆).map
    e.toMonoidHom ≤ (S : Subgroup Q).map e.toMonoidHom
  rw [map_commutator,map_equiv_normalizer_eq]
  exact hmap.trans inf_le_left

private theorem sylow_product (S : Sylow 2 (Q × Q)) :
    (S : Subgroup (Q × Q)) = ((S : Subgroup _).map (MonoidHom.fst Q Q)).prod
      ((S : Subgroup _).map (MonoidHom.snd Q Q)) := by
  let A := S.mapSurjective (f := MonoidHom.fst Q Q) (fun q => ⟨(q,1),rfl⟩)
  let B := S.mapSurjective (f := MonoidHom.snd Q Q) (fun q => ⟨(1,q),rfl⟩)
  apply Eq.symm
  apply S.is_maximal'
  · obtain ⟨a,ha⟩ := A.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := B.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a+b)
    rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod]
    change Nat.card A * Nat.card B = 2^(a+b)
    rw [ha,hb,pow_add]
  · intro x hx
    exact ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩

/-- Both coordinate Borels give the same derived-subgroup bound in the product. -/
theorem binary_product_normalizer_commutator {n : ℕ}
    (hm : ClassicalGroup.IsPSL Q 2 (2^n)) (hn : 0 < n) (S : Sylow 2 (Q × Q)) :
    ⁅normalizer (S : Set (Q × Q)),normalizer (S : Set (Q × Q))⁆ ≤ (S : Subgroup (Q × Q)) := by
  have hproj (f : (Q × Q) →* Q) (hf : Function.Surjective f) :
      ⁅normalizer (S : Set (Q × Q)),normalizer (S : Set (Q × Q))⁆.map f ≤
        (S : Subgroup (Q × Q)).map f := by
    rw [map_commutator]
    exact (commutator_mono (le_normalizer_map f) (le_normalizer_map f)).trans
      (binary_normalizer_commutator hm hn (S.mapSurjective hf))
  intro x hx
  rw [sylow_product S]
  exact ⟨hproj (MonoidHom.fst Q Q) (fun q => ⟨(q,1),rfl⟩) (mem_map_of_mem _ hx),
    hproj (MonoidHom.snd Q Q) (fun q => ⟨(1,q),rfl⟩) (mem_map_of_mem _ hx)⟩
end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow

namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow
variable {Q A : Type*} [Group Q] [Finite Q] [Group A] [Finite A]
/-- The full cubic plane and literal core interval determine a preserved join. -/
theorem binary_pair_preserves_join {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL Q 2 (2^n)) (e : A ≃* Q × Q)
    (S : Sylow 2 A) (P U : Subgroup A)
    [Group.IsSolvable (P ⊔ (S : Subgroup A) : Subgroup A)]
    [IsElementaryAbelian 3 P] (hcard : Nat.card P = 9) (hrank : primeRank 3 A ≤ 2)
    (hcore : (P ⊔ (S : Subgroup A)).pCoreIn 2 ≤ U) (hUS : U ≤ (S : Subgroup A))
    (a : MulAut A) (ha : U.map a.toMonoidHom = U) :
    (P ⊔ (S : Subgroup A)).map a.toMonoidHom = P ⊔ S := by
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let P' := P.map e.toMonoidHom
  let : Group.IsSolvable (P' ⊔ (S' : Subgroup (Q × Q)) : Subgroup (Q × Q)) := by
    change Group.IsSolvable (P.map e.toMonoidHom ⊔ (S : Subgroup A).map e.toMonoidHom : Subgroup _)
    rw [← Subgroup.map_sup]
    exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _)
  have hPN : P ≤ normalizer (S : Set A) := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    change P.map e.toMonoidHom ≤ (normalizer ((S : Subgroup A) : Set A)).map e.toMonoidHom
    rw [map_equiv_normalizer_eq]
    exact binary_model_prod_le_normalizer hn hm S' P'
  have hSN : P ⊔ (S : Subgroup A) ≤ normalizer (S : Set A) :=
    sup_le hPN (S : Subgroup A).le_normalizer
  have hSCore : (S : Subgroup A) ≤ (P ⊔ (S : Subgroup A)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes S.isPGroup' le_sup_right hSN
  have hUS' : U = (S : Subgroup A) := le_antisymm hUS (hSCore.trans hcore)
  have hd : ⁅normalizer (S : Set A),normalizer (S : Set A)⁆ ≤ (S : Subgroup A) := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    change (⁅normalizer ((S : Subgroup A) : Set A),normalizer ((S : Subgroup A) : Set A)⁆).map
      e.toMonoidHom ≤ (S : Subgroup A).map e.toMonoidHom
    rw [map_commutator,map_equiv_normalizer_eq]
    exact binary_product_normalizer_commutator hm (by omega) S'
  apply map_sylow_join_of_elementary S P (p := 3) (n := 2) (by decide)
    (by simpa using hcard) hrank hPN hd a
  simpa only [hUS'] using ha
end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow

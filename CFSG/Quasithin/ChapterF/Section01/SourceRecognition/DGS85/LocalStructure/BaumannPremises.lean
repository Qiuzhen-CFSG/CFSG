module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CoreClosure
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.BaumannApplication.Commutator
public import Theory.GroupTheory.ConjugateSpanNormalClosure

/-!
# Baumann's theorem on the marked source closure

The internal normal closure used by `BaumannApplication` is identified with
X = <Q_delta^{G_lambda}> in the actual completion. The equivalence preserves
each element, the original core, the core of X, the Sylow index and the
Sylow omega-center closure. Relative 6.4 normality supplies the literal
no-characteristic-normal premise; normal subgroup inheritance supplies the
self-centralizing-core premise.

The independently proved Baumann theorem therefore gives its full commutator
bound in the original completion and natural coordinates for the same marked
quotient. Only the still-unproved 6.4 Sylow and SL2 quotient premises remain
explicit. The reduced F1.11 application uses the constructed reduced triple;
it does not assert the remaining 6.5 contradiction.

Source: DGS, *Groups and Graphs* (1985), 6.3--6.5, pp.120--122.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85
namespace MarkedClosure
open CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
variable {G : Type*} [Group G]

/-- The intrinsic adjacent-core closure has exactly the intended original image. -/
theorem coreClosure_image (A B : Subgroup G) (hAB : A.pCoreIn 2 ≤ B) :
    (coreClosure A B).map B.subtype = conjugateSpanBy (A.pCoreIn 2) B := by
  let X := conjugateSpanBy (A.pCoreIn 2) B
  have hXB : X ≤ B := conjugateSpanBy_le_self hAB
  let : (X.subgroupOf B).Normal :=
    (normal_subgroupOf_iff_le_normalizer hXB).mpr (le_normalizer_conjugateSpanBy _ _)
  have hcX : coreClosure A B ≤ X.subgroupOf B :=
    normalClosure_le_normal (fun x hx => le_conjugateSpanBy _ _ hx)
  apply le_antisymm ((map_mono hcX).trans_eq (map_subgroupOf_eq_of_le hXB))
  have hn : B ≤ normalizer ((coreClosure A B).map B.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
    change (((coreClosure A B).map B.subtype).comap B.subtype).Normal
    rw [comap_map_eq_self_of_injective B.subtype_injective]
    change (normalClosure _).Normal
    infer_instance
  apply conjugateSpanBy_le _ hn
  calc
    A.pCoreIn 2 = (coreInClosure A B).map (originalEmbedding A B) :=
      (coreInClosure_image A B hAB).symm
    _ ≤ (coreClosure A B).map B.subtype := by
      rw [originalEmbedding, ← map_map]
      exact map_mono (map_subtype_le _)

/-- The original embedding is an inclusion, with no quotient kernel. -/
theorem originalEmbedding_injective (A B : Subgroup G) :
    Function.Injective (originalEmbedding A B) :=
  B.subtype_injective.comp (coreClosure A B).subtype_injective

/-- The exact isomorphism from the nested subgroup carrier to the ambient closure. -/
def coreClosureEquiv (A B : Subgroup G) (hAB : A.pCoreIn 2 ≤ B) :
    coreClosure A B ≃* conjugateSpanBy (A.pCoreIn 2) B :=
  ((coreClosure A B).equivMapOfInjective B.subtype B.subtype_injective).trans
    (MulEquiv.subgroupCongr (coreClosure_image A B hAB))

/-- The closure equivalence preserves each original group element. -/
theorem coreClosureEquiv_coe (A B : Subgroup G) (hAB : A.pCoreIn 2 ≤ B)
    (x : coreClosure A B) :
    (coreClosureEquiv A B hAB x : G) = originalEmbedding A B x := rfl

 private def coreEquiv (A B : Subgroup G) (hAB : A.pCoreIn 2 ≤ B) :
    coreInClosure A B ≃* A.pCoreIn 2 :=
  ((coreInClosure A B).equivMapOfInjective (originalEmbedding A B)
    (originalEmbedding_injective A B)).trans
    (MulEquiv.subgroupCongr (coreInClosure_image A B hAB))

 private theorem characteristic_map_equiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (D : Subgroup H) [D.Characteristic] :
    (D.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let a' : MulAut H := (e.trans a).trans e.symm
  refine mem_map.mpr ⟨a' y, characteristic_iff_le_comap.mp inferInstance a' hy, ?_⟩
  exact e.apply_symm_apply _


/-- The range is precisely the original adjacent-core closure. -/
theorem originalEmbedding_range (A B : Subgroup G) (hAB : A.pCoreIn 2 ≤ B) :
    (originalEmbedding A B).range = conjugateSpanBy (A.pCoreIn 2) B := by
  rw [originalEmbedding, MonoidHom.range_comp, range_subtype, coreClosure_image A B hAB]

/-- The closure core maps to the actual embedded core of the original X. -/
theorem core_image (A B : Subgroup G) (hAB : A.pCoreIn 2 ≤ B) :
    (pCore 2 (coreClosure A B)).map (originalEmbedding A B) =
      (conjugateSpanBy (A.pCoreIn 2) B).pCoreIn 2 := by
  let e := coreClosureEquiv A B hAB
  have he := pCore_map_iso 2 e
  have hm := congrArg (map (conjugateSpanBy (A.pCoreIn 2) B).subtype) he
  rw [map_map] at hm
  exact hm

/-- The Baumann center closure maps to the literal original omega-center span. -/
theorem centerClosure_image (A B : Subgroup G) (hAB : A.pCoreIn 2 ≤ B) :
    (BaumannBinary.centerClosure (coreInClosure A B)).map (originalEmbedding A B) =
      conjugateSpanBy (omegaCenterIn (A.pCoreIn 2)) (conjugateSpanBy (A.pCoreIn 2) B) := by
  rw [BaumannBinary.centerClosure, map_normalClosure_eq_conjugateSpanBy_range,
    NilesRankOneKernel.omegaCenterIn_map_injective _ (originalEmbedding_injective A B),
    coreInClosure_image A B hAB, originalEmbedding_range A B hAB]
  rfl

/-- The intrinsic Sylow index is the relative index in the original completion. -/
theorem coreInClosure_index (A B : Subgroup G) (hAB : A.pCoreIn 2 ≤ B) :
    (coreInClosure A B).index = (A.pCoreIn 2).relIndex (conjugateSpanBy (A.pCoreIn 2) B) := by
  have hi := relIndex_map_map_of_injective (coreInClosure A B) ⊤
    (originalEmbedding_injective A B)
  rw [coreInClosure_image A B hAB, ← MonoidHom.range_eq_map,
    originalEmbedding_range A B hAB, relIndex_top_right] at hi
  exact hi.symm

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Characteristic two for the exact internal closure consumed by Baumann. -/
theorem selfCentralizing (h : LocallyRankOneTriple P B) (i : Fin 2) :
    centralizer (pCore 2 (coreClosure (P i) (P (other i))) :
      Set (coreClosure (P i) (P (other i)))) ≤ pCore 2 (coreClosure (P i) (P (other i))) := by
  have hAB : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans (Classical.choice (h.local_data (other i))).supplement.le)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (coreClosureEquiv (P i) (P (other i)) hAB)).mpr (core_closure_selfCentralizing h i)

/-- DGS 6.4(b) on the exact Baumann carrier, with printed relative normality. -/
theorem noCharacteristicNormal (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B) (i : Fin 2)
    (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    NoCharacteristicNormal (coreInClosure (P i) (P (other i))) := by
  have hAB : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans d.supplement.le)
  have hn' := (inter_core_local_normal_iff h i d).mp hn
  intro K hK hnK
  let := hK
  let := hnK
  let e := coreEquiv (P i) (P (other i)) hAB
  let D := K.map e.toMonoidHom
  let : D.Characteristic := characteristic_map_equiv e K
  have hm : D.map ((P i).pCoreIn 2).subtype =
      (K.map ((coreInClosure (P i) (P (other i))).subtype)).map
        (originalEmbedding (P i) (P (other i))) := by
    simp only [D, map_map]
    rfl
  have hnD : conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) ≤
      normalizer (D.map ((P i).pCoreIn 2).subtype : Set G) := by
    rw [hm]
    apply le_normalizer_iff.mpr
    intro g hg z hz
    rw [← coreClosure_image (P i) (P (other i)) hAB] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    obtain ⟨z', hz', rfl⟩ := hz
    let a : coreClosure (P i) (P (other i)) := ⟨g', hg'⟩
    refine mem_map.mpr ⟨a * z' * a⁻¹, Subgroup.Normal.conj_mem hnK z' hz' a, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  have hD := characteristic_core_eq_bot_of_inter_normal h hB i hn' D hnD
  exact (map_eq_bot_iff_of_injective _ e.injective).mp hD

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The full Baumann commutator in the original completion; only 6.4 Sylow and quotient inputs remain. -/
theorem source_baumann_commutator (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B) (i : Fin 2)
    (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (hs : ¬ 2 ∣ ((P i).pCoreIn 2).relIndex
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))))
    (q : coreClosure (P i) (P (other i)) →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (coreClosure (P i) (P (other i))))
    {n : ℕ} (hnpos : 0 < n) (hF : Nat.card F = 2^n) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    ⁅X.pCoreIn 2, X⁆ ≤ conjugateSpanBy (omegaCenterIn ((P i).pCoreIn 2)) X := by
  let := d.finite_P
  have hAB : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans d.supplement.le)
  have hindex : ¬ 2 ∣ (coreInClosure (P i) (P (other i))).index := by
    rwa [coreInClosure_index _ _ hAB]
  have hh := (source_conclusions (P i) (P (other i)) hAB hindex
    (selfCentralizing h i) (noCharacteristicNormal h hB i d hn) q hq hk hnpos hF).2.1
  have hm := map_mono (f := originalEmbedding (P i) (P (other i))) hh
  rwa [map_commutator, core_image _ _ hAB, ← MonoidHom.range_eq_map,
    originalEmbedding_range _ _ hAB, centerClosure_image _ _ hAB] at hm

/-- Equivariant natural coordinates with the same quotient map and full central kernel. -/
theorem source_baumann_natural (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B) (i : Fin 2)
    (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (hindex : ¬ 2 ∣ (coreInClosure (P i) (P (other i))).index)
    (q : coreClosure (P i) (P (other i)) →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (coreClosure (P i) (P (other i))))
    {n : ℕ} (hnpos : 0 < n) (hF : Nat.card F = 2^n) :
    letI := d.finite_P
    letI : IsElementaryAbelian 2 (BaumannBinary.centerClosure (coreInClosure (P i) (P (other i)))) :=
      (BaumannBinary.centerClosure_reduced (coreSylow (P i) (P (other i)) hindex)
        (selfCentralizing h i)).elementary
    let V := BaumannBinary.centerClosure (coreInClosure (P i) (P (other i)))
    ∃ f : Additive V →ₗ[ZMod 2] (Fin 2 → F), Function.Surjective f ∧
      LinearMap.ker f = Representation.NormalElementaryQuotient.subspace V
        ((V ⊓ center (coreClosure (P i) (P (other i)))).subgroupOf V) ∧
      ∀ g v, f (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        Matrix.mulVec (q g).val (f v) := by
  let := d.finite_P
  have hAB : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans d.supplement.le)
  exact (natural_projection_all (P i) (P (other i)) hAB hindex
    (selfCentralizing h i) (noCharacteristicNormal h hB i d hn) q hq hk hnpos hF).2
end MarkedClosure
namespace Reduction
open CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Actual reduced F1.11 application, retaining the outstanding 6.4 Sylow and quotient premises. -/
theorem reduced_baumann_commutator (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (hs : ¬ 2 ∣ (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2).relIndex
      (conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
        ((P₀ L S (other i)).subgroupOf (G₀ L S))))
    (q : coreClosure ((P₀ L S i).subgroupOf (G₀ L S))
      ((P₀ L S (other i)).subgroupOf (G₀ L S)) →* SL(2,F))
    (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (coreClosure ((P₀ L S i).subgroupOf (G₀ L S))
      ((P₀ L S (other i)).subgroupOf (G₀ L S))))
    {n : ℕ} (hnpos : 0 < n) (hF : Nat.card F = 2^n) :
    let X := conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
      ((P₀ L S (other i)).subgroupOf (G₀ L S))
    ⁅X.pCoreIn 2, X⁆ ≤
      conjugateSpanBy (omegaCenterIn (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)) X :=
  MarkedClosure.source_baumann_commutator (reduced_triple h) (reduced_borel_core_sylow h) i
    (Classical.choice ((reduced_triple h).local_data (other i))) hn hs q hq hk hnpos hF
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85

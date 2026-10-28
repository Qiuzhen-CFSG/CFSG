module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ContainedNormalizer
public import Theory.SpecificGroups.PSL3.EvenLocalNormalizers
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PCoreImage

/-!
# The original binary PSL3 component local conditions

The concrete characteristic-two local theorem transports through the
literal component embedding. In the contained branch, the earlier source
Borel intersection identifies its core as a Sylow subgroup; saturation
therefore makes the actual component radical Sylow too.

Source: Aschbacher--Smith 2.5.2(2) and 2.5.3(4), printed pp.551--553.
The actual Borel identification remains the preceding source input.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

omit [Finite G] in

/-- Every nontrivial two-subgroup normalizer in an actual binary PSL3
component lies in He, with both ambient embeddings retained. -/
theorem linear_even_normalizer_mem_He
    (D : Subgroup H) (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : D ≃* PSL(3,F))
    (R : Subgroup D) (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    ((normalizer (R : Set D)).map D.subtype).map H.subtype ∈ Chapter1.He G := by
  have hmap : R.map e.toMonoidHom ≠ ⊥ := by
    intro hb
    apply hne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa using hb
  have hc := normalizer_core_selfCentralizing_of_equiv e R
    (Matrix.PSL3.EvenInnerCentralizers.normalizer_core_selfCentralizing F hn hF
      (R.map e.toMonoidHom) (hp.map e.toMonoidHom) hmap)
  apply Chapter1.mem_He_iff.mpr
  let j := (equivMapOfInjective (normalizer (R : Set D)) D.subtype D.subtype_injective).trans
    (equivMapOfInjective ((normalizer (R : Set D)).map D.subtype) H.subtype H.subtype_injective)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 j).mp hc

/-- The preceding literal Borel intersection discharges the Sylow requirement
in the source contained-normalizer branch. -/
theorem linear_even_contained_source_sylow
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : D ≃* PSL(3,F))
    (hB : (((M.subgroupOf H).subgroupOf D).map e.toMonoidHom) = Matrix.PSL3.LinearThree.borel F)
    (hinside : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    ∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = D ⊓ (twoCore HU).subgroupOf H := by
  let I := (M.subgroupOf H).subgroupOf D
  let Q := (twoCore HU).subgroupOf H
  let S := Matrix.PSL3.LinearThree.unipotentSylow F hn hF
  let P := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcore : (I.pCoreIn 2).map e.toMonoidHom = Matrix.PSL3.LinearThree.unipotent F := by
    rw [map_pCoreIn_of_injective 2 I e.toMonoidHom e.injective, hB]
    rw [pCoreIn, Matrix.PSL3.CartanActions.BorelQuotient.twoCore_eq F hF,
      map_subgroupOf_eq_of_le (Matrix.PSL3.LinearThree.unipotent_le_borel F)]
  have hP : (P : Subgroup D) = I.pCoreIn 2 := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hcore]
    change ((S : Subgroup PSL(3,F)).map e.symm.toMonoidHom).map e.toMonoidHom = _
    have hei : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
      ext x; exact e.apply_symm_apply x
    rw [map_map, hei, map_id, Matrix.PSL3.LinearThree.coe_unipotentSylow]
  have hPR : (P : Subgroup D) ≤ Q.subgroupOf D := hP.le.trans
    (intersection_core_le_saturated_component_of_normalizer_le hpair hsat D hD hinside)
  have heq : Q.subgroupOf D = (P : Subgroup D) :=
    P.is_maximal' (isPGroup_pCoreIn 2 HU).comap_subtype.comap_subtype hPR
  refine ⟨P, ?_⟩
  rw [← heq, subgroupOf_map_subtype, inf_comm]

/-- The original saturated component radical contains every normal two-subgroup
of the component, including a binary-cover kernel, even if H permutes D. -/
theorem component_twoCore_le_saturated_intersection
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D) :
    pCore 2 D ≤ ((twoCore HU).subgroupOf H).subgroupOf D := by
  let Q := (twoCore HU).subgroupOf H
  have hsatH : ∀ P : Subgroup H, IsPGroup 2 P →
      HU.subgroupOf H ≤ normalizer (P : Set H) → P ≤ Q := by
    intro P hp hn x hx
    have hna : HU ≤ normalizer (P.map H.subtype : Set G) := by
      intro a ha
      exact P.le_normalizer_map H.subtype ⟨⟨a, hpair.2 ha⟩, hn ha, rfl⟩
    exact hsat _ (map_subtype_le P) (hp.map H.subtype) hna
      (mem_map_of_mem H.subtype hx)
  have hc : D.pCoreIn 2 ≤ Q := hD.stabilizer_saturation hsatH _
    (pCoreIn_le 2 D) (isPGroup_pCoreIn 2 D)
    (inf_le_right.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))
  intro x hx
  exact hc (mem_map_of_mem D.subtype hx)

/-- Binary covers satisfy the literal local He assertion once the radical's
projective image is nontrivial. Kernel containment is proved by saturation;
it is not an additional source input. -/
theorem linear_even_cover_radical_mem_He
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (f : D →* PSL(3,F)) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hne : ((((twoCore HU).subgroupOf H).subgroupOf D).map f) ≠ ⊥) :
    (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ∈ Chapter1.He G := by
  let Q := (twoCore HU).subgroupOf H
  let R := Q.subgroupOf D
  have hker : f.ker ≤ R := (le_sSup ⟨inferInstance, hk⟩ : f.ker ≤ pCore 2 D).trans
    (component_twoCore_le_saturated_intersection hpair hsat D hD)
  have hc := Matrix.PSL3.EvenInnerCentralizers.cover_normalizer_core_selfCentralizing F
    f hf hk hn hF R (isPGroup_pCoreIn 2 HU).comap_subtype.comap_subtype hker hne
  have hnorm : (normalizer (R : Set D)).map D.subtype = D ⊓ normalizer ((D ⊓ Q : Subgroup H) : Set H) := by
    have he : R = (D ⊓ Q).subgroupOf D := by ext x; simp [R]
    rw [he, ← subgroupOf_normalizer_eq (show D ⊓ Q ≤ D from inf_le_left),
      subgroupOf_map_subtype, inf_comm]
  apply Chapter1.mem_He_iff.mpr
  let j := (equivMapOfInjective (normalizer (R : Set D)) D.subtype D.subtype_injective).trans
    (equivMapOfInjective ((normalizer (R : Set D)).map D.subtype) H.subtype H.subtype_injective)
  have hh := (Theory.Quasithin.centralizer_pCore_le_iff 2 j).mp hc
  rwa [hnorm] at hh

/-- The Borel-intersection reduction also handles the full binary cover.
Its two-kernel already lies in the saturated radical, and preimage of the
actual unipotent Sylow is Sylow in the cover. -/
theorem linear_even_cover_contained_source_sylow
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (f : D →* PSL(3,F)) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hB : (((M.subgroupOf H).subgroupOf D).map f) = Matrix.PSL3.LinearThree.borel F)
    (hinside : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    ∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = D ⊓ (twoCore HU).subgroupOf H := by
  let I := (M.subgroupOf H).subgroupOf D
  let Q := (twoCore HU).subgroupOf H
  let R := Q.subgroupOf D
  let S := Matrix.PSL3.LinearThree.unipotentSylow F hn hF
  let P := S.comapOfKerIsPGroup f hk (by rw [f.range_eq_top_of_surjective hf]; exact le_top)
  have hker : f.ker ≤ R := (le_sSup ⟨inferInstance, hk⟩ : f.ker ≤ pCore 2 D).trans
    (component_twoCore_le_saturated_intersection hpair hsat D hD)
  have hcore : (I.pCoreIn 2).map f = Matrix.PSL3.LinearThree.unipotent F := by
    rw [map_pCoreIn_of_ker_isPGroup f hk I, hB]
    rw [pCoreIn, Matrix.PSL3.CartanActions.BorelQuotient.twoCore_eq F hF,
      map_subgroupOf_eq_of_le (Matrix.PSL3.LinearThree.unipotent_le_borel F)]
  have hSR : (S : Subgroup PSL(3,F)) ≤ R.map f := by
    rw [Matrix.PSL3.LinearThree.coe_unipotentSylow, ← hcore]
    exact map_mono (intersection_core_le_saturated_component_of_normalizer_le hpair hsat D hD hinside)
  have hPR : (P : Subgroup D) ≤ R := by
    change (S : Subgroup PSL(3,F)).comap f ≤ R
    exact (comap_mono hSR).trans (Subgroup.comap_map_eq_self hker).le
  have heq : R = (P : Subgroup D) :=
    P.is_maximal' (isPGroup_pCoreIn 2 HU).comap_subtype.comap_subtype hPR
  refine ⟨P, ?_⟩
  rw [← heq, subgroupOf_map_subtype, inf_comm]

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection

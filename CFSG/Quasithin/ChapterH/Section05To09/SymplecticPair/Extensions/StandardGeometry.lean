module

public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry
public import CFSG.Quasithin.ChapterE.Section04.Basic

/-!
# Inner reductions for the standard H.7 action

The genuine E.3.8 family first excludes summand interchange, using the actual
index-two stabilizer. Its coefficient-kernel intersection also has corank at
most one. That intersection fixes a nonzero F-linear space, so equality of
fixed spaces excludes a nontrivial field actor.

Injective pullback to the full Sp₄ carrier preserves every relevant subgroup,
relative index and fixed space. This gives native reductions for E.3.8
emptiness, the minimum involution codimension, and the (F−1) exclusion.
The scalar-kernel and numerical overgroup calculations are explicit inputs
in the reductions that still need them. Native paired-module conclusions
also remain explicit inputs, owned by the independent inner-geometry work.
No theorem here asserts completion of H.7 from those pending inputs.

Source: Aschbacher–Smith H.7, printed pp.388–389, and E.3.8, printed p.232,
of `refs/quasithin.pdf`.
-/

@[expose] public section

open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair SymplecticConjugatePair.Ambient
namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair

lemma family_comap_of_le_range {G D V : Type*} [Group G] [Group D]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (f : G →* D) (hf : Function.Injective f)
    {A : Subgroup D} {k : ℕ} (hA : A ∈ ChapterE.fixedSpaceFamily ρ k)
    (hArange : A ≤ f.range) :
    A.comap f ∈ ChapterE.fixedSpaceFamily (ρ.comp f) k := by
  have hmap : (A.comap f).map f = A := Subgroup.map_comap_eq_self hArange
  refine ⟨hA.1, elementary_preimage f hf hA.2.1 hArange, ?_⟩
  intro B hB hidx
  have hBA : B.map f ≤ A := Subgroup.map_le_iff_le_comap.mpr hB
  have hi : Nat.log 2 ((B.map f).relIndex A) < k := by
    rw [← hmap, Subgroup.relIndex_map_map_of_injective _ _ hf]
    exact hidx
  rw [fixedSpace_comp_map, fixedSpace_comp_map, hmap]
  exact hA.2.2 (B.map f) hBA hi

lemma family_le_coefficient_kernel {F G V : Type*} [Field F] [Finite F] [Group G]
    [AddCommGroup V] [Module F V] [Module (ZMod 2) V] [Nontrivial V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (π : G →* (F ≃+* F))
    (hsemi : ∀ g : G, ∀ (c : F) (v : V), ρ g (c • v) = π g c • ρ g v)
    {A : Subgroup G} {k : ℕ} (hk : 1 < k)
    (hA : A ∈ ChapterE.fixedSpaceFamily ρ k) : A ≤ π.ker := by
  let _ : IsElementaryAbelian 2 A := hA.2.1.2
  let B := A ⊓ π.ker
  have hi : B.relIndex A ≤ 2 :=
    SemilinearCoefficients.kernel_relativeIndex_le_two π hA.2.1.2
  have hlog : Nat.log 2 (B.relIndex A) < k := by
    have h := Nat.log_mono_right (b := 2) hi
    norm_num at h
    omega
  have hB : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 A).of_injective
    (Subgroup.inclusion (show B ≤ A from inf_le_left)) (Subgroup.inclusion_injective _)
  exact SemilinearCoefficients.le_kernel_of_fixedSpace_eq ρ π hsemi hB inf_le_right
    (hA.2.2 B inf_le_left hlog)

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F] [CharP F 2]

lemma standard_family_le_stabilizer {k : ℕ} (hk : 1 < k)
    {A : Subgroup (standardAmbient (F := F))}
    (hA : A ∈ ChapterE.fixedSpaceFamily standardAction k) : A ≤ standardPreserving := by
  let _ : IsElementaryAbelian 2 A := hA.2.1.2
  let N := standardPreserving (F := F)
  have hn : N.index = 2 := standard_stabilizer_index_two
  let _ : N.Normal := N.normal_of_index_eq_two hn
  let B := A ⊓ N
  have hi : B.relIndex A ≤ 2 := by
    have hdiv := N.relIndex_dvd_index_of_normal A
    rw [hn, ← Subgroup.inf_relIndex_left] at hdiv
    exact Nat.le_of_dvd (by decide) hdiv
  have hc : Nat.log 2 (B.relIndex A) < k := by
    have hlog := Nat.log_mono_right (b := 2) hi
    norm_num at hlog
    omega
  have heq := hA.2.2 B inf_le_left hc
  by_contra hAN
  obtain ⟨s, hsA, hsN⟩ := SetLike.not_le_iff_exists.mp hAN
  have hB : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 A).of_injective
    (Subgroup.inclusion (show B ≤ A from inf_le_left)) (Subgroup.inclusion_injective _)
  exact fixedSpace_ne_of_swapping standardAction hB (show B ≤ N from inf_le_right) hsA
    (swaps_of_not_mem_stabilizer standardAction standardAction_permutesSummands hsN) heq

/-- The actual coefficient field acts trivially on every E.3.8 member with
parameter greater than one, after restricting to the actual summand stabilizer. -/
lemma standard_family_le_coefficient_kernel {k : ℕ} (hk : 1 < k)
    {A : Subgroup (standardAmbient (F := F))}
    (hA : A ∈ ChapterE.fixedSpaceFamily standardAction k) :
    A.subgroupOf standardPreserving ≤ standardCoefficient.ker := by
  have hAN := standard_family_le_stabilizer hk hA
  have hArange : A ≤ (standardPreserving (F := F)).subtype.range := by
    simpa only [Subgroup.range_subtype] using hAN
  have hfamily := family_comap_of_le_range standardAction standardPreserving.subtype
    standardPreserving.subtype_injective hA hArange
  exact family_le_coefficient_kernel (standardAction.comp standardPreserving.subtype)
    standardCoefficient standardCoefficient_smul hk hfamily

lemma standard_family_le_full_of_coefficients
    (π : standardPreserving (F := F) →* (F ≃+* F))
    (hsemi : ∀ g : standardPreserving (F := F), ∀ (c : F) (v : Space F),
      standardAction g.val (c • v) = π g c • standardAction g.val v)
    (hker : ∀ g : standardPreserving (F := F), g^2 = 1 → π g = 1 → g.val ∈ fullHom.range)
    {k : ℕ} (hk : 1 < k) {A : Subgroup (standardAmbient (F := F))}
    (hA : A ∈ ChapterE.fixedSpaceFamily standardAction k) : A ≤ fullHom.range := by
  let N := standardPreserving (F := F)
  have hAN : A ≤ N := standard_family_le_stabilizer hk hA
  have hArange : A ≤ N.subtype.range := by simpa only [Subgroup.range_subtype] using hAN
  have hfamily := family_comap_of_le_range standardAction N.subtype N.subtype_injective hA hArange
  have hlin := family_le_coefficient_kernel (standardAction.comp N.subtype) π hsemi hk hfamily
  let _ : IsElementaryAbelian 2 A := hA.2.1.2
  intro a ha
  let g : N := ⟨a, hAN ha⟩
  apply hker g
  · apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian a ha
  · exact hlin (show g ∈ A.comap N.subtype from ha)

lemma standard_full_family_comap {k : ℕ} {A : Subgroup (standardAmbient (F := F))}
    (hA : A ∈ ChapterE.fixedSpaceFamily standardAction k) (hAL : A ≤ fullHom.range) :
    A.comap fullHom ∈ ChapterE.fixedSpaceFamily graphPair k := by
  simpa only [standardAction_comp_fullHom] using
    family_comap_of_le_range standardAction fullHom fullHom_injective hA hAL

lemma standard_family_empty_of_inner_reduction {k : ℕ}
    (hinner : ∀ A ∈ ChapterE.fixedSpaceFamily (standardAction (F := F)) k, A ≤ fullHom.range)
    (hnative : ChapterE.fixedSpaceFamily (graphPair (F := F)) k = ∅) :
    ChapterE.fixedSpaceFamily (standardAction (F := F)) k = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  have h := standard_full_family_comap hA (hinner A hA)
  rw [hnative] at h
  exact h

lemma standard_family_two_n_empty_of_coefficients
    (π : standardPreserving (F := F) →* (F ≃+* F))
    (hsemi : ∀ g : standardPreserving (F := F), ∀ (c : F) (v : Space F),
      standardAction g.val (c • v) = π g c • standardAction g.val v)
    (hker : ∀ g : standardPreserving (F := F), g^2 = 1 → π g = 1 → g.val ∈ fullHom.range)
    {n : ℕ} (hn : 0 < n)
    (hnative : ChapterE.fixedSpaceFamily (graphPair (F := F)) (2*n) = ∅) :
    ChapterE.fixedSpaceFamily (standardAction (F := F)) (2*n) = ∅ :=
  standard_family_empty_of_inner_reduction
    (fun _ hA => standard_family_le_full_of_coefficients π hsemi hker (by omega) hA) hnative

lemma standard_family_le_full_of_kernel
    (hker : ∀ g : standardPreserving (F := F), g^2 = 1 →
      standardCoefficient g = 1 → g.val ∈ fullHom.range)
    {k : ℕ} (hk : 1 < k) {A : Subgroup (standardAmbient (F := F))}
    (hA : A ∈ ChapterE.fixedSpaceFamily standardAction k) : A ≤ fullHom.range :=
  standard_family_le_full_of_coefficients standardCoefficient standardCoefficient_smul hker hk hA

lemma standard_moduleM_lower_of_kernel
    (hker : ∀ g : standardPreserving (F := F), g^2 = 1 →
      standardCoefficient g = 1 → g.val ∈ fullHom.range)
    {n : ℕ} (hF : Nat.card F = 2^n)
    (hnative : ∀ x : Sp F, orderOf x = 2 →
      3*n ≤ fixedCodim graphPair (Subgroup.zpowers x)) :
    3*n ≤ ChapterE.moduleM (standardAction (F := F)) := by
  apply le_csInf ⟨Module.finrank (ZMod 2) (Space F), Set.mem_insert _ _⟩
  rintro d (rfl | ⟨s, hs, rfl⟩)
  · rw [finrank_space hF]
    omega
  · exact standard_involution_bound_of_kernel hker hF hnative s hs

lemma standard_not_offender_of_kernel_and_ranks
    (hker : ∀ g : standardPreserving (F := F), g^2 = 1 →
      standardCoefficient g = 1 → g.val ∈ fullHom.range)
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    (hc : ∀ s : standardAmbient (F := F), orderOf s = 2 → SwapsSummands standardAction s →
      primeRank 2 (Subgroup.centralizer ({s} : Set (standardAmbient (F := F)))) ≤ n+1)
    (hlarge : ∀ A : Subgroup (standardAmbient (F := F)), IsElementaryTwo A →
      A ≤ standardPreserving → 3*n-1 ≤ rank A → A ≤ fullHom.range)
    (hmin : ∀ x : Sp F, orderOf x = 2 → 3*n ≤ fixedCodim graphPair (Subgroup.zpowers x))
    (hnative : ∀ B : Subgroup (Sp F), IsElementaryTwo B →
      rank B + 1 < fixedCodim graphPair B)
    {A : Subgroup (standardAmbient (F := F))} (hA : IsElementaryTwo A) :
    rank A + 1 < fixedCodim standardAction A := by
  by_contra h
  have hoff := Nat.le_of_not_gt h
  have hAN := standard_offender_le_stabilizer hF hn hc hA hoff
  have hmA : ChapterE.moduleM (standardAction (F := F)) ≤ fixedCodim standardAction A :=
    ChapterE.moduleM_le_fixedCodim (standardAction (F := F)) hA
  have hm : 3*n ≤ fixedCodim standardAction A :=
    (standard_moduleM_lower_of_kernel hker hF hmin).trans hmA
  have hAL := hlarge A hA hAN (by omega)
  exact (full_not_offender hnative hA hAL).not_ge hoff

end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair

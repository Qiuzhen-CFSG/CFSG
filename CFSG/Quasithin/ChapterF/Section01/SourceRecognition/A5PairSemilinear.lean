module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5LocalFactorization
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.LocalExtension

/-!
# Semilinear reduction of the A5-pair containment

A marked local model identifies the literal group Li S with X semidirect A,
identifies Li with the embedded X, and records a surjective map from X to
PSL2(F4) with two-group kernel. The action of A is an injective coefficient
field action on this quotient. The field-action kernel calculation therefore
places the entire extension two-core in the original local subgroup.

The resulting equality of the two embedded cores gives S <= Lj at the
normalized Borel. F.1.3 then makes the entire common Borel normalize S,
allowing the same argument at the other index. Only one initial Borel
normalization is required, as in the source.

Constructing these marked models from F.1.1 remains the independent
nonsolvable rank-two recognition obligation `A5PairSemilinearRecognition`.
The theorems here prove the conditional implication used in the original
9.3.3 tensor consumer; they do not assert that recognition.

Source: Aschbacher--Smith, F.1.1 and F.1.12, printed pp.259 and 262--264.
The local semilinear kernel calculation is on printed p.264.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source

/-- A marked local semilinear realization, keeping the original local subgroup. -/
structure A5SemilinearLocalModel {H : Type*} [Group H] (K : Subgroup H) where
  base : Type
  [baseGroup : Group base]
  [baseFinite : Finite base]
  actor : Type
  [actorGroup : Group actor]
  [actorFinite : Finite actor]
  projection : base →* PSL(2, GaloisField 2 2)
  projection_surjective : Function.Surjective projection
  kernel_isTwo : IsPGroup 2 projection.ker
  action : actor →* MulAut base
  coefficient : actor →* (GaloisField 2 2 ≃+* GaloisField 2 2)
  coefficient_injective : Function.Injective coefficient
  equivariant : ∀ a x, projection (action a x) =
    Atlas.fieldEquivPSL 2 (coefficient a) (projection x)
  realization : H ≃* base ⋊[action] actor
  local_image : K.map realization.toMonoidHom =
    (SemidirectProduct.inl : base →* base ⋊[action] actor).range

attribute [instance] A5SemilinearLocalModel.baseGroup A5SemilinearLocalModel.baseFinite
  A5SemilinearLocalModel.actorGroup A5SemilinearLocalModel.actorFinite

/-- The faithful coefficient action prevents an extra two-core in the extension. -/
theorem A5SemilinearLocalModel.core_le {H : Type*} [Group H] {K : Subgroup H}
    (m : A5SemilinearLocalModel K) : pCore 2 H ≤ K := by
  intro x hx
  apply (Subgroup.mem_map_iff_mem (f := m.realization.toMonoidHom)
    m.realization.injective).mp
  rw [m.local_image]
  have hm : m.realization x ∈ pCore 2 (m.base ⋊[m.action] m.actor) := by
    rw [← pCore_map_iso 2 m.realization]
    exact mem_map_of_mem _ hx
  rw [Atlas.G2.LieAutomorphismExtensions.localExtension_twoCore_eq_map
    m.projection m.action m.coefficient m.equivariant
    m.projection_surjective m.coefficient_injective m.kernel_isTwo] at hm
  obtain ⟨y, _, hy⟩ := hm
  exact ⟨y, hy⟩

variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

omit [Finite G] in
/-- Both intrinsic cores are compared under their literal inclusions into G. -/
theorem HypothesisF11.a5_join_core_eq_of_semilinear_model
    (h : HypothesisF11 L S) (i : Fin 2)
    (m : A5SemilinearLocalModel ((L i).subgroupOf (L i ⊔ S))) :
    twoCore (L i ⊔ S) = twoCore (L i) := by
  have hle : twoCore (L i ⊔ S) ≤ L i := by
    rintro x ⟨y, hy, rfl⟩
    exact m.core_le hy
  apply le_antisymm
  · exact le_pCoreIn_of_normalizes (pCore_isPGroup.map (L i ⊔ S).subtype) hle
      ((le_sup_left.trans (L i ⊔ S).le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image (L i ⊔ S)
          (pCore 2 (L i ⊔ S : Subgroup G))))
  · exact le_pCoreIn_of_normalizes (pCore_isPGroup.map (L i).subtype)
      ((map_subtype_le _).trans le_sup_left)
      ((sup_le (L i).le_normalizer (h.S_normalizes i)).trans
        (normalizer_le_normalizer_characteristic_image (L i) (pCore 2 (L i))))

/-- The p.264 containment argument, starting with just one normalized Borel. -/
theorem HypothesisF11.a5_pair_containment_of_semilinear_models
    (h : HypothesisF11 L S)
    (he : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (hn : ∃ j, borel (L j) S ≤ normalizer (S : Set G))
    (hm : ∀ i, Nonempty (A5SemilinearLocalModel ((L i).subgroupOf (L i ⊔ S)))) :
    ∀ i, S ≤ L i := by
  obtain ⟨j, hj⟩ := hn
  obtain ⟨ej⟩ := he j
  obtain ⟨mj⟩ := hm j
  have hSj : S ≤ L j := (h.a5_local_containment_iff_core_eq j ej hj).mpr
    (h.a5_join_core_eq_of_semilinear_model j mj)
  have hB : commonBorel L S ≤ normalizer (S : Set G) := by
    simpa only [inf_eq_left.mpr hSj] using h.commonBorel_normalizes_localSylow j
  intro i
  obtain ⟨ei⟩ := he i
  obtain ⟨mi⟩ := hm i
  exact (h.a5_local_containment_iff_core_eq i ei ((borel_le_commonBorel i).trans hB)).mpr
    (h.a5_join_core_eq_of_semilinear_model i mi)

/-- The remaining recognition obligation, with actual marked local isomorphisms. -/
def A5PairSemilinearRecognition (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (L : Fin 2 → Subgroup G) (S : Subgroup G),
    HypothesisF11 L S → IsQuasithin (generated L S) →
    (∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))) →
    (∃ j, borel (L j) S ≤ normalizer (S : Set G)) →
    ∀ i, Nonempty (A5SemilinearLocalModel ((L i).subgroupOf (L i ⊔ S)))

/-- The exact A5/A5 containment interface once marked recognition is supplied. -/
theorem a5_pair_containment_of_semilinear_recognition
    (recognition : A5PairSemilinearRecognition G)
    (h : HypothesisF11 L S) (hqt : IsQuasithin (generated L S))
    (he : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (hn : ∃ j, borel (L j) S ≤ normalizer (S : Set G)) : ∀ i, S ≤ L i :=
  h.a5_pair_containment_of_semilinear_models he hn (recognition L S h hqt he hn)

end CFSG.Quasithin.ChapterF.Source

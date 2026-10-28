module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsSingularComponentsCore
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.OddCore
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality

/-!
# The actual normal singular overcomponent containing the common HS residual

The original singular centralizer has an SQTK quotient by its two-core.
The same full ambient Sylow P restricts to a Sylow of that centralizer.
The proved 1.2.4 source therefore puts the literal P-local residual J in
a unique normal C-component K of G_z. This is containment J ≤ K, not an
identification of J with K. All embeddings are transported back through
the literal subgroup inclusion of G_z into G.

The final application retains the original returned pair, both Sylow
subgroups, and both points in the actual two-core, with no normality or
component-selection premise added to the original source hypotheses.

Source: Aschbacher--Smith 1.2.4, printed p.505, and the common subgroup
configuration in the original HS inspection for 12.6.12, pp.825--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Original 1.2.4 selects a unique actual normal overcomponent of a
P-normalized local member in the unchanged singular centralizer. -/
theorem SourceHypothesis.original_singular_normal_overcomponent
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hZ : ZV L V = ⊥) (z : V) (hz : z ≠ 1)
    (hHz : Gv (z : G) ∈ (D.fullSetup hZ T z).Hz)
    (P : Sylow 2 G) (hPz : (P : Subgroup G) ≤ Gv (z : G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LIn (Gv (z : G)) (P : Subgroup G))
    (hPJ : (P : Subgroup G) ≤ normalizer (J : Set G)) :
    ∃! K : Subgroup G, K ≤ Gv (z : G) ∧
      (K.subgroupOf (Gv (z : G))).IsCComponent ∧ J ≤ K ∧
      Gv (z : G) ≤ normalizer (K : Set G) := by
  let A := Gv (z : G)
  let S := P.subtype hPz
  have hloc : J.subgroupOf A ∈ Chapter1.L A (S : Subgroup A) := by
    exact (Chapter1.mem_LIn_iff_subgroupOf hPz hJ.1).mp hJ
  have hn : (S : Subgroup A) ≤ normalizer (J.subgroupOf A : Set A) := by
    rw [←subgroupOf_normalizer_eq hJ.1]
    exact comap_mono hPJ
  obtain ⟨K,⟨hK,hJK,hKn⟩,hunique⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (H.original_star_sqtk D hZ z hz hHz) S hloc hn
  let K₀ := K.map A.subtype
  have hKA : K₀ ≤ A := map_subtype_le K
  have he : K₀.subgroupOf A = K := by
    exact comap_map_eq_self_of_injective A.subtype_injective K
  have hnormal : (K₀.subgroupOf A).Normal := he.symm ▸ hKn
  have hJK₀ : J ≤ K₀ := by
    have hh := map_mono (f := A.subtype) hJK
    rwa [map_subgroupOf_eq_of_le hJ.1] at hh
  refine ⟨K₀,⟨hKA,he.symm ▸ hK,hJK₀,
    (normal_subgroupOf_iff_le_normalizer hKA).mp hnormal⟩,?_⟩
  intro E hE
  have hEn : (E.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hE.2.2.2
  have hEq := hunique (E.subgroupOf A) ⟨hE.2.1,comap_mono hE.2.2.1,hEn⟩
  have hh := congrArg (map A.subtype) hEq
  rw [map_subgroupOf_eq_of_le (show E ≤ A from hE.1)] at hh
  exact hh

/-- The original escaping HS configuration has a genuine normal C-component
of its singular centralizer containing the literal common A₅ residual. -/
theorem SourceHypothesis.exists_original_hs_singular_normal_overcomponent
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ hZ : ZV L V = ⊥, ∃ u w : V,
      D.Nonsingular u ∧ D.Nonsingular w ∧ w ≠ u ∧
      ∃ P : Sylow 2 G, ∃ t ∈ (P : Subgroup G),
        (MulAut.conj t) (u : G) = w ∧ (MulAut.conj t) (w : G) = u ∧
        let z := u*w
        z ≠ 1 ∧ ¬ D.Nonsingular z ∧
        (T : Subgroup G) ≤ Gv (z : G) ∧ (P : Subgroup G) ≤ Gv (z : G) ∧
        ¬ Gv (z : G) ≤ M L ∧ (D.fullSetup hZ T z).Gz ∈ (D.fullSetup hZ T z).Hz ∧
        (u : G) ∈ (Gv (z : G)).pCoreIn 2 ∧ (w : G) ∈ (Gv (z : G)).pCoreIn 2 ∧
        let B := Gv (u : G) ⊓ Gv (z : G)
        let J := (primeToResidual 3 B).map B.subtype
        J ≤ Kv (u : G) ⊓ Kv (w : G) ∧
        (P : Subgroup G) ≤ normalizer (J : Set G) ∧
        Group.IsPerfect J ∧ Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∧
        ∃! K : Subgroup G, K ≤ Gv (z : G) ∧
          (K.subgroupOf (Gv (z : G))).IsCComponent ∧ J ≤ K ∧
          Gv (z : G) ≤ normalizer (K : Set G) := by
  obtain ⟨hZ,u,w,hu,hw,huw,P,t,ht,htu,htw,hz,hs,hTz,hPz,hout,hHz,
    _,_,_,S,_,hJC,hPJ,hJ,hperf,hquot⟩ :=
    H.exists_original_hs_singular_local_component D hTV hTI v hv he
  have hpoint := H.original_hs_nonsingular_pair_mem_singular_core
    D hTV hTI v hv he hZ u w hu hw hz hs
  have hHz' : Gv ((u*w : V) : G) ∈ (D.fullSetup hZ T (u*w)).Hz := by
    rwa [(D.fullSetup hZ T (u*w)).Gz_eq] at hHz
  have hcomp := H.original_singular_normal_overcomponent D hZ (u*w) hz hHz' P hPz hJ hPJ
  exact ⟨hZ,u,w,hu,hw,huw,P,t,ht,htu,htw,hz,hs,hTz,hPz,hout,hHz,
    hpoint.2.2.2.1,hpoint.2.2.2.2,hJC,hPJ,hperf,hquot,hcomp⟩

end CFSG.Quasithin.Chapter12.Section06

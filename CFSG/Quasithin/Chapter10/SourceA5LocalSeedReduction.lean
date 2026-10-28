module
public import CFSG.Quasithin.Chapter10.SourceA5LocalSeedSplit
public import CFSG.Quasithin.Chapter10.SourceA5IrreducibleTwists
public import Theory.Representation.BinaryOffender.Homogeneous.ActiveFactorTwist
public import Theory.GroupTheory.ConjugateNormalizerIndexTwo

/-!
# A₅ normalizer stability of the original separated seed

When one of the two conjugate factors centralizes the chosen seed, its
central image is irreducible for the other factor. Every binary irreducible
A₅ module is invariant under all actor automorphisms. Correcting the original
normalizer action by this intertwiner and applying the given homogeneity
therefore proves that N_T(L) normalizes the original seed.

Both support orientations are retained. The final theorem applies the
original seed-splitting bridge to the literal originalMovedQuotientAction,
removing its normalizer-stability assumption. Only full/local module equality
and support separation remain explicit earlier-source inputs.

Source: the A₅ specialization of Aschbacher–Smith, D.3.5–6 and3.2.6,
combined manuscript, printed pp.195–196 and581; consumer10.1.1, p.741.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem seed_normalized_of_active_a5
    (A B S : Subgroup G) (hpair : A ⊔ B = localOrbit T L)
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5))
    (hB : D.seed ≤ centralizer (B : Set G))
    (hST : S ≤ T) (hSA : S ≤ normalizer (A : Set G))
    (hSB : S ≤ normalizer (B : Set G)) : S ≤ normalizer (D.seed : Set G) := by
  let H := localJoin T L
  let ρ := ReducedNormal.representation H
  have hAH : A ≤ H := (le_sup_left.trans hpair.le).trans le_sup_left
  have hBH : B ≤ H := (le_sup_right.trans hpair.le).trans le_sup_left
  have hpairH : A.subgroupOf H ⊔ B.subgroupOf H = (localOrbit T L).subgroupOf H := by
    rw [← subgroupOf_sup hAH hBH, hpair]
  have hfix : D.seedSpace ≤ fixedSpace ρ (B.subgroupOf H) := by
    intro v hv
    apply (ReducedNormal.mem_reduced_fixedSpace_iff H B hBH v).mpr
    exact hB (mem_map_of_mem H.subtype (mem_map_of_mem (ReducedNormal.ModuleGroup H).subtype hv))
  let eA := subgroupOfEquivOfLe hAH
  let eQ : ((A.subgroupOf H) ⧸ pCore 2 (A.subgroupOf H)) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans e
  intro s hs
  let sH : H := ⟨s, (show (T : Subgroup G) ≤ H from le_sup_right) (hST hs)⟩
  let sT : (T : Subgroup G).subgroupOf H := ⟨sH, hST hs⟩
  have hA : sH ∈ normalizer (A.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq hAH]
    exact hSA hs
  have hB' : sH ∈ normalizer (B.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq hBH]
    exact hSB hs
  have he := D.homogeneous.map_eq_of_active_factor_twist ρ sT
    (A.subgroupOf H) (B.subgroupOf H) hpairH hfix hA hB'
    (fun σ _ a => source_a5_irreducible_core_quotient_twist σ eQ a)
  have himage := congrArg (ReducedNormal.subspaceImage H) he
  rw [ReducedNormal.subspaceImage_map] at himage
  exact mem_normalizer_iff_map_conj_eq.mpr himage

/-- A separated original seed is normalized by the original factor stabilizer. -/
theorem source_a5_seed_normalizer_of_separated
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (D.seed : Set G) := by
  have hi := source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  have hp : L ⊔ L.map (MulAut.conj t).toMonoidHom = localOrbit T L :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G)) hi inf_le_right ht htn).symm
  have hnb := normalizes_conjugate_of_index_two L T hi ht
  rcases hsep with hsep | hsep
  · exact seed_normalized_of_active_a5 D L _ _ hp e hsep inf_le_left inf_le_right hnb
  · let f := L.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
    let eB := (QuotientGroup.congr _ _ f.symm (pCore_map_iso 2 f.symm)).trans e
    exact seed_normalized_of_active_a5 D _ L _ (by simpa only [sup_comm] using hp) eB hsep
      inf_le_left hnb inf_le_right

local instance localSeedReductionElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The exact original quotient and conjugate moved subgroup, with stability proved. -/
theorem source_a5_original_irreducible_of_separated_seed
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hfull : D.fullModule = D.moduleSubgroup)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    (originalMovedQuotientAction D e).IsIrreducible ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  source_a5_original_irreducible_of_local_seed_alternative D hn ht htn e hfull
    (source_a5_seed_normalizer_of_separated D hn ht htn e hsep) hsep

end CFSG.Quasithin.Chapter10

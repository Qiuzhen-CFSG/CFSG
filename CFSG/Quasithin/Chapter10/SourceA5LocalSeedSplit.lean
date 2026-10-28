module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.Recognition
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import Theory.GroupTheory.ReducedNormal.SubspaceMinimality
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.Representation.BinaryConjugationSection.Irreducible

/-!
# The original moved quotient after local seed splitting

The two local conclusions needed from D.3.5–6 are explicit: the chosen seed
is centralized by the opposite component and is invariant under N_T(L).
The index-two orbit then identifies [V,L] with that very seed. Irr⁺
minimality in the original reduced subgroup proves irreducibility of the
literal marked central quotient, and conjugation gives cross-centralization.

This is the final implication in the proper-seed branch of3.2.6, not a
proof of the earlier quadratic-ratio exclusions. In particular a component
pair or full-module equality alone is not used to assert seed splitting.
Source: Aschbacher–Smith, D.3.6 and3.2.6, printed pp.196 and581;
the quotient recognition consumer is10.1.1, printed p.741.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))

include D hn ht htn in
private theorem original_pair :
    localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
  componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
    inf_le_right ht htn

include hn ht in
/-- The opposite seed centralizer conjugates back to the original component. -/
theorem source_local_seed_conjugate_centralizes
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G)) :
    D.seed.map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  have hsquare := conjugate_twice_eq_of_index_two L T (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
    inf_le_right ht
  have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hsep
  rw [Theory.GroupTheory.map_centralizer_equiv] at hh
  change D.seed.map (MulAut.conj t).toMonoidHom ≤
    centralizer (((L.map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj t).toMonoidHom) : Set G) at hh
  rwa [hsquare] at hh

include hn ht htn in
/-- The exact local splitting conclusions identify the original moved factor
with the original homogeneous seed. -/
theorem source_local_moved_eq_seed
    (hfull : D.fullModule = D.moduleSubgroup)
    (hstab : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (D.seed : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G)) :
    ⁅D.fullModule,L⁆ = D.seed := by
  have hpair := original_pair D hn ht htn
  have hseed : D.seed = ⁅D.seed,localOrbit T L⁆ :=
    ReducedNormal.subspaceImage_eq_commutator (localJoin T L) D.seedSpace
      (localOrbit T L) le_sup_left D.homogeneous.invariant
      D.homogeneous.isIrrPlus.choose_spec.1
  have hLS : L ≤ normalizer (D.seed : Set G) :=
    (le_componentOrbit L T).trans D.orbit_normalizes_seed
  have hcomm : ⁅D.seed,L⁆ = D.seed := by
    rw [commutator_eq_of_centralizing_sup (by simpa only [sup_comm] using hpair.symm)
      (le_centralizer_iff.mp hsep) hLS, ←hseed]
  have hsplit : D.moduleSubgroup = D.seed ⊔ D.seed.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two D.seed T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      hstab ht htn
  have hSL : D.seed ≤ normalizer (L : Set G) :=
    (le_componentOrbit D.seed T).trans
      (D.module_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
  have hc := commutator_eq_of_centralizing_sup
    (by simpa only [sup_comm] using hsplit.symm)
    (source_local_seed_conjugate_centralizes D hn ht hsep) hSL
  rw [hfull,commutator_comm,←hc,commutator_comm,hcomm]

include hn ht htn in
/-- The original seed has no proper noncentral L-invariant subgroup once
the opposite factor centralizes it. -/
theorem source_local_seed_minimal
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G))
    (J : Subgroup G) (hJS : J ≤ D.seed) (hLJ : L ≤ normalizer (J : Set G)) :
    J = D.seed ∨ J ≤ centralizer (L : Set G) := by
  have hpair := original_pair D hn ht htn
  have hBJ : L.map (MulAut.conj t).toMonoidHom ≤ normalizer (J : Set G) :=
    ((le_centralizer_iff.mp hsep).trans (centralizer_le hJS)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hOJ : localOrbit T L ≤ normalizer (J : Set G) := by
    rw [hpair]
    exact sup_le hLJ hBJ
  rcases ReducedNormal.subspaceImage_eq_or_le_centralizer (localJoin T L)
      (localOrbit T L) le_sup_left D.homogeneous.isIrrPlus J hJS hOJ with he | hc
  · exact Or.inl he
  · exact Or.inr (hc.trans (centralizer_le (le_componentOrbit L T)))

local instance localSeedMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

private theorem original_quotient_irreducible_of_subgroup_minimal
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hmin : ∀ J : Subgroup G, J ≤ ⁅D.fullModule,L⁆ → L ≤ normalizer (J : Set G) →
      J = ⁅D.fullModule,L⁆ ∨ J ≤ centralizer (L : Set G)) :
    (originalMovedQuotientAction D e).IsIrreducible := by
  let Q := Additive ((⁅D.fullModule,L⁆ : Subgroup G) ⧸
    (sourceMovedFixed D).subgroupOf ⁅D.fullModule,L⁆)
  have : Nontrivial Q := by
    by_contra h
    let : Subsingleton Q := not_nontrivial_iff_subsingleton.mp h
    let : Subsingleton (alternatingGroup (Fin 5)) :=
      Function.Injective.subsingleton (originalMovedQuotientAction_faithful D e)
    exact false_of_nontrivial_of_subsingleton (alternatingGroup (Fin 5))
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  apply (Representation.irreducible_comp_surjective_iff π
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) _).mp
  apply (originalMovedQuotientSection D e).irreducible_of_subgroup_minimal
  intro J hJW hLJ
  rcases hmin J hJW hLJ with he | hc
  · exact Or.inl he
  · exact Or.inr (le_inf hJW hc)

include hn ht htn in
/-- The oriented proper-seed branch feeds the literal original quotient action;
no irreducibility or model-coordinate hypothesis is assumed. -/
theorem source_a5_original_irreducible_of_local_seed_split
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hfull : D.fullModule = D.moduleSubgroup)
    (hstab : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (D.seed : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G)) :
    (originalMovedQuotientAction D e).IsIrreducible ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  have hW := source_local_moved_eq_seed D hn ht htn hfull hstab hsep
  refine ⟨?_, by rw [hW]; exact source_local_seed_conjugate_centralizes D hn ht hsep⟩
  apply original_quotient_irreducible_of_subgroup_minimal D e
  intro J hJW hLJ
  rw [hW] at hJW ⊢
  exact source_local_seed_minimal D hn ht htn hsep J hJW hLJ

include hn ht htn in
private theorem opposite_seed_movement_and_minimality
    (hfull : D.fullModule = D.moduleSubgroup)
    (hstab : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (D.seed : Set G))
    (hsep : D.seed ≤ centralizer (L : Set G)) :
    ⁅D.fullModule,L⁆ = D.seed.map (MulAut.conj t).toMonoidHom ∧
      ∀ J : Subgroup G, J ≤ ⁅D.fullModule,L⁆ → L ≤ normalizer (J : Set G) →
        J = ⁅D.fullModule,L⁆ ∨ J ≤ centralizer (L : Set G) := by
  let H := localJoin T L
  let τ := ReducedNormal.representation H
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let I := D.seedSpace.map (τ tH)
  let U := D.seed.map (MulAut.conj t).toMonoidHom
  have hi : IsIrrPlus τ ((localOrbit T L).subgroupOf H) I :=
    D.homogeneous.isIrrPlus.map_normalizer τ
      (D.homogeneous.normalizes (show tH ∈ (T : Subgroup G).subgroupOf H from ht))
  have himage : ReducedNormal.subspaceImage H I = U :=
    ReducedNormal.subspaceImage_map H D.seedSpace tH
  have hpair := original_pair D hn ht htn
  have hsep' : U ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hsep
    rw [Theory.GroupTheory.map_centralizer_equiv] at hh
    exact hh
  have hUO : U = ⁅U,localOrbit T L⁆ := by
    have hh := ReducedNormal.subspaceImage_eq_commutator H I (localOrbit T L)
      le_sup_left hi.choose hi.choose_spec.1
    rwa [himage] at hh
  have hOU : localOrbit T L ≤ normalizer (U : Set G) := by
    rw [←himage]
    exact ReducedNormal.subspaceImage_normalizes H (localOrbit T L) le_sup_left I hi.choose
  have hcomm : ⁅U,L⁆ = U := by
    rw [commutator_eq_of_centralizing_sup (by simpa only [sup_comm] using hpair.symm)
      (le_centralizer_iff.mp hsep') ((le_componentOrbit L T).trans hOU), ←hUO]
  have hsplit : D.moduleSubgroup = D.seed ⊔ U :=
    componentOrbit_eq_sup_of_index_two D.seed T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      hstab ht htn
  have hUL : U ≤ normalizer (L : Set G) :=
    ((le_sup_right : U ≤ D.seed ⊔ U).trans hsplit.ge).trans
      (D.module_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
  have hW : ⁅D.fullModule,L⁆ = U := by
    have hc := commutator_eq_of_centralizing_sup hsplit.symm hsep hUL
    rw [hfull,commutator_comm,←hc,commutator_comm,hcomm]
  refine ⟨hW,?_⟩
  intro J hJW hLJ
  have hJU : J ≤ U := hJW.trans_eq hW
  have hBJ : L.map (MulAut.conj t).toMonoidHom ≤ normalizer (J : Set G) :=
    ((le_centralizer_iff.mp hsep').trans (centralizer_le hJU)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hOJ : localOrbit T L ≤ normalizer (J : Set G) := by
    rw [hpair]
    exact sup_le hLJ hBJ
  rcases ReducedNormal.subspaceImage_eq_or_le_centralizer H (localOrbit T L)
      le_sup_left hi J (hJU.trans_eq himage.symm) hOJ with he | hc
  · exact Or.inl ((he.trans himage).trans hW.symm)
  · exact Or.inr (hc.trans (centralizer_le (le_componentOrbit L T)))

include hn ht htn in
/-- Either seed orientation gives irreducibility and cross-centralization
for the same original D, L, e and quotient action. -/
theorem source_a5_original_irreducible_of_local_seed_alternative
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hfull : D.fullModule = D.moduleSubgroup)
    (hstab : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (D.seed : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    (originalMovedQuotientAction D e).IsIrreducible ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  rcases hsep with hsep | hsep
  · exact source_a5_original_irreducible_of_local_seed_split D hn ht htn e hfull hstab hsep
  · obtain ⟨hW,hmin⟩ := opposite_seed_movement_and_minimality D hn ht htn hfull hstab hsep
    refine ⟨original_quotient_irreducible_of_subgroup_minimal D e hmin,?_⟩
    rw [hW,conjugate_twice_eq_of_index_two D.seed T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn) hstab ht]
    exact hsep

end CFSG.Quasithin.Chapter10

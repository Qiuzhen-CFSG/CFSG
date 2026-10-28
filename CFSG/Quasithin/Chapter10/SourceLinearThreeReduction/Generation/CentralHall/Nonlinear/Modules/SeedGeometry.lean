module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.Contracts
public import CFSG.Quasithin.Chapter10.SourceA5LocalSeedSplit
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction

/-!
# From the original separated seed to the nonlinear moved subgroup

The index-two stabilizer identifies the moved subgroup with either the
original homogeneous seed or its exchanged conjugate. Irr⁺ minimality then
gives subgroup minimality above its centralizer. Conjugation yields crossed
centralization for the chosen exchanger, and the two-element component orbit
extends it to every original Sylow exchanger.

The proof uses only the group-independent seed lemmas from
`SourceA5LocalSeedSplit`; it requires no A₅ marking. The earlier seed separation,
stability and full/local equality remain explicit, as does module recognition.
Source: Aschbacher--Smith D.3.6 and 3.2.6(3), pp.196,581;
application to the literal subgroups of 10.1.1, p.741.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- All original Sylow exchangers give the same conjugate moved subgroup.
Thus crossed centralization for one of them suffices for the full geometry. -/
theorem crossed_of_one {t : G} (ht : t ∈ (T : Subgroup G))
    (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G)) :
    ∀ s ∈ (T : Subgroup G), s ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj s).toMonoidHom ≤ centralizer (L : Set G) := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hmaps (s : G) (hs : s ∈ (T : Subgroup G)) :
      D.fullModule.map (MulAut.conj s).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule (hTM hs))
  intro s hs hsn
  have he : L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom := by
    rcases source_nonnormal_maximal_pair D hn ht htn s (hTM hs) with he | he
    · exact (hsn (mem_normalizer_iff_map_conj_eq.mpr he)).elim
    · exact he
  rw [map_commutator,hmaps s hs,he]
  simpa only [map_commutator,hmaps t ht] using hcross

private theorem opposite_movement_and_minimality
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hfull : D.fullModule = D.moduleSubgroup)
    (hstab : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (D.seed : Set G))
    (hsep : D.seed ≤ centralizer (L : Set G)) :
    ⁅D.fullModule,L⁆ = D.seed.map (MulAut.conj t).toMonoidHom ∧ MovedMinimal D := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
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
  have hpair : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn
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

/-- The original separated seed gives the required geometry and the literal
moved-quotient minimality in either orientation, for the unchanged setup D. -/
theorem geometry_and_minimality_of_separatedSeed
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (h : SeparatedSeed D t) : ModuleGeometry D ∧ MovedMinimal D := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hlocal :
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) ∧
        MovedMinimal D := by
    rcases h.separated with hs | hs
    · have he := source_local_moved_eq_seed D hn ht htn h.full_eq_local h.stable hs
      refine ⟨?_,?_⟩
      · rw [he]
        exact source_local_seed_conjugate_centralizes D hn ht hs
      · intro J hJW hLJ
        rw [he] at hJW ⊢
        exact source_local_seed_minimal D hn ht htn hs J hJW hLJ
    · obtain ⟨he,hmin⟩ := opposite_movement_and_minimality D ht htn
        h.full_eq_local h.stable hs
      refine ⟨?_,hmin⟩
      rw [he,conjugate_twice_eq_of_index_two D.seed T (normalizer (L : Set G))
        (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn) h.stable ht]
      exact hs
  exact ⟨⟨h.full_eq_local,crossed_of_one D ht htn hlocal.1⟩,hlocal.2⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules

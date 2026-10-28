module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupNatural
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalInitial
public import Theory.GroupTheory.ReducedNormal.SubspaceIrreducible

/-!
# The actual FSU seed in odd field degree

The odd-degree Sylow factorization makes the original FSU seed T-invariant:
T ∩ L normalizes it and O₂(LT) centralizes every reduced-module subspace.
Thus V = V◦. The vanishing of C_{Ω₁(Z(T))}(L) removes the fixed kernel,
and the Irr⁺ hypothesis then gives irreducibility on this literal subgroup.
Its intersecting normalizer conjugates coincide. A natural marking of its
fixed quotient consequently lifts to the entire original module.

This proves the irreducibility and fixed-kernel steps of 5.1.17 without
assuming the natural classification. That classification, global TI of Z₁,
and the F.8 construction remain with qt-d-1222-linear-field-parity.
Source: Aschbacher–Smith, 5.1.17, printed p.640 (refs/quasithin.pdf),
using the FSU of 3.2.1 and A.1.40.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}

/-- Odd degree prevents the Sylow group from enlarging the original FSU seed. -/
theorem fundamental_module_eq_seed_of_odd
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hodd : Odd n) : D.moduleSubgroup = D.seed := by
  have hOrbit : Chapter3.Section02.localOrbit T L = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTL)
      (le_componentOrbit _ _)
  have hJoin : Chapter3.Section02.localJoin T L = L ⊔ (T : Subgroup G) := by
    rw [Chapter3.Section02.localJoin, hOrbit]
  have hLS : L ≤ normalizer (D.seed : Set G) := by
    simpa only [hOrbit] using D.orbit_normalizes_seed
  have hCS : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (D.seed : Set G) := by
    rw [← hJoin]
    exact ReducedNormal.subspaceImage_core_centralizes _ _
  have hTS : (T : Subgroup G) ≤ normalizer (D.seed : Set G) := by
    rw [sylow_factor_of_odd hTL hpsl hodd]
    exact sup_le (inf_le_right.trans hLS) (hCS.trans (Subgroup.centralizer_le_normalizer _))
  exact le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTS)
    (le_componentOrbit _ _)

/-- The source central-involution bound removes all fixed vectors of the FSU module. -/
theorem fundamental_fixed_eq_bot
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (L : Set G) = ⊥) :
    D.moduleSubgroup ⊓ centralizer (L : Set G) = ⊥ := by
  have hCT := Stellmacher.inf_centralizer_eq_bot_of_omega_center
    (T : Subgroup G) L T.isPGroup' hTL hZ
  exact bot_unique ((inf_le_inf_right _ D.module_le_sylow).trans hCT.le)

/-- The actual subgroup module is irreducible in odd degree, before identifying its model. -/
theorem fundamental_invariant_subgroup_of_odd
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hodd : Odd n)
    (hZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (L : Set G) = ⊥)
    (E : Subgroup G) (hE : E ≤ D.moduleSubgroup)
    (hn : L ≤ normalizer (E : Set G)) : E = ⊥ ∨ E = D.moduleSubgroup := by
  have he := fundamental_module_eq_seed_of_odd D hTL hpsl hodd
  have hOrbit : Chapter3.Section02.localOrbit T L = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTL)
      (le_componentOrbit _ _)
  rw [he] at hE ⊢
  apply ReducedNormal.invariant_subgroup_of_irrPlus (Chapter3.Section02.localJoin T L)
    (Chapter3.Section02.localOrbit T L) le_sup_left D.homogeneous.isIrrPlus
  · change D.seed ⊓ centralizer (Chapter3.Section02.localOrbit T L : Set G) = ⊥
    rw [hOrbit, ← he]
    exact fundamental_fixed_eq_bot D hTL hZ
  · exact hE
  · rwa [hOrbit]

/-- The module TI alternative under N_G(L) requires no natural-module premise. -/
theorem fundamental_module_ti_of_odd
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hodd : Odd n)
    (hZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (L : Set G) = ⊥)
    {g : G} (hg : g ∈ normalizer (L : Set G)) :
    D.moduleSubgroup ⊓ D.moduleSubgroup.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      D.moduleSubgroup.map (MulAut.conj g).toMonoidHom = D.moduleSubgroup := by
  have hOrbit : Chapter3.Section02.localOrbit T L = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTL)
      (le_componentOrbit _ _)
  have hnL : L ≤ normalizer (D.moduleSubgroup : Set G) := by
    simpa only [hOrbit] using D.orbit_normalizes_module
  have hgL : L.map (MulAut.conj g).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp hg
  have hng : L ≤ normalizer (D.moduleSubgroup.map (MulAut.conj g).toMonoidHom : Set G) := by
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hnL
    rwa [hgL, map_equiv_normalizer_eq] at hm
  rcases fundamental_invariant_subgroup_of_odd D hTL hpsl hodd hZ _ inf_le_left
      ((le_inf hnL hng).trans inf_normalizer_le_normalizer_inf) with he | he
  · exact Or.inl he
  · exact Or.inr (eq_of_le_of_card_ge (he.symm.le.trans inf_le_right)
      (by rw [card_map_of_injective (MulAut.conj g).injective])).symm

/-- A marking on the seed's fixed quotient gives the whole natural FSU module. -/
theorem fundamental_natural_of_seed_fixed_quotient
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hodd : Odd n)
    (hZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (L : Set G) = ⊥)
    (hq : IsNaturalFixedQuotient L D.seed n) : IsNaturalModule L D.moduleSubgroup n := by
  have he := fundamental_module_eq_seed_of_odd D hTL hpsl hodd
  rw [← he] at hq
  exact hq.natural_of_fixed_eq_bot (fundamental_fixed_eq_bot D hTL hZ)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity

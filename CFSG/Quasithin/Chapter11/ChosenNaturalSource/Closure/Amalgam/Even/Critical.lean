module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Geometry

/-!
# Reversing an even critical pair into the original R₁

Normalize the first edge of an F.7 critical geodesic using local transitivity.
Viewed from its even endpoint, the second base vertex is strictly closer than
the critical distance. The F.7 edge-core containment in this reverse direction
puts the endpoint module in the two-core of the base overlap. F.7.11(2) supplies
its nonzero commutator with V and containment in their intersection.

All groups are then mapped from ⟨LT,KT⟩ back to G. The proved overlap identity
identifies the resulting core with the literal R₁ = O₂(L₁T). In particular the
conjugate is not merely placed in LT or in a replacement quotient. Both nested
commutators vanish because the two conjugates are elementary abelian.

The SL₃/Sp₄ quadratic alternatives and field-line alignment remain separate
mathematical obligations; no parity conclusion is asserted here.
Source: Aschbacher--Smith, 11.5.8, printed p.784, using F.7.9 and F.7.11,
printed pp.313--314. Conjugation is x ↦ g*x*g⁻¹ throughout.
-/

public noncomputable section

open Subgroup
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (exists_smul_base stabilizer_base incident_base)
open CFSG.Quasithin.ChapterF.Section07
open Track CriticalPairs

private theorem even_pair_core {A : Type*} [Group A] (F : Bool → Subgroup A)
    (S : SourceSetup F) (hne : S.V ≠ ⊥) (he : Even (S.track hne)) :
    ∃ g : A, S.seed.map (MulAut.conj g).toMonoidHom ≤ (F false ⊓ F true).pCoreIn 2 ∧
      ⁅S.seed, S.seed.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅S.seed, S.seed.map (MulAut.conj g).toMonoidHom⁆ ≤
        S.seed ⊓ S.seed.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨v, hd, hc⟩ := (S.critical_witness hne).1
  have hv := even_endpoint_type F S hne hd he
  have hvne : v ≠ base F false := by
    intro hh
    rw [hh, SimpleGraph.dist_self] at hd
    have := (S.track_spec hne).1
    omega
  obtain ⟨w, hw, hwd⟩ := exists_predecessor F S.generates v (base F false) hvne
  have hedge : (graph F).Adj (base F false) (base F true) :=
    ⟨Bool.false_ne_true, incident_base F false true⟩
  obtain ⟨t, ht, htw⟩ := locally_transitive F hedge hw
  have htfix : t • base F false = base F false := ht
  have htinv : t⁻¹ • base F false = base F false := by
    calc
      t⁻¹ • base F false = t⁻¹ • (t • base F false) := congrArg (t⁻¹ • ·) htfix.symm
      _ = base F false := inv_smul_smul _ _
  have hnorm : S.seed.map (MulAut.conj t).toMonoidHom = S.seed :=
    mem_normalizer_iff_map_conj_eq.mp (S.seed_normalized (by
      simpa only [stabilizer_base] using ht))
  have hd' : (graph F).dist (base F false) (t⁻¹ • v) = S.track hne := by
    rw [← htinv, dist_smul F t⁻¹]
    exact hd
  have hc' : ¬ S.seed ≤ ballKernel F (t⁻¹ • v) 1 := by
    intro hh
    have hm := map_mono (f := (MulAut.conj t).toMonoidHom) hh
    rw [hnorm, ← ballKernel_translate, smul_inv_smul] at hm
    exact hc hm
  have hdist : (graph F).dist (t⁻¹ • v) (base F true) < S.track hne := by
    have hh : (graph F).dist (t⁻¹ • v) (base F true) = (graph F).dist v w := by
      rw [← inv_smul_smul t (base F true), htw, dist_smul F t⁻¹]
    rw [hh]
    rw [SimpleGraph.dist_comm (u := v) (v := base F false), hd] at hwd
    omega
  have hcore := firstModule_le_edge_core F S hne
    (show (t⁻¹ • v).type = false from hv) hdist hedge.symm
  rw [show stabilizer F (base F true) = F true from stabilizer_base F true,
    show stabilizer F (base F false) = F false from stabilizer_base F false,
    inf_comm] at hcore
  have hp := SourceAction.even_critical_pair S hne hd' he hc'
  obtain ⟨g, hg⟩ := exists_smul_base F (t⁻¹ • v)
  have hvt : (t⁻¹ • v).type = false := hv
  rw [hvt] at hg
  rw [vertexModule_first F S.seed hvt, ← hg,
    firstModule_translate_base F S.seed S.seed_normalized] at hp
  rw [← hg, firstModule_translate_base F S.seed S.seed_normalized] at hcore
  exact ⟨g, hcore, hp.1, hp.2.1⟩

open Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- An even critical distance yields the actual noncommuting conjugate inside R₁. -/
theorem exists_critical_conjugate_in_R₁ (h : LocalInputs E) (hout : ¬ E.K ≤ E.M)
    (he : Even (distance E h hout)) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ E.R₁ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤
        V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  let S := sourceSetup E h hout
  obtain ⟨g, hg, hn, hc⟩ := even_pair_core (family E) S (sourceV_ne_bot E h hout) he
  have hseed : S.seed.map (generated E).subtype = V := sourceSeed_map E h hout
  have hconj : (S.seed.map (MulAut.conj g).toMonoidHom).map (generated E).subtype =
      V.map (MulAut.conj (g : G)).toMonoidHom := by
    calc
      _ = (S.seed.map (generated E).subtype).map
          (MulAut.conj (g : G)).toMonoidHom := by rw [map_map, map_map]; rfl
      _ = _ := congrArg (map (MulAut.conj (g : G)).toMonoidHom) hseed
  have hedge : (family E false ⊓ family E true).map (generated E).subtype =
      E.L₁ ⊔ (T : Subgroup G) := by
    rw [map_inf _ _ _ (generated E).subtype_injective]
    rw [show (family E false).map (generated E).subtype = LT E from
      map_subgroupOf_eq_of_le le_sup_left]
    rw [show (family E true).map (generated E).subtype = KT E from
      map_subgroupOf_eq_of_le le_sup_right]
    exact overlap E h
  refine ⟨g, ?_, ?_, ?_⟩
  · have hm := map_mono (f := (generated E).subtype) hg
    rw [hconj, ← AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (generated E).subtype_injective, hedge] at hm
    exact hm
  · intro hz
    apply hn
    apply (map_eq_bot_iff_of_injective _ (generated E).subtype_injective).mp
    rw [map_commutator, hseed, hconj, hz]
  · have hm := map_mono (f := (generated E).subtype) hc
    rw [map_commutator, map_inf _ _ _ (generated E).subtype_injective,
      hseed, hconj] at hm
    exact hm

/-- The nontrivial pair acts quadratically in both orientations. -/
theorem exists_mutually_quadratic_conjugate (h : LocalInputs E) (hout : ¬ E.K ≤ E.M)
    (he : Even (distance E h hout)) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ E.R₁ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤
        V ⊓ V.map (MulAut.conj g).toMonoidHom ∧
      ⁅⁅V, V.map (MulAut.conj g).toMonoidHom⁆, V⁆ = ⊥ ∧
      ⁅⁅V, V.map (MulAut.conj g).toMonoidHom⁆,
        V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  obtain ⟨g, hg, hn, hc⟩ := exists_critical_conjugate_in_R₁ E h hout he
  let := D.elementary
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  refine ⟨g, hg, hn, hc, ?_, ?_⟩
  · exact eq_bot_iff.mpr ((commutator_mono (hc.trans inf_le_left) le_rfl).trans
      (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative V)).le)
  · exact eq_bot_iff.mpr ((commutator_mono (hc.trans inf_le_right) le_rfl).trans
      (commutator_self_eq_bot_iff.mpr
        (inferInstance : IsMulCommutative (V.map (MulAut.conj g).toMonoidHom))).le)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even

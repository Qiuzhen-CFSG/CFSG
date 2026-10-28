module
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroupResidual
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.ResidualNormalization

/-!
# The actual SQTK residual product in the rank-five argument

The escaping minimal parabolic properly contains the original point Sylow.
Its two-residual R therefore has nontrivial two-core, by characteristic-two
inheritance from I C_T(v). Since N_G(R) normalizes that core, it lies in a
genuine two-local subgroup and inherits the full SQTK condition. The already
proved normalization by P_f and P_f^t bounds the cubic rank of their join
with R by two, using the literal ambient subgroups.

This supplies the upper bound in Aschbacher--Smith 10.2.9, printed p.753.
The elementary-nine construction and lower bound remain with the final owner
qt-d-10-nona5-point-constrained; this module does not assert the terminal
contradiction or the earlier construction of LinearFiveData.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The actual residual of each proper point-Sylow overgroup has nontrivial
two-core. This uses the original characteristic-two point join. -/
theorem Context.node_residual_core_ne_bot (c : Context D t v I) (P : Subgroup G)
    (hSP : pointSylow T v < P) (hPH : P ≤ pointJoin T v I) :
    pCore 2 ((pResidual 2 P).map P.subtype) ≠ ⊥ := by
  let H := pointJoin T v I
  obtain ⟨S,hS⟩ := c.join_sylow
  have hlt : (S : Subgroup H) < P.subgroupOf H := by
    apply lt_of_le_of_ne
    · intro x hx
      exact hSP.le (hS ▸ mem_map_of_mem H.subtype hx)
    · intro he
      have hh := congrArg (Subgroup.map H.subtype) he
      rw [hS,map_subgroupOf_eq_of_le hPH] at hh
      exact hSP.ne hh
  let R := (pResidual 2 (P.subgroupOf H)).map (P.subgroupOf H).subtype
  have hr : pCore 2 R ≠ ⊥ :=
    pCore_embedded_pResidual_ne_bot_of_sylow_lt c.characteristic_two S _ hlt
  have he : R.map H.subtype = (pResidual 2 P).map P.subtype := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hPH]
  let e : R ≃* (pResidual 2 P).map P.subtype :=
    (R.equivMapOfInjective H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr he)
  intro hz
  apply hr
  apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
  rw [pCore_map_iso 2 e,hz]

/-- The residual normalizer lies in the normalizer of a nontrivial two-core,
so it inherits the source SQTK condition with the full known-simple class. -/
theorem Context.node_residual_normalizer_sqtk (c : Context D t v I) (P : Subgroup G)
    (hSP : pointSylow T v < P) (hPH : P ≤ pointJoin T v I) :
    IsSQTK KnownSimple.IsKnownSimple (normalizer ((pResidual 2 P).map P.subtype : Set G)) := by
  let R := (pResidual 2 P).map P.subtype
  let Q := R.pCoreIn 2
  have hQ : Q ≠ ⊥ := fun he => c.node_residual_core_ne_bot P hSP hPH
    ((map_eq_bot_iff_of_injective _ R.subtype_injective).mp he)
  have hlocal : IsTwoLocal (normalizer (Q : Set G)) :=
    ⟨Q,hQ,isPGroup_pCoreIn 2 R,rfl⟩
  have hN : normalizer (R : Set G) ≤ normalizer (Q : Set G) :=
    normalizer_le_normalizer_characteristic_image R (pCore 2 R)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hN)).mp
    ((D.simpleQTKE.twoLocal_sqtk hlocal).subgroup _)

/-- Every literal product with an actor normalizing O²(P) has cubic rank at
most two. The local hypothesis is derived, not postulated for the product. -/
theorem Context.node_residual_join_three_rank (c : Context D t v I)
    (P A : Subgroup G) (hSP : pointSylow T v < P) (hPH : P ≤ pointJoin T v I)
    (hA : A ≤ normalizer ((pResidual 2 P).map P.subtype : Set G)) :
    primeRank 3 ((pResidual 2 P).map P.subtype ⊔ A : Subgroup G) ≤ 2 := by
  let R := (pResidual 2 P).map P.subtype
  have hn : R ⊔ A ≤ normalizer (R : Set G) := sup_le R.le_normalizer hA
  exact (primeRank_mono 3 hn).trans
    ((c.node_residual_normalizer_sqtk P hSP hPH).stronglyQuasithin 3 (by decide) (by decide))

/-- The source rank-five parabolics satisfy the actual two-local cubic-rank
bound on the residual product, including both moving nodes. -/
theorem LinearFiveData.exists_rankFive_residual_configuration {c : Context D t v I}
    (m : LinearFiveData c) :
    ∃ P F : Subgroup G,
      pointSylow T v ⋖ P ∧ P ≤ planeCentralizer T t v I ∧
      ¬ P ≤ D.maximalLocal ∧ t ∈ normalizer (P : Set G) ∧
      pointSylow T v ⋖ F ∧ F ≤ L ⊔ pointSylow T v ∧
      ¬ F ≤ planeCentralizer T t v I ∧
      Nonempty (((P ⊔ F : Subgroup G) ⧸ pCore 2 (P ⊔ F : Subgroup G)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      F ⊔ F.map (MulAut.conj t).toMonoidHom ≤
        normalizer ((pResidual 2 P).map P.subtype : Set G) ∧
      IsSQTK KnownSimple.IsKnownSimple (normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
      primeRank 3 ((pResidual 2 P).map P.subtype ⊔
        (F ⊔ F.map (MulAut.conj t).toMonoidHom) : Subgroup G) ≤ 2 := by
  obtain ⟨P,F,hP,hPC,hPM,htP,hF,hFK,hFC,he,hn⟩ := m.exists_residual_normalizing_pair
  have hPH : P ≤ pointJoin T v I := hPC.trans inf_le_left
  exact ⟨P,F,hP,hPC,hPM,htP,hF,hFK,hFC,he,hn,
    c.node_residual_normalizer_sqtk P hP.lt hPH,
    c.node_residual_join_three_rank P _ hP.lt hPH hn⟩
end CFSG.Quasithin.Chapter10.PointControl.Constrained

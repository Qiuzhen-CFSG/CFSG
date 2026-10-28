module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.Setup
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Orbit
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The actual residual orbit in the local E-member branch

An element of ambient tau which fixes J centralizes the local actor modulo the
local two-core. The E-member tau clause therefore makes it normalize P and its
two-residual. Distinct conjugates of that residual lie in distinct centerless
chief components; the component-orbit product theorem identifies their join
with a positive direct power.

The orbit is two-perfect and equals the embedded two-residual of its join with
tau. In the component branch it is perfect. Finally, elementary abelian linear
algebra constructs the complement to `N_A(J)` needed for the diagonal maps.
The diagonal membership, quotient generation and local Sylow assertions remain
separate obligations; none is inferred from the abstract direct-power equivalence.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed p.213.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Ambient tau elements fixing J belong to the actual local tau. Triviality of
the ambient two-core is used before passing to the possibly larger local core. -/
theorem ambientTau_stabilizer_le_localTau (T : Sylow 2 G) (J A : Subgroup G)
    (hcore : pCore 2 G = ⊥) :
    (tau (T : Subgroup G) A ⊓ normalizer (J : Set G)).subgroupOf (localGroup T J) ≤
      tau ((stabilizer T J).subgroupOf (localGroup T J))
        (A.subgroupOf (localGroup T J)) := by
  intro x hx
  obtain ⟨hxT, hc⟩ := mem_centralizerModulo_iff.mp hx.1
  apply mem_centralizerModulo_iff.mpr
  refine ⟨⟨hxT, hx.2⟩, ?_⟩
  intro a ha
  have he : ⁅a, x⁆ = 1 := by
    apply Subtype.ext
    exact mem_bot.mp (hcore ▸ hc (a : G) ha)
  rw [he]
  exact one_mem _

omit [Finite G] in
/-- A local subgroup normalizes its two-residual through the literal inclusions. -/
theorem local_member_le_residual_normalizer (T : Sylow 2 G) (J : Subgroup G)
    (P : Subgroup (localGroup T J)) :
    P.map (localGroup T J).subtype ≤ normalizer (localMemberResidual T J P : Set G) := by
  let f := (localGroup T J).subtype.comp P.subtype
  have hn : f.range ≤ normalizer (((pResidual 2 P).map f) : Set G) := by
    rw [MonoidHom.range_eq_map]
    exact (map_mono (show (⊤ : Subgroup P) ≤ normalizer (pResidual 2 P : Set P) by
      rw [normalizer_eq_top])).trans (le_normalizer_map f)
  simpa only [f, MonoidHom.range_comp, range_subtype, localMemberResidual, map_map] using hn

/-- The local E-member tau clause supplies invariance under the ambient stabilizer. -/
theorem memberResidual_stabilizer_invariant {n : ℕ} (T : Sylow 2 G) (J A : Subgroup G)
    (hcore : pCore 2 G = ⊥) {P : Subgroup (localGroup T J)}
    (hP : IsEMemberAt n ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P) :
    tau (T : Subgroup G) A ⊓ normalizer (J : Set G) ≤
      normalizer (localMemberResidual T J P : Set G) := by
  intro x hx
  have hxS : x ∈ stabilizer T J := ⟨tau_le _ _ hx.1, hx.2⟩
  let xH : localGroup T J := ⟨x, (show stabilizer T J ≤ localGroup T J from le_sup_right) hxS⟩
  have hxτ := ambientTau_stabilizer_le_localTau T J A hcore
    (show xH ∈ (tau (T : Subgroup G) A ⊓ normalizer (J : Set G)).subgroupOf
      (localGroup T J) from hx)
  have hxP : xH ∈ P := (hP.1.2.2.2.1 hxτ).2
  exact local_member_le_residual_normalizer T J P (mem_map_of_mem _ hxP)

/-- The actual tau orbit of the residual is a positive direct power. The factors
are distinct subgroups in distinct centerless chief components. -/
theorem memberResidualOrbit_equiv_power {n : ℕ} (T : Sylow 2 G) {J A : Subgroup G}
    (hcore : pCore 2 G = ⊥)
    (hX : ChiefFactor.IsChief (pResidual 2 G) ⊥)
    (hna : ¬ IsMulCommutative (pResidual 2 G)) (hJ : IsComponentIn J (pResidual 2 G))
    {P : Subgroup (localGroup T J)}
    (hP : IsEMemberAt n ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P) :
    ∃ r : ℕ, 0 < r ∧ Nonempty ((Fin r → localMemberResidual T J P) ≃*
      memberResidualOrbit T J A P) := by
  have hJG : IsComponent G J :=
    ⟨hJ.2.1.trans hJ.1 hX.normal_upper.isSubnormal, hJ.quasisimple⟩
  exact componentOrbit_localFactor_equiv_power hJG
    (hX.component_center_eq_bot hna hJ) (localMemberResidual_le_component T J P)
    (memberResidual_stabilizer_invariant T J A hcore hP)


/-- Embedding the local two-residual preserves two-perfectness. -/
theorem localMemberResidual_isPPerfect (T : Sylow 2 G) (J : Subgroup G)
    (P : Subgroup (localGroup T J)) : IsPPerfect 2 (localMemberResidual T J P) := by
  let e := ((pResidual 2 P).map P.subtype).equivMapOfInjective
    (localGroup T J).subtype (localGroup T J).subtype_injective
  exact (isPPerfect_embedded_pResidual 2 P).of_surjective e.toMonoidHom e.surjective

/-- The tau conjugates generate a two-perfect subgroup. -/
theorem memberResidualOrbit_isPPerfect (T : Sylow 2 G) (J A : Subgroup G)
    (P : Subgroup (localGroup T J)) : IsPPerfect 2 (memberResidualOrbit T J A P) := by
  let E := localMemberResidual T J P
  let N := memberResidualOrbit T J A P
  have hE := localMemberResidual_isPPerfect T J P
  apply (pResidual_eq_top_iff 2 N).mp
  apply map_injective N.subtype_injective
  rw [← MonoidHom.range_eq_map, range_subtype]
  apply le_antisymm (map_subtype_le _)
  apply iSup_le
  intro a
  let B := E.map (MulAut.conj (a : G)).toMonoidHom
  have hBN : B ≤ N := le_iSup (fun a : tau (T : Subgroup G) A =>
    E.map (MulAut.conj (a : G)).toMonoidHom) a
  let e := (MulAut.conj (a : G)).subgroupMap E
  have hB := hE.of_surjective e.toMonoidHom e.surjective
  let eN := (subgroupOfEquivOfLe hBN).symm
  have hB' := hB.of_surjective eN.toMonoidHom eN.surjective
  simpa only [map_subgroupOf_eq_of_le hBN] using
    map_mono (f := N.subtype) (le_pResidual_of_isPPerfect (B.subgroupOf N) hB')

/-- The source orbit group has precisely the orbit as its embedded two-residual. -/
theorem memberOrbitGroup_residual (T : Sylow 2 G) (J A : Subgroup G)
    (P : Subgroup (localGroup T J)) :
    (pResidual 2 (memberOrbitGroup T J A P)).map (memberOrbitGroup T J A P).subtype =
      memberResidualOrbit T J A P :=
  embedded_pResidual_join_pGroup _ _ (memberResidualOrbit_isPPerfect T J A P)
    (T.isPGroup'.to_le (tau_le _ _)) (le_normalizer_componentOrbit _ _)


/-- In the component branch the actual orbit is perfect, as asserted on p.213. -/
theorem memberResidualOrbit_isPerfect_of_componentCase (T : Sylow 2 G) (J A : Subgroup G)
    {P : Subgroup (localGroup T J)}
    (hP : ECaseComponent ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P) : Group.IsPerfect (memberResidualOrbit T J A P) := by
  let _ : Group.IsPerfect (pResidual 2 P) := by
    rw [hP.2.2.1]
    infer_instance
  let _ : Group.IsPerfect ((pResidual 2 P).map P.subtype) := Group.IsPerfect.map _
  let _ : Group.IsPerfect (localMemberResidual T J P) := Group.IsPerfect.map _
  exact isPerfect_iSup_conjugates _ _

omit [Finite G] in
/-- Construct the source complement to the actual stabilizer in the elementary actor. -/
theorem exists_local_actor_complement (J A : Subgroup G) [IsElementaryAbelian 2 A] :
    ∃ Z : Subgroup G, Z ≤ A ∧ Disjoint (A ⊓ normalizer (J : Set G)) Z ∧
      (A ⊓ normalizer (J : Set G)) ⊔ Z = A := by
  let V := (normalizer (J : Set G)).subgroupOf A
  obtain ⟨D, hD⟩ := IsElementaryAbelian.exists_isCompl 2 A V
  refine ⟨D.map A.subtype, map_subtype_le _, ?_, ?_⟩
  · apply disjoint_iff.mpr
    have h := congrArg (Subgroup.map A.subtype) hD.inf_eq_bot
    rw [Subgroup.map_inf _ _ _ A.subtype_injective, Subgroup.map_bot] at h
    simpa only [V, subgroupOf_map_subtype, inf_comm] using h
  · have h := congrArg (Subgroup.map A.subtype) hD.sup_eq_top
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_comm, ← MonoidHom.range_eq_map,
      range_subtype] at h
    exact h

end CFSG.Quasithin.ChapterE.ChiefOrbit

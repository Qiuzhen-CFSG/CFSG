module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionThree.LemmaThreeFour
public import Theory.GroupTheory.PGroup.NormalQuotientInvolutionActor
/-!
# An actual involution for the terminal residual action

At critical distance one, there is an involution x in the initial vertex
center outside the terminal two-core Q such that K=Q⟨x⟩ is normal in the
edge Sylow subgroup T and [O²(G_terminal),K]=O²(G_terminal).
Only the ambient Section Nine context is used.

The initial center is elementary abelian, normal in T, and not contained
in Q by criticality. Its nontrivial normal image in T/Q meets the center;
lifting a nontrivial element gives x and normality of K. Apply (3.4) to
this normal subgroup K of T in the terminal stabilizer. The core alternative
is excluded because x lies outside Q.

For the later action on V₁/Z_terminal, Q acts trivially, so this theorem
makes the residual image a full commutator with the single image of x.
The assertion here retains Q in K; it does not require the cyclic subgroup
of x to be normal in T. This supplies the actual actor for the invocation
of (1.3) in Stellmacher (9.1), Journal of Algebra 190 (1997), p.47.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u
public theorem distance_one_involution_residual_actor
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) :
    ∃ x ∈ z ctx.Γ ctx.criticalPath.a,
      _root_.IsInvolution x ∧ x ∉ q ctx.Γ ctx.criticalPath.a' ∧
      (q ctx.Γ ctx.criticalPath.a' ⊔ Subgroup.zpowers x ≤ T) ∧
      ((q ctx.Γ ctx.criticalPath.a' ⊔ Subgroup.zpowers x).subgroupOf T).Normal ∧
      ⁅twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a'),
        q ctx.Γ ctx.criticalPath.a' ⊔ Subgroup.zpowers x⁆ =
        twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a') := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Z := z Γ cp.a
  let Q := q Γ cp.a'
  let P := stabilizer Γ cp.a'
  have hlen : cp.length = 1 := hb
  have hstep : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hb.symm
      _ = cp.a' := cp.path_end
  have hneighbor : cp.a' ∈ neighborhood Γ cp.a := by
    rw [neighborhood, Γ.neighbors_def]
    exact (Γ.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
  have hZT : Z ≤ T :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.a' hneighbor).trans
      ((Subgroup.map_subtype_le _).trans
        (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1)
  have hQT : Q ≤ T := by
    change q Γ cp.a' ≤ T
    rw [← hstep]
    exact (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2
  have hTG := (edge_sylow_data ctx.sectionSeven Γ cp).1.1
  have hTP : T ≤ P := by
    change T ≤ stabilizer Γ cp.a'
    rw [← hstep]
    exact (edge_sylow_data ctx.sectionSeven Γ cp).2.1
  have hZn : (Z.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZT).mpr
      (hTG.trans (stabilizer_le_normalizer_z Γ cp.a))
  have hQn : (Q.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).mpr
      (hTP.trans (stabilizer_le_normalizer_q Γ cp.a'))
  let _ : IsElementaryAbelian 2 Z := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hneighbor
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot : ¬ Z.subgroupOf T ≤ Q.subgroupOf T := by
    intro hh
    apply cp.critical.2
    intro z hz
    exact hh (show (⟨z, hZT hz⟩ : T) ∈ Z.subgroupOf T from hz)
  let _ := hZn
  let _ := hQn
  let _ : IsElementaryAbelian 2 (Z.subgroupOf T) := IsElementaryAbelian.subgroupOf hZT
  have hTtwo : IsPGroup 2 T :=
    (sectionThreeHypotheses ctx.sectionSeven).nontrivial_two_subgroup.2
  obtain ⟨x, hx, hxi, hxnot, hxN⟩ :=
    Subgroup.exists_involution_normal_sup_of_elementary_not_le hTtwo
      (Z.subgroupOf T) (Q.subgroupOf T) hnot
  let K := Q ⊔ Subgroup.zpowers (x : G)
  have hKT : K ≤ T := sup_le hQT (Subgroup.zpowers_le.mpr x.property)
  have hmap : (Q.subgroupOf T ⊔ Subgroup.zpowers x).map T.subtype = K := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hQT, MonoidHom.map_zpowers]
    rfl
  have hKn : (K.subgroupOf T).Normal := by
    have heq : K.subgroupOf T = Q.subgroupOf T ⊔ Subgroup.zpowers x := by
      apply Subgroup.map_injective T.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hKT, hmap]
    rw [heq]
    exact hxN
  have hlocal : P ∈ PFamily (⊤ : Subgroup G) T ∧ Group.IsSolvable P := by
    have heq := congrArg (fun b => stabilizer Γ b ∈ PFamily (⊤ : Subgroup G) T ∧
      Group.IsSolvable (stabilizer Γ b)) hstep
    exact heq.mp (edge_local_data ctx.sectionSeven Γ cp).2
  have hQeq : Q = twoCoreAmbient P := by
    change q Γ cp.a' = twoCoreAmbient (stabilizer Γ cp.a')
    rw [q, Γ.twoCoreAt_def]
    rfl
  have hc := SectionThree.lemma_three_four T (sectionThreeHypotheses ctx.sectionSeven) P
    ((pFamily_iff_pSet ⊤ T P).mp hlocal.1) K ⟨hKT,hKn⟩ hlocal.2
  have hres : ⁅twoResidualIn P, K⁆ = twoResidualIn P := hc.resolve_left (by
    intro hKQ
    exact hxnot ((hQeq ▸ hKQ) ((show Subgroup.zpowers (x : G) ≤ K from le_sup_right) (Subgroup.mem_zpowers (x : G)))))
  refine ⟨x, hx, ?_, hxnot, hKT, hKn, hres⟩
  exact ⟨fun heq => hxi.1 (Subtype.ext heq), congrArg Subtype.val hxi.2⟩
end Stellmacher.SectionNine

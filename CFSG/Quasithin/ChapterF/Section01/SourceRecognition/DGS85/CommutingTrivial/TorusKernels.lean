module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.PathCartan

/-!
# Separation and intrinsic kernels of the two Cartan factors

A nonidentity odd matrix in characteristic-two SL2 fixes no nonzero natural
vector. The beta factor centralizes its nontrivial center inside the alpha
natural module, so the two local factors of an odd Cartan intersect trivially.

For a nonbinary marked local quotient, simplicity makes the image of the
full permutation kernel either trivial or the whole quotient. The latter
would place the transitive local actor inside the two-closed edge, which is
impossible. Thus L_delta meets G_delta^(1) exactly in Q_delta, and each odd
local factor has trivial intersection with its own permutation kernel.
Relative normality and the distinction between Q_delta and G_delta^(1)
are retained throughout. The actual source application is `DistanceThreeCartan`.

Source: DGS, *Groups and Graphs* (1985), 9.9 and the even-field part of
9.10(2), printed pp.147--148.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Naturality of the alpha center separates the two odd local factors.
The beta factor fixes its nontrivial center; no nonidentity odd alpha
actor can fix a nonzero vector of the alpha natural module. -/
theorem odd_local_tori_disjoint
    (h : LocallyRankOneTriple P B) {a beta : Vertex (family P)}
    (hZba : Z (family P) beta ≤ Z (family P) a)
    (hZb : Z (family P) beta ≠ ⊥)
    (hω : Z (family P) beta = omegaCenterIn (graphLocalGroup (family P) beta))
    {F : Type*} [Field F] [CharP F 2]
    (ea : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,F)) :
    letI := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) a
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let H := graphLocalGroup (family P) a
    let q := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    ∀ ρ : Representation (ZMod 2) SL(2,F) (Additive (Z (family P) a)),
      (∀ (l : H) (z : Additive (Z (family P) a)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      ∀ E : Additive (Z (family P) a) ≃ₗ[ZMod 2] (Fin 2 → F),
      (∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) →
      ∀ C : Subgroup G, Odd (Nat.card C) →
        Disjoint (C ⊓ H) (C ⊓ graphLocalGroup (family P) beta) := by
  let := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) a
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let Γ := family P
  let H := graphLocalGroup Γ a
  let q := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  dsimp only
  intro ρ hact E hE C ho
  obtain ⟨y,hy,hyne⟩ := (Z Γ beta).bot_or_exists_ne_one.resolve_left hZb
  let z : Additive (Z Γ a) := Additive.ofMul ⟨y,hZba hy⟩
  have hz : E z ≠ 0 := by
    intro he
    have hh : z = 0 := E.injective (he.trans E.map_zero.symm)
    exact hyne (congrArg (fun w : Additive (Z Γ a) => (w.toMul : G)) hh)
  apply disjoint_def.mpr
  intro t htA htB
  let l : H := ⟨t,htA.2⟩
  have hodd : Odd (orderOf l) := by
    rw [Subgroup.orderOf_mk]
    simpa only [Subgroup.orderOf_mk] using
      ho.of_dvd_nat (_root_.orderOf_dvd_natCard (⟨t,htA.1⟩ : C))
  have hfix : ρ (q l) z = z := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hact]
    exact mul_inv_eq_iff_eq_mul.mpr
      (((mem_omegaCenterIn_iff _ _).mp (hω ▸ hy)).2.1 t htB.2)
  have hq : q l = 1 := by
    by_contra hn
    apply hz
    apply Matrix.SL2.odd_power_fixed_eq_zero (q l) (orderOf l) hodd
      (by rw [←map_pow,pow_orderOf_eq_one,map_one]) hn
    rw [←hE,hfix]
  have hl : l ∈ pCore 2 H := (QuotientGroup.eq_one_iff l).mp
    (ea.injective (hq.trans ea.map_one.symm))
  have hc := (pCore_isPGroup (p := 2) (G := H)).orderOf_coprime
    hodd.coprime_two_left (⟨l,hl⟩ : pCore 2 H)
  have hc' : Nat.Coprime (orderOf t) (orderOf t) := by
    simpa only [l,Subgroup.orderOf_mk] using hc
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc' dvd_rfl dvd_rfl)


/-- In the nonbinary branch the intrinsic actor meets its full local
permutation kernel in exactly its two-core. -/
theorem nonbinary_local_kernel_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (hF : 4 ≤ Nat.card F) :
    graphLocalGroup (family P) v ⊓ ballKernel (family P) v 1 = Q (family P) v := by
  let Γ := family P
  let := finite_endpoints h
  let H := graphLocalGroup Γ v
  let N := (ballKernel Γ v 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    ((sylowGenerated_le _).trans (stabilizer_le_normalizer_ballKernel Γ v 1))
  let : (N.map q).Normal := (inferInstance : N.Normal).map q hq
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  let : IsSimpleGroup SL(2,F) := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).isSimpleGroup
  have hkerN : q.ker ≤ N := by
    rw [hk]
    intro z hz
    exact (source_Z_Q_U h v).2 ((graphLocalGroup_core h v).le (mem_map_of_mem H.subtype hz))
  have hNk : N ≤ q.ker := by
    rcases (inferInstance : (N.map q).Normal).eq_bot_or_eq_top with hi | hi
    · intro z hz
      exact hi.le (mem_map_of_mem q hz)
    · have htop : N = ⊤ := by
        calc N = (N.map q).comap q := (comap_map_eq_self hkerN).symm
             _ = ⊤ := by rw [hi,Subgroup.comap_top]
      let E := stabilizer Γ v ⊓ stabilizer Γ w
      let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer Γ v from inf_le_left)) (inclusion_injective _)
      have hHE : H ≤ E := by
        intro z hz
        exact ballKernel_one_le_edge Γ hvw (show (⟨z,hz⟩ : H) ∈ N from htop.symm ▸ mem_top _)
      exact (graphLocalGroup_not_closed h hB hS v
        (core_sylow_of_le E H hHE (source_edge_core_sylow h hB hvw))).elim
  apply le_antisymm
  · intro z hz
    exact (graphLocalGroup_core h v).le (mem_map_of_mem H.subtype
      (hk ▸ hNk (show (⟨z,hz.1⟩ : H) ∈ N from hz.2)))
  · exact le_inf (core_le_graphLocalGroup h v) (source_Z_Q_U h v).2

/-- Consequently an odd local torus has trivial intersection with its own
full permutation kernel, the even-field kernel exclusion in §9.10(2). -/
theorem nonbinary_odd_torus_disjoint_kernel
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (hF : 4 ≤ Nat.card F) (C : Subgroup G) (ho : Odd (Nat.card C)) :
    Disjoint (C ⊓ graphLocalGroup (family P) v) (ballKernel (family P) v 1) := by
  let := finite_endpoints h
  let : Finite (Q (family P) v) := Finite.of_injective
    (inclusion (Q_le_stabilizer (family P) v)) (inclusion_injective _)
  have hp : IsPGroup 2 (Q (family P) v) := isPGroup_pCoreIn 2 _
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  have hd : Disjoint C (Q (family P) v) := disjoint_of_coprime_natCard (by
    rw [hk]; exact ho.coprime_two_right.pow_right k)
  apply disjoint_def.mpr
  intro z hz hzk
  exact disjoint_def.mp hd hz.1 ((nonbinary_local_kernel_intersection h hB hS hvw e hF).le ⟨hz.2,hzk⟩)


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

module

public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreActionSplitting
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Local cores of an amalgam

All cores are intrinsic p-cores mapped into the stated ambient group. The local
kernel of an edge subgroup D in a vertex H is the image of the normal core of
D ∩ H in H. Restricting a normal p-subgroup proves the core-containment chain.
When D contains a Sylow subgroup of H, its local kernel contains O_p(H), and
intersecting O_p(D) with that kernel recovers O_p(H).

For the faithfulness argument, a common normal subgroup has p-core normal in
the join. If that join has trivial p-core, commutator containment and a
self-centralizing vertex p-core force the common normal subgroup to vanish.
Finally, a reduced normal elementary abelian subgroup has centralizer with
the same embedded p-core. If this core is the Sylow centralizer, the residual
with prime-to-p quotient equals it as well.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), F.7.3(8), F.7.4 and F.7.7, printed pp.311--312
(PDF pp.322--323). The Chapter F consumer supplies the generalized-Fitting
bridge and specializes these statements to the actual intersection of vertices.
-/

@[expose] public section
namespace Theory.GroupTheory.AmalgamLocalCores
open Subgroup
variable {G A : Type*} [Group G] [Group A] {p : ℕ}

/-- Embedded p-cores commute with injective homomorphisms. -/
theorem pCoreIn_map_of_injective (p : ℕ) (f : G →* A) (hf : Function.Injective f)
    (H : Subgroup G) : (H.map f).pCoreIn p = (H.pCoreIn p).map f := by
  have h := pCoreIn_range_of_injective p (f.comp H.subtype)
    (hf.comp H.subtype_injective)
  rw [MonoidHom.range_comp, range_subtype] at h
  simpa only [pCoreIn, map_map] using h

/-- The normal core of the edge subgroup D inside vertex H, mapped back to G. -/
def localKernel (H D : Subgroup G) : Subgroup G :=
  (D.subgroupOf H).normalCore.map H.subtype

/-- The local kernel lies in its vertex group. -/
theorem localKernel_le_left (H D : Subgroup G) : localKernel H D ≤ H :=
  map_subtype_le _

/-- The local kernel lies in the edge subgroup. -/
theorem localKernel_le_right (H D : Subgroup G) : localKernel H D ≤ D := by
  rintro x ⟨y, hy, rfl⟩
  exact (D.subgroupOf H).normalCore_le hy

/-- Normality is relative to the vertex, not to the ambient group. -/
theorem normalizes_localKernel (H D : Subgroup G) :
    H ≤ normalizer (localKernel H D : Set G) := by
  have h := (D.subgroupOf H).normalCore.le_normalizer_map H.subtype
  rwa [normalizer_eq_top_iff.mpr (inferInstance : (D.subgroupOf H).normalCore.Normal),
    ← MonoidHom.range_eq_map, range_subtype] at h

/-- The core-containment chain across an edge, without a Sylow assumption. -/
theorem core_containment_chain (p : ℕ) (B C D : Subgroup G)
    (hDB : D ≤ B) :
    B.pCoreIn p ⊓ localKernel C D ≤ D.pCoreIn p ⊓ localKernel C D ∧
      D.pCoreIn p ⊓ localKernel C D ≤ (localKernel C D).pCoreIn p := by
  constructor
  · apply le_inf _ inf_le_right
    exact (le_inf (inf_le_right.trans (localKernel_le_right C D)) inf_le_left).trans
      (inf_pCoreIn_le_of_le p hDB)
  · rw [inf_comm]
    exact inf_pCoreIn_le_of_le p (localKernel_le_right C D)

/-- The normal core of a Sylow overgroup has the same embedded p-core. -/
theorem core_normalCore_eq (T : Sylow p G) (D : Subgroup G)
    (hTD : (T : Subgroup G) ≤ D) : D.normalCore.pCoreIn p = pCore p G := by
  symm
  exact pCore_eq_map_of_normal_of_le p D.normalCore
    (normal_le_normalCore.mpr ((pCore_isPGroup.le_sylow_of_normal T).trans hTD))

/-- The vertex p-core is the intersection of the edge core with its normal core. -/
theorem core_eq_edge_inf_kernel (T : Sylow p G) (D : Subgroup G)
    (hTD : (T : Subgroup G) ≤ D) :
    pCore p G = D.pCoreIn p ⊓ D.normalCore := by
  apply le_antisymm
  · exact le_inf (pCore_le_map_of_sylow_le T D hTD)
      (normal_le_normalCore.mpr ((pCore_isPGroup.le_sylow_of_normal T).trans hTD))
  · calc
      D.pCoreIn p ⊓ D.normalCore ≤ D.normalCore.pCoreIn p := by
        rw [inf_comm]
        exact inf_pCoreIn_le_of_le p D.normalCore_le
      _ = _ := core_normalCore_eq T D hTD

/-- The local kernel and its vertex have the same p-core in the ambient group. -/
theorem vertex_core_eq_kernel_core (H D : Subgroup G) (T : Sylow p H)
    (hTD : (T : Subgroup H).map H.subtype ≤ D) :
    (localKernel H D).pCoreIn p = H.pCoreIn p := by
  have hT : (T : Subgroup H) ≤ D.subgroupOf H := by
    intro x hx
    exact hTD (mem_map_of_mem H.subtype hx)
  rw [localKernel, pCoreIn_map_of_injective p H.subtype H.subtype_injective,
    core_normalCore_eq T (D.subgroupOf H) hT]
  rfl

/-- Ambient form of the vertex/edge/local-kernel core identity. -/
theorem vertex_core_eq_edge_inf_kernel (H D : Subgroup G) (hDH : D ≤ H)
    (T : Sylow p H) (hTD : (T : Subgroup H).map H.subtype ≤ D) :
    H.pCoreIn p = D.pCoreIn p ⊓ localKernel H D := by
  have hT : (T : Subgroup H) ≤ D.subgroupOf H := by
    intro x hx
    exact hTD (mem_map_of_mem H.subtype hx)
  have hm := congrArg (fun X : Subgroup H => X.map H.subtype)
    (core_eq_edge_inf_kernel T (D.subgroupOf H) hT)
  rw [Subgroup.map_inf _ _ _ H.subtype_injective, ← pCoreIn_map_of_injective p H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le hDH] at hm
  exact hm

/-- In a group with self-centralizing p-core, a normal p-core-free subgroup vanishes. -/
theorem normal_eq_bot_of_core_eq_bot (N : Subgroup G) [N.Normal]
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G)
    (hn : pCore p N = ⊥) : N = ⊥ := by
  have hi : N ⊓ pCore p G = ⊥ := by
    apply eq_bot_iff.mpr
    rintro x ⟨hxN, hxQ⟩
    have h : (pCore p G).subgroupOf N ≤ pCore p N :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
    have hx := h (show (⟨x, hxN⟩ : N) ∈ (pCore p G).subgroupOf N from hxQ)
    rw [hn] at hx
    exact congrArg Subtype.val (mem_bot.mp hx)
  have hcomm : ⁅N, pCore p G⁆ = ⊥ :=
    eq_bot_iff.mpr ((commutator_le_inf N (pCore p G)).trans hi.le)
  have hNQ : N ≤ pCore p G := (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hc
  exact eq_bot_iff.mpr ((le_inf le_rfl hNQ).trans hi.le)

/-- A p-core-free join and a self-centralizing vertex core kill every common normal subgroup. -/
theorem common_normal_eq_bot (H J K : Subgroup G)
    (hKHJ : K ≤ H ⊓ J)
    (hnH : H ≤ normalizer (K : Set G)) (hnJ : J ≤ normalizer (K : Set G))
    (hcore : pCore p (H ⊔ J : Subgroup G) = ⊥)
    (hc : centralizer (pCore p H : Set H) ≤ pCore p H) : K = ⊥ := by
  have hKH : K ≤ H := hKHJ.trans inf_le_left
  have hKN : K ≤ H ⊔ J := hKH.trans le_sup_left
  have hnormal : H ⊔ J ≤ normalizer (K : Set G) := sup_le hnH hnJ
  have hcoreK : K.pCoreIn p ≤ (H ⊔ J).pCoreIn p :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn p K)
      ((pCoreIn_le p K).trans hKN)
      (hnormal.trans (normalizer_le_normalizer_characteristic_image K (pCore p K)))
  have hbot : K.pCoreIn p = ⊥ := by
    apply eq_bot_iff.mpr
    simpa only [pCoreIn, hcore, Subgroup.map_bot] using hcoreK
  let N := K.subgroupOf H
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hnH
  have hNcore : pCore p N = ⊥ := by
    have hmap : (N.pCoreIn p).map H.subtype = K.pCoreIn p := by
      rw [← pCoreIn_map_of_injective p H.subtype H.subtype_injective,
        map_subgroupOf_eq_of_le hKH]
    have hN : N.pCoreIn p = ⊥ :=
      ((N.pCoreIn p).map_eq_bot_iff_of_injective H.subtype_injective).mp (hmap.trans hbot)
    exact ((pCore p N).map_eq_bot_iff_of_injective N.subtype_injective).mp hN
  have hN := normal_eq_bot_of_core_eq_bot N hc hNcore
  have hm := congrArg (fun X : Subgroup H => X.map H.subtype) hN
  simpa only [N, map_subgroupOf_eq_of_le hKH, Subgroup.map_bot] using hm

/-- Reducedness identifies the centralizer core with the ambient core. -/
theorem reduced_centralizer_core (V : Subgroup G)
    (hV : Theory.GroupTheory.IsPReduced p V) :
    (centralizer (V : Set G)).pCoreIn p = pCore p G := by
  let := hV.normal
  exact (pCore_eq_map_of_normal_of_le p _
    (le_centralizer_iff.mp hV.le_centralizer_pCore)).symm

/-- A Sylow centralizer equal to its p-core is the prime-to-p residual. -/
theorem reduced_centralizer_residual [Finite G] [Fact p.Prime]
    (V : Subgroup G) (hV : Theory.GroupTheory.IsPReduced p V) (T : Sylow p G)
    (hCT : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (centralizer (V : Set G)).pCoreIn p) :
    (primeToResidual p (centralizer (V : Set G))).map
      (centralizer (V : Set G)).subtype = pCore p G := by
  let := hV.normal
  let C := centralizer (V : Set G)
  obtain ⟨S, hS⟩ := T.exists_sylow_map_eq_inf_of_normal C
  have hSCore : (S : Subgroup C) = pCore p C := by
    apply (map_injective C.subtype_injective)
    exact hS.trans hCT
  have hindex : Nat.Coprime p (pCore p C).index := by
    rw [← hSCore]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr S.not_dvd_index
  have heq : primeToResidual p C = pCore p C := by
    apply le_antisymm (primeToResidual_le _ hindex)
    intro x hx
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := C)) ⟨x, hx⟩
    exact mem_primeToResidual_of_pow (congrArg Subtype.val hn)
  rw [heq]
  exact reduced_centralizer_core V hV

end Theory.GroupTheory.AmalgamLocalCores

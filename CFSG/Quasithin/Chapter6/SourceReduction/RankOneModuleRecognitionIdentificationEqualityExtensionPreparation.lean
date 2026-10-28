module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityTransfer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedReduction

/-!
# Centralizer bounds for the canonical equality closure

Write H = C_G(z), K = ⟨V^H⟩ and D = C_H(K), with V the actual natural
layer. Since the normal closure of Z_S lies in K, the local action-kernel
identity puts D in O₂(H), hence in T. The natural-module kernel theorem
identifies C_T(V) with Q = O₂(LT), so D lies in Q.

The intersection D ∩ K is a normal two-subgroup of K. It therefore lies
in P = O₂(K), and centralizing K puts it in Z(P). Once the preceding pair
calculation identifies Z(P) with ⟨z⟩, we obtain D ∩ V = ⟨z⟩. These arguments
supply two premises of the later transfer exclusion without a centralizer
order assumption or a recognition theorem.

Source: Aschbacher--Smith, proof of 6.2.13, printed pp.687--688.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

theorem equality_layer_le_closure
    (h611 : Hypothesis611 κ T L M R n) (hz : z ∈ ZS (T : Subgroup G) L R) :
    layer L R ≤ (equalityLayerClosure L R z).map (centralizer ({z} : Set G)).subtype := by
  have hh := map_mono (f := (centralizer ({z} : Set G)).subtype)
    (show (layer L R).subgroupOf (centralizer ({z} : Set G)) ≤
      equalityLayerClosure L R z from le_normalClosure)
  rwa [map_subgroupOf_eq_of_le (layer_le_involution_centralizer h611 hz)] at hh

omit [Finite G] in
theorem equality_sourceClosure_le_closure (T L R : Subgroup G) (z : G) :
    sourceClosure T L R z ≤
      (equalityLayerClosure L R z).map (centralizer ({z} : Set G)).subtype := by
  apply map_mono
  apply normalClosure_le_normal
  exact (subgroupOf_mono _ (show ZS T L R ≤ layer L R from inf_le_left)).trans
    (show (layer L R).subgroupOf (centralizer ({z} : Set G)) ≤
      equalityLayerClosure L R z from le_normalClosure)

omit [Finite G] in
theorem LocalAnalysis.equality_centralizer_le_involution_core
    (A : LocalAnalysis (T : Subgroup G) L M R z) :
    equalityCentralizer L R z ≤ (centralizer ({z} : Set G)).pCoreIn 2 := by
  rintro x ⟨xH, hx, rfl⟩
  apply (A.action_kernel xH xH.property).mp
  intro u hu
  obtain ⟨uH, huK, hu⟩ := equality_sourceClosure_le_closure (T : Subgroup G) L R z hu
  have hc : uH * xH = xH * uH := mem_centralizer_iff.mp hx uH huK
  have he : ⁅(xH : G), u⁆ = 1 := by
    rw [← hu]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (congrArg Subtype.val hc).symm
  rw [he]
  exact (zpowers z).one_mem

omit [Finite G] in
theorem LocalAnalysis.equality_centralizer_le_sylow
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    equalityCentralizer L R z ≤ (T : Subgroup G) := by
  have hh := pCoreIn_le_sylow (centralizer ({z} : Set G)) (T.subtype hTH)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at hh
  exact A.equality_centralizer_le_involution_core.trans hh

theorem equality_sylow_centralizer_eq_core
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n) :
    (T : Subgroup G) ⊓ centralizer (layer L R : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hQT := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] at hQT
  apply le_antisymm
  · exact (inf_le_inf_right _ le_sup_right).trans
      (local_layer_centralizer_eq_core h611 (hnatural.1.symm ▸ hnatural.2.1)).le
  · exact le_inf hQT (local_core_centralizes_layer h611)

theorem LocalAnalysis.equality_centralizer_le_local_core
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    equalityCentralizer L R z ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rw [← equality_sylow_centralizer_eq_core h611 hnatural]
  refine le_inf (A.equality_centralizer_le_sylow hTH) ?_
  intro x hx v hv
  obtain ⟨xH, hxH, rfl⟩ := hx
  obtain ⟨vH, hvK, rfl⟩ := equality_layer_le_closure h611 hz hv
  exact congrArg Subtype.val (mem_centralizer_iff.mp hxH vH hvK)

omit [Finite G] in
theorem equality_line_le_centralizer (z : G) (L R : Subgroup G) :
    zpowers z ≤ equalityCentralizer L R z := by
  apply zpowers_le.mpr
  have hzH : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  refine ⟨⟨z, hzH⟩, ?_, rfl⟩
  intro k _
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp k.property

omit [Finite G] in
theorem LocalAnalysis.equality_centralizer_inf_closure_le_center
    (A : LocalAnalysis (T : Subgroup G) L M R z) :
    equalityCentralizer L R z ⊓
      (equalityLayerClosure L R z).map (centralizer ({z} : Set G)).subtype ≤
      (coreCenter (equalityCore L R z)).map (centralizer ({z} : Set G)).subtype := by
  let H := centralizer ({z} : Set G)
  let K := equalityLayerClosure L R z
  let D := centralizer (K : Set H)
  have hDp : D ≤ pCore 2 H := by
    intro x hx
    have hh := A.equality_centralizer_le_involution_core (mem_map_of_mem H.subtype hx)
    obtain ⟨y, hy, he⟩ := hh
    exact (Subtype.ext he : y = x) ▸ hy
  have hCP : D ⊓ K ≤ equalityCore L R z := by
    exact le_pCoreIn_of_normalizes
      (pCore_isPGroup.to_le (inf_le_left.trans hDp)) inf_le_right
      (by rw [normalizer_eq_top]; exact le_top)
  rintro x ⟨⟨xH, hxD, rfl⟩, hxK⟩
  have hxKH : xH ∈ K := by
    obtain ⟨k, hk, he⟩ := hxK
    exact (Subtype.ext he : k = xH) ▸ hk
  have hxP := hCP ⟨hxD, hxKH⟩
  refine ⟨xH, ?_, rfl⟩
  refine ⟨⟨xH, hxP⟩, mem_center_iff.mpr ?_, rfl⟩
  intro p
  apply Subtype.ext
  exact mem_centralizer_iff.mp hxD p ((pCoreIn_le 2 K) p.property)

theorem LocalAnalysis.equality_centralizer_inf_layer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hcenter : coreCenter (equalityCore L R z) =
      (zpowers z).subgroupOf (centralizer ({z} : Set G))) :
    equalityCentralizer L R z ⊓ layer L R = zpowers z := by
  apply le_antisymm
  · have hh := (inf_le_inf_left _ (equality_layer_le_closure h611 hz)).trans
      A.equality_centralizer_inf_closure_le_center
    rw [hcenter, subgroupOf_map_subtype] at hh
    exact hh.trans inf_le_left
  · exact le_inf (equality_line_le_centralizer z L R) (zpowers_le.mpr hz.1)


/-- Maximal two-locality identifies the normalizer once Q is normal in M. -/
theorem equality_local_core_normalizer
    (h611 : Hypothesis611 κ T L M R n)
    (hQ : (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf M).Normal) :
    normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) = M := by
  have hVQ : layer L R ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    h611.layer_le_V.trans (reduced_le_core h611.V_mem)
  have hne : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≠ ⊥ := by
    intro he
    exact h611.nontrivial_action (le_bot_iff.mp (he ▸ hVQ))
  have hQM : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ M :=
    (pCoreIn_le 2 _).trans (sup_le h611.L_le h611.sylow_le)
  have hMN := (normal_subgroupOf_iff_le_normalizer hQM).mp hQ
  exact (h611.maximal.eq_of_le
    ⟨_, hne, isPGroup_pCoreIn 2 _, rfl⟩ hMN).symm

/-- The block kernel and V = O₂(L) remove the transfer normalizer premise. -/
theorem equality_local_core_normalizer_normalizes_layer
    (h611 : Hypothesis611 κ T L M R n)
    (hQ : (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf M).Normal)
    (hV : layer L R = L.pCoreIn 2) :
    normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤
      normalizer (layer L R : Set G) := by
  rw [equality_local_core_normalizer h611 hQ, hV]
  exact ((normal_subgroupOf_iff_le_normalizer h611.L_le).mp h611.L_normal).trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

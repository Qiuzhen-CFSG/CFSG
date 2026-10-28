module
public import CFSG.Quasithin.ChapterF.Section08.CriticalPath
public import Theory.GroupTheory.CommutatorPreimageTransport
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The terminal critical-pair conclusions of F.8

F.7.11 supplies both edge-core containments and mutual normalization. If V
centralized U_γ/A₁, the exact F.8.2 kernel would put V in the local ball
kernel at the critical endpoint, a contradiction. A nontrivial V₁∩A₁ would
make V centralize every generator of U_γ by F.8.1(a). The two relative
quotient centralizers therefore have commutator in V₁∩A₁=1.

All subgroup statements live in the original G. Both quotient centralizers
are identified using actual quotient maps and relative normality, and L_γ
is identified with the two-residual of the last edge, not its two-core.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Definitions F.8.6 and Lemma F.8.7, printed p.317.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (stabilizer_base)
namespace CFSG.Quasithin.ChapterF.Section08.Setup
open Section07
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
namespace Hypothesis.CriticalPath
variable {h : D.Hypothesis} (C : h.CriticalPath)

/-- The source right-action representative g_b. -/
def gb : G := (C.g : G)⁻¹
/-- The source endpoint module U_γ=U_H^{g_b}. -/
def Ug : Subgroup G := D.U.map (MulAut.conj (C.g : G)).toMonoidHom
/-- The source endpoint point A₁=V₁^{g_b}. -/
def A₁ : Subgroup G := D.V₁.map (MulAut.conj (C.g : G)).toMonoidHom
/-- The literal ambient stabilizer of a vertex. -/
def vertexGroup (_C : h.CriticalPath) (v : Vertex (family (D := D))) : Subgroup G :=
  (stabilizer (family (D := D)) v).map (D.LT ⊔ D.H).subtype
/-- The penultimate vertex. -/
abbrev penultimate := C.path.getVert (C.path.length - 1)
/-- The second vertex along the chosen geodesic. -/
abbrev second := C.path.getVert 2

omit [Finite G] in
private theorem map_conj_generated (A : Subgroup (D.LT ⊔ D.H : Subgroup G))
    (g : (D.LT ⊔ D.H : Subgroup G)) :
    (A.map (MulAut.conj g).toMonoidHom).map (D.LT ⊔ D.H).subtype =
      (A.map (D.LT ⊔ D.H).subtype).map (MulAut.conj (g : G)).toMonoidHom := by
  rw [map_map, map_map]
  rfl

theorem endpointModule_map :
    (CriticalPairs.vertexModule (family (D := D)) h.f7Setup.seed C.endpoint).map
      (D.LT ⊔ D.H).subtype = C.Ug := by
  rw [← C.endpoint_eq, CriticalPairs.vertexModule_translate _ _ h.f7Setup.seed_normalized,
    map_conj_generated, h.secondModule_map]
  rfl

theorem endpointGroup_eq : C.vertexGroup C.endpoint =
    D.H.map (MulAut.conj (C.g : G)).toMonoidHom := by
  rw [vertexGroup, ← C.endpoint_eq, stabilizer_translate,
    show stabilizer (family (D := D)) (base (family (D := D)) true) = family true from
      stabilizer_base _ true, map_conj_generated]
  rw [show (family (D := D) true).map (D.LT ⊔ D.H).subtype = D.H from
    map_subgroupOf_eq_of_le le_sup_right]

/-- The standard edge is the original L₁T, in G. -/
theorem base_edge_eq :
    C.vertexGroup (base (family (D := D)) false) ⊓
      C.vertexGroup (base (family (D := D)) true) = D.L₁ ⊔ D.T := by
  change (Geometry.vertexStabilizer D.LT D.H (Geometry.base D.LT D.H false)).map _ ⊓
    (Geometry.vertexStabilizer D.LT D.H (Geometry.base D.LT D.H true)).map _ = _
  rw [Geometry.base_stabilizer_map_false, Geometry.base_stabilizer_map_true, h.LT_inf_H_eq]

/-- Both edge-core containments of F.8.7(2), in the original ambient group. -/
theorem edge_cores :
    D.U ≤ (C.vertexGroup C.penultimate ⊓ C.vertexGroup C.endpoint).pCoreIn 2 ∧
    C.Ug ≤ (C.vertexGroup (base (family (D := D)) true) ⊓ C.vertexGroup C.second).pCoreIn 2 := by
  let F := family (D := D)
  let S := h.f7Setup
  obtain ⟨hpen, hseg, htwo, hend⟩ := CriticalPairs.geodesic_internal_segments F S
    h.f7V_ne_bot C.distance h.lemma_F_8_5.1 C.path C.shortest C.first
  have hl := CriticalPairs.geodesic_edge_core F S h.f7V_ne_bot
    (s := base F true) rfl hseg hpen
  have hr := CriticalPairs.odd_endpoint_edge_core F S h.f7V_ne_bot
    C.distance h.odd_b htwo hend
  constructor
  · have hm := map_mono (f := (D.LT ⊔ D.H).subtype) hl
    rwa [h.secondModule_map, ← AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (D.LT ⊔ D.H).subtype_injective, Subgroup.map_inf _ _ _
      (D.LT ⊔ D.H).subtype_injective] at hm
  · have hm := map_mono (f := (D.LT ⊔ D.H).subtype) hr
    rwa [C.endpointModule_map, ← AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (D.LT ⊔ D.H).subtype_injective, Subgroup.map_inf _ _ _
      (D.LT ⊔ D.H).subtype_injective] at hm

/-- The commutator lies in both actual endpoint modules. -/
theorem commutator_le_inf : ⁅D.U, C.Ug⁆ ≤ D.U ⊓ C.Ug := by
  have hh := (CriticalPairs.odd_geodesic_commutators _ h.f7Setup h.f7V_ne_bot
    C.distance h.odd_b h.lemma_F_8_5.1 C.path C.shortest C.first).1
  have hm := map_mono (f := (D.LT ⊔ D.H).subtype) hh
  rwa [map_commutator, Subgroup.map_inf _ _ _ (D.LT ⊔ D.H).subtype_injective,
    h.secondModule_map, C.endpointModule_map] at hm

/-- F.8.7(4): U_γ acts on the actual V_{γ₁}=U_H. -/
theorem normalizes_U : C.Ug ≤ normalizer (D.U : Set G) :=
  le_normalizer_iff_commutator_le_left.mpr (C.commutator_le_inf.trans inf_le_left)

/-- The entire seed lies in the endpoint stabilizer. -/
theorem V_le_endpointGroup : D.V ≤ C.vertexGroup C.endpoint := by
  have hh := CriticalPairs.firstModule_le_stabilizer_at_dist_le _ h.f7Setup
    h.f7V_ne_bot (a := base (family (D := D)) false) rfl C.distance.le
  rw [CriticalPairs.firstModule_base _ _ h.f7Setup.seed_normalized] at hh
  have hm := map_mono (f := (D.LT ⊔ D.H).subtype) hh
  rwa [h.f7Seed_map] at hm

include h in
/-- The F.8.2 action kernel detects a subgroup of the original H. -/
private theorem le_QH_of_commutator (A : Subgroup G) (hA : A ≤ D.H)
    (hc : ⁅D.U, A⁆ ≤ D.V₁) : A ≤ D.QH := by
  intro a ha
  have hk : (⟨a, hA ha⟩ : D.H) ∈ D.quotientCentralizer h.H_le D.U :=
    (mem_quotientCentralizer_iff _ _ _ (h.g2.U_le_H.trans h.H_le) _).mpr
      (fun u hu => hc (commutator_mem_commutator hu ha))
  rw [h.quotientCentralizer_U_eq_pCore] at hk
  exact mem_map_of_mem D.H.subtype hk

omit [Finite G] in
private theorem conj_cancel (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [map_map]
  have hi : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by ext x; simp [MulAut.conj_apply, mul_assoc]
  rw [hi, map_id]

/-- Criticality and the exact F.8.2 kernel rule out centralization modulo A₁. -/
theorem commutator_not_le_A₁ : ¬ ⁅C.Ug, D.V⁆ ≤ C.A₁ := by
  intro hc
  let f := (MulAut.conj (C.g : G)⁻¹).toMonoidHom
  have hVH : D.V.map f ≤ D.H := by
    have hm := map_mono (f := f) C.V_le_endpointGroup
    rw [C.endpointGroup_eq, conj_cancel] at hm
    exact hm
  have hm := map_mono (f := f) hc
  rw [map_commutator, Ug, A₁, conj_cancel, conj_cancel] at hm
  have hQ := le_QH_of_commutator (h := h) (D.V.map f) hVH hm
  have hvcore : D.V ≤ (C.vertexGroup C.endpoint).pCoreIn 2 := by
    have hh := map_mono (f := (MulAut.conj (C.g : G)).toMonoidHom) hQ
    have hi := conj_cancel D.V (C.g : G)⁻¹
    rw [inv_inv] at hi
    rw [hi] at hh
    rw [C.endpointGroup_eq, AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (MulAut.conj (C.g : G)).injective]
    exact hh
  have hcore : h.f7Setup.seed ≤ (stabilizer (family (D := D)) C.endpoint).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective (D.LT ⊔ D.H).subtype_injective).mp
    rw [h.f7Seed_map, ← AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (D.LT ⊔ D.H).subtype_injective]
    exact hvcore
  have hk : (stabilizer (family (D := D)) C.endpoint).pCoreIn 2 ≤
      ballKernel (family (D := D)) C.endpoint 1 := by
    have hh := map_mono (f := (MulAut.conj C.g).toMonoidHom)
      (CriticalPairs.Completion.base_core_le_kernel _ h.f7Setup true)
    rw [← ballKernel_translate, C.endpoint_eq,
      ← AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (MulAut.conj C.g).injective] at hh
    rw [← C.endpoint_eq, stabilizer_translate,
      show stabilizer (family (D := D)) (base (family (D := D)) true) = family true from
        stabilizer_base _ true, C.endpoint_eq]
    exact hh
  exact C.critical (hcore.trans hk)

/-- A common nontrivial point would make V commute with every generator of U_γ. -/
theorem points_disjoint : D.V₁ ⊓ C.A₁ = ⊥ := by
  by_contra hne
  have hc : C.Ug ≤ centralizer (D.V : Set G) := by
    rw [Ug, ChapterG.Section02.Setup.U, conjugateSpanBy_eq_iSup_conj,
      Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    let k : G := (C.g : G) * (a : G)
    have hm : (D.V.map (MulAut.conj (a : G)).toMonoidHom).map
        (MulAut.conj (C.g : G)).toMonoidHom = D.V.map (MulAut.conj k).toMonoidHom := by
      rw [map_map]
      congr 1
      ext x
      simp [k, MulAut.conj_apply, mul_assoc]
    rw [hm]
    have hpoint : C.A₁ ≤ D.V.map (MulAut.conj k).toMonoidHom := by
      have hfix : D.V₁.map (MulAut.conj (a : G)).toMonoidHom = D.V₁ :=
        mem_normalizer_iff_map_conj_eq.mp (h.H_le a.property)
      rw [← hm, A₁, ← hfix]
      exact map_mono (map_mono h.point_le)
    have hi : D.V₁ ⊓ D.V.map (MulAut.conj k).toMonoidHom ≠ ⊥ := by
      intro hz
      exact hne (eq_bot_iff.mpr ((inf_le_inf_left _ hpoint).trans hz.le))
    have he := h.conjugates_commute k⁻¹ (by
      simpa only [ChapterG.Section02.Setup.conjugate, inv_inv] using hi)
    rw [ChapterG.Section02.Setup.conjugate, inv_inv] at he
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
  exact C.commutator_not_le_A₁ ((commutator_eq_bot_iff_le_centralizer.mpr hc).le.trans bot_le)

/-- The two literal relative centralizers of F.8.6, expressed first by commutators. -/
def DH : Subgroup G := commutatorPreimage D.U C.Ug C.A₁

def Dg : Subgroup G := commutatorPreimage C.Ug D.U D.V₁

theorem U_le_endpoint : D.U ≤ C.vertexGroup C.endpoint :=
  C.edge_cores.1.trans ((pCoreIn_le 2 _).trans inf_le_right)

theorem Ug_le_H : C.Ug ≤ D.H := by
  have hh := C.edge_cores.2.trans ((pCoreIn_le 2 _).trans inf_le_left)
  have he : C.vertexGroup (base (family (D := D)) true) = D.H :=
    Geometry.base_stabilizer_map_true D.LT D.H
  rwa [he] at hh

theorem U_normalizes_A₁ : D.U ≤ normalizer (C.A₁ : Set G) := by
  have hh := C.U_le_endpoint
  rw [C.endpointGroup_eq] at hh
  apply hh.trans
  apply le_normalizer_iff.mpr
  rintro _ ⟨a, ha, rfl⟩ _ ⟨v, hv, rfl⟩
  exact ⟨a * v * a⁻¹, le_normalizer_iff.mp h.H_le a ha v hv, by simp [mul_assoc]⟩

theorem Ug_normalizes_point : C.Ug ≤ D.G₁ := C.Ug_le_H.trans h.H_le

/-- F.8.6's first definition is the centralizer on the literal quotient
N_G(A₁)/A₁, with no ambient normality assumption on A₁. -/
theorem DH_eq_quotientCentralizer :
    let N := normalizer (C.A₁ : Set G)
    letI : (C.A₁.subgroupOf N).Normal := C.A₁.normal_in_normalizer
    C.DH =
      (centralizerModulo (D.U.subgroupOf N) (C.Ug.subgroupOf N)
        (C.A₁.subgroupOf N)).map N.subtype := by
  let N := normalizer (C.A₁ : Set G)
  let : (C.A₁.subgroupOf N).Normal := C.A₁.normal_in_normalizer
  have hUgN : C.Ug ≤ N := by
    apply le_normalizer_iff.mpr
    rintro _ ⟨a, ha, rfl⟩ _ ⟨v, hv, rfl⟩
    have haN := h.H_le (h.g2.U_le_H ha)
    exact ⟨a * v * a⁻¹, le_normalizer_iff.mp (show D.U ≤ D.G₁ from
      h.g2.U_le_H.trans h.H_le) a ha v hv, by simp [mul_assoc]⟩
  change C.DH = (centralizerModulo (D.U.subgroupOf N) (C.Ug.subgroupOf N)
    (C.A₁.subgroupOf N)).map N.subtype
  calc
    C.DH = (C.DH.subgroupOf N).map N.subtype :=
      (map_subgroupOf_eq_of_le ((commutatorPreimage_le _ _ _).trans C.U_normalizes_A₁)).symm
    _ = _ := by
      rw [DH, commutatorPreimage_subgroupOf _ _ _ N C.U_normalizes_A₁ hUgN le_rfl,
        commutatorPreimage_eq_inf_comap_centralizer]
      rfl

/-- The second definition uses the original tilde quotient N_G(V₁)/V₁. -/
theorem Dg_eq_quotientCentralizer :
    C.Dg = ((D.quotientCentralizer h.H_le D.U).map D.H.subtype) ⊓ C.Ug := by
  apply le_antisymm
  · intro x hx
    have hxU := commutatorPreimage_le C.Ug D.U D.V₁ hx
    have hc := commutator_commutatorPreimage_le C.Ug D.U D.V₁ C.Ug_normalizes_point
    have hcx : ∀ u ∈ D.U, ⁅u, x⁆ ∈ D.V₁ := by
      intro u hu
      rw [← commutatorElement_inv]
      exact D.V₁.inv_mem (hc (commutator_mem_commutator hx hu))
    exact ⟨⟨⟨x, C.Ug_le_H hxU⟩,
      (mem_quotientCentralizer_iff _ _ _ (h.g2.U_le_H.trans h.H_le) _).mpr hcx, rfl⟩, hxU⟩
  · rintro x ⟨⟨y, hy, rfl⟩, hxU⟩
    have hc := (mem_quotientCentralizer_iff _ _ _ (h.g2.U_le_H.trans h.H_le) _).mp hy
    have hxp : zpowers (y : G) ≤ C.Ug := zpowers_le.mpr hxU
    apply le_commutatorPreimage hxp _ (mem_zpowers (y : G))
    have hzy : zpowers (y : G) ≤ (D.quotientCentralizer h.H_le D.U).map D.H.subtype :=
      zpowers_le.mpr (mem_map_of_mem _ hy)
    rw [commutator_comm]
    apply commutator_le.mpr
    intro u hu a ha
    obtain ⟨z, hz, rfl⟩ := hzy ha
    exact (mem_quotientCentralizer_iff _ _ _ (h.g2.U_le_H.trans h.H_le) _).mp hz u hu

/-- F.8.7(6): both commutators lie in the specified, distinct points. -/
theorem centralizer_commutators : ⁅C.Ug, C.DH⁆ ≤ C.A₁ ∧ ⁅D.U, C.Dg⁆ ≤ D.V₁ := by
  constructor
  · rw [commutator_comm]
    exact commutator_commutatorPreimage_le D.U C.Ug C.A₁ C.U_normalizes_A₁
  · rw [commutator_comm]
    exact commutator_commutatorPreimage_le C.Ug D.U D.V₁ C.Ug_normalizes_point

/-- F.8.7(7): the two quotient centralizers commute. -/
theorem centralizers_commute : ⁅C.DH, C.Dg⁆ = ⊥ := by
  apply eq_bot_iff.mpr
  have hA : ⁅C.DH, C.Dg⁆ ≤ C.A₁ := by
    rw [commutator_comm]
    exact (commutator_mono (commutatorPreimage_le _ _ _) le_rfl).trans
      C.centralizer_commutators.1
  have hV : ⁅C.DH, C.Dg⁆ ≤ D.V₁ :=
    (commutator_mono (commutatorPreimage_le _ _ _) le_rfl).trans
      C.centralizer_commutators.2
  exact (le_inf hV hA).trans C.points_disjoint.le

/-- All seven clauses of F.8.7, with the original chosen geodesic and
literal subgroups in G. -/
theorem lemma_F_8_7 :
    (C.vertexGroup (base (family (D := D)) false) ⊓
      C.vertexGroup (base (family (D := D)) true) = D.L₁ ⊔ D.T) ∧
    (D.U ≤ (C.vertexGroup C.penultimate ⊓ C.vertexGroup C.endpoint).pCoreIn 2 ∧
      C.Ug ≤ (C.vertexGroup (base (family (D := D)) true) ⊓ C.vertexGroup C.second).pCoreIn 2) ∧
    ⁅D.U, C.Ug⁆ ≤ D.U ⊓ C.Ug ∧
    C.Ug ≤ normalizer (D.U : Set G) ∧
    (¬ ⁅C.Ug, D.V⁆ ≤ C.A₁) ∧ D.V₁ ⊓ C.A₁ = ⊥ ∧
    (⁅C.Ug, C.DH⁆ ≤ C.A₁ ∧ ⁅D.U, C.Dg⁆ ≤ D.V₁) ∧
    ⁅C.DH, C.Dg⁆ = ⊥ :=
  ⟨C.base_edge_eq, C.edge_cores, C.commutator_le_inf, C.normalizes_U,
    C.commutator_not_le_A₁, C.points_disjoint, C.centralizer_commutators,
    C.centralizers_commute⟩

include h in
/-- The point-stabilizer two-residual is normalized by the original T. -/
private theorem T_normalizes_L₁ : D.T ≤ normalizer (D.L₁ : Set G) := by
  let A := D.L ⊓ D.G₁
  have hTA : D.T ≤ normalizer (A : Set G) :=
    (le_inf h.T_normalizes_L (h.T_normalizes_point.trans D.G₁.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact hTA.trans (normalizer_le_normalizer_characteristic_image A (pResidual 2 A))

include h in
/-- The embedded residual of the standard edge is the original L₁. -/
theorem edge_residual : (pResidual 2 (D.L₁ ⊔ D.T : Subgroup G)).map
    (D.L₁ ⊔ D.T).subtype = D.L₁ := by
  obtain ⟨P, hP⟩ := h.sylow
  exact embedded_pResidual_join_pGroup D.L₁ D.T
    (isPPerfect_embedded_pResidual 2 (D.L ⊓ D.G₁))
    (hP ▸ P.isPGroup') (T_normalizes_L₁ (h := h))

/-- The source L_γ=L₁^{g_b}. -/
def Lg : Subgroup G := D.L₁.map (MulAut.conj (C.g : G)).toMonoidHom

/-- The last edge is the indicated conjugate of L₁T. -/
theorem endpoint_edge_eq :
    C.vertexGroup C.penultimate ⊓ C.vertexGroup C.endpoint =
      (D.L₁ ⊔ D.T).map (MulAut.conj (C.g : G)).toMonoidHom := by
  rw [vertexGroup, vertexGroup, penultimate, ← C.penultimate_eq, ← C.endpoint_eq,
    stabilizer_translate, stabilizer_translate,
    show stabilizer (family (D := D)) (base (family (D := D)) false) = family false from
      stabilizer_base _ false,
    show stabilizer (family (D := D)) (base (family (D := D)) true) = family true from
      stabilizer_base _ true, map_conj_generated, map_conj_generated,
    ← Subgroup.map_inf _ _ _ (MulAut.conj (C.g : G)).injective]
  rw [show (family (D := D) false).map (D.LT ⊔ D.H).subtype = D.LT from
    map_subgroupOf_eq_of_le le_sup_left,
    show (family (D := D) true).map (D.LT ⊔ D.H).subtype = D.H from
    map_subgroupOf_eq_of_le le_sup_right, h.LT_inf_H_eq]

/-- The residual convention in F.8.6: L_γ is O² of the last edge stabilizer. -/
theorem Lg_eq_residual : C.Lg =
    (pResidual 2 (C.vertexGroup C.penultimate ⊓ C.vertexGroup C.endpoint : Subgroup G)).map
      (C.vertexGroup C.penultimate ⊓ C.vertexGroup C.endpoint).subtype := by
  rw [C.endpoint_edge_eq, ← map_embedded_pResidual, edge_residual (h := h)]
  rfl

/-- In the manuscript's right-conjugation convention the endpoint module is U_H^{g_b}. -/
theorem Ug_eq_conjugate : C.Ug = ChapterG.Section02.Setup.conjugate D.U C.gb := by
  simp only [Ug, ChapterG.Section02.Setup.conjugate, gb, inv_inv]

/-- The endpoint point is literally V₁^{g_b}. -/
theorem A₁_eq_conjugate : C.A₁ = ChapterG.Section02.Setup.conjugate D.V₁ C.gb := by
  simp only [A₁, ChapterG.Section02.Setup.conjugate, gb, inv_inv]

/-- The endpoint residual is literally L₁^{g_b}. -/
theorem Lg_eq_conjugate : C.Lg = ChapterG.Section02.Setup.conjugate D.L₁ C.gb := by
  simp only [Lg, ChapterG.Section02.Setup.conjugate, gb, inv_inv]

end Hypothesis.CriticalPath

end CFSG.Quasithin.ChapterF.Section08.Setup

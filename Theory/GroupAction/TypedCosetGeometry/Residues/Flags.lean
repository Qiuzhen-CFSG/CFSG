module
public import Theory.GroupAction.TypedCosetGeometry
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Rank-three flags and the string property

Suppose the middle vertex subgroup is the setwise product of its intersections
with the two endpoint subgroups. Every point and plane incident with the same
line then have a common representative in that line coset. Consequently every
pairwise incident flag has a common representative, and flags with the same
types form a single orbit. This also proves the complete bipartite incidence
property of line residues and both point/plane containment statements.

The proof at the standard line factors `a⁻¹ * b` into the two intersections;
translation gives the statement at an arbitrary line. Flags missing a type
reduce to a pair of incident vertices. These results need neither finiteness
nor generation assumptions; generation is needed separately for connectivity.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.3
and I.5.6, printed pp. 419–420; cf. Aschbacher, *Sporadic Groups*, section 4.
-/

@[expose] public section
namespace Subgroup.CosetGeometry
open scoped Pointwise
variable {G : Type*} [Group G]

/-- The middle parabolic is the setwise product of its intersections with the endpoints. -/
def MiddleProduct (F : Fin 3 → Subgroup G) : Prop :=
  (F 1 : Set G) = (↑(F 1 ⊓ F 0) : Set G) * (↑(F 1 ⊓ F 2) : Set G)

variable (F : Fin 3 → Subgroup G)

/-- An incident point and plane at the base line share a representative in the line group. -/
theorem common_representative_at_base_line (hprod : MiddleProduct F)
    (p : G ⧸ F 0) (q : G ⧸ F 2)
    (hp : Incident F (base F 1) ⟨0, p⟩) (hq : Incident F (base F 1) ⟨2, q⟩) :
    ∃ g : G, g ∈ F 1 ∧ (g : G ⧸ F 0) = p ∧ (g : G ⧸ F 2) = q := by
  obtain ⟨a, ha, hap⟩ := (incident_base_iff F 1 _).mp hp
  obtain ⟨b, hb, hbq⟩ := (incident_base_iff F 1 _).mp hq
  have hab : a⁻¹ * b ∈ (↑(F 1 ⊓ F 0) : Set G) * (↑(F 1 ⊓ F 2) : Set G) := by
    rw [← hprod]
    exact (F 1).mul_mem ((F 1).inv_mem ha) hb
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hab
  have haxy : a * x * y = b := by rw [mul_assoc, hxy, mul_inv_cancel_left]
  refine ⟨a * x, (F 1).mul_mem ha hx.1, ?_, ?_⟩
  · apply Eq.trans _ hap
    apply QuotientGroup.eq.mpr
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using (F 0).inv_mem hx.2
  · apply Eq.trans _ hbq
    apply QuotientGroup.eq.mpr
    rw [← haxy, inv_mul_cancel_left]
    exact hy.2

/-- Two vertices of endpoint types incident with a line share a representative with it. -/
theorem common_representative_on_line (hprod : MiddleProduct F)
    (p : G ⧸ F 0) (l : G ⧸ F 1) (q : G ⧸ F 2)
    (hp : Incident F ⟨1, l⟩ ⟨0, p⟩) (hq : Incident F ⟨1, l⟩ ⟨2, q⟩) :
    ∃ g : G, (g : G ⧸ F 0) = p ∧ (g : G ⧸ F 1) = l ∧
      (g : G ⧸ F 2) = q := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective l
  have hbase : a⁻¹ • (⟨1, (a : G ⧸ F 1)⟩ : Vertex F) = base F 1 := by
    change Vertex.mk 1 (a⁻¹ • (a : G ⧸ F 1)) = _
    rw [MulAction.Quotient.smul_mk]
    simp only [smul_eq_mul, inv_mul_cancel]
    rfl
  have hp' := hp.smul F a⁻¹
  have hq' := hq.smul F a⁻¹
  rw [hbase] at hp' hq'
  obtain ⟨g, hg, hgp, hgq⟩ := common_representative_at_base_line F hprod
    (a⁻¹ • p) (a⁻¹ • q) hp' hq'
  refine ⟨a * g, ?_, ?_, ?_⟩
  · simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, smul_inv_smul] using
      congrArg (a • ·) hgp
  · apply QuotientGroup.eq.mpr
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using (F 1).inv_mem hg
  · simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, smul_inv_smul] using
      congrArg (a • ·) hgq

/-- The string property: a point and a plane incident with a common line are incident. -/
theorem incident_of_incident_line (hprod : MiddleProduct F)
    {p : G ⧸ F 0} {l : G ⧸ F 1} {q : G ⧸ F 2}
    (hp : Incident F ⟨0, p⟩ ⟨1, l⟩) (hq : Incident F ⟨1, l⟩ ⟨2, q⟩) :
    Incident F ⟨0, p⟩ ⟨2, q⟩ := by
  obtain ⟨g, hgp, _, hgq⟩ := common_representative_on_line F hprod p l q (hp.symm F) hq
  exact ⟨g, hgp, hgq⟩

private theorem common_of_two_types {s : Set (Vertex F)} (hs : IsFlag F s)
    {v w : Vertex F} (hv : v ∈ s) (hw : w ∈ s)
    (hcover : ∀ u ∈ s, u.type = v.type ∨ u.type = w.type) :
    ∃ g : G, ∀ u ∈ s, (g : G ⧸ F u.type) = u.coset := by
  obtain ⟨g, hgv, hgw⟩ := hs v hv w hw
  refine ⟨g, fun u hu => ?_⟩
  rcases hcover u hu with h | h
  · have heq := hs.type_injective F hu hv h
    subst u
    exact hgv
  · have heq := hs.type_injective F hu hw h
    subst u
    exact hgw

/-- In rank three, the middle product condition implies a common representative for every flag. -/
theorem IsFlag.common_representative {s : Set (Vertex F)} (hs : IsFlag F s)
    (hprod : MiddleProduct F) : ∃ g : G, ∀ v ∈ s, (g : G ⧸ F v.type) = v.coset := by
  classical
  by_cases h0 : ∃ v ∈ s, v.type = 0
  · obtain ⟨p, hp, ht0⟩ := h0
    by_cases h1 : ∃ v ∈ s, v.type = 1
    · obtain ⟨l, hl, ht1⟩ := h1
      by_cases h2 : ∃ v ∈ s, v.type = 2
      · obtain ⟨q, hq, ht2⟩ := h2
        rcases p with ⟨i, p⟩; rcases l with ⟨j, l⟩; rcases q with ⟨k, q⟩
        change i = 0 at ht0; change j = 1 at ht1; change k = 2 at ht2
        subst i; subst j; subst k
        obtain ⟨g, hgp, hgl, hgq⟩ := common_representative_on_line F hprod p l q
          (hs _ hl _ hp) (hs _ hl _ hq)
        refine ⟨g, fun v hv => ?_⟩
        have htypes : v.type = 0 ∨ v.type = 1 ∨ v.type = 2 := by omega
        rcases htypes with ht | ht | ht
        · have heq := hs.type_injective F hv hp ht
          subst v
          exact hgp
        · have heq := hs.type_injective F hv hl ht
          subst v
          exact hgl
        · have heq := hs.type_injective F hv hq ht
          subst v
          exact hgq
      · apply common_of_two_types F hs hp hl
        intro v hv
        have hn : v.type ≠ 2 := fun ht => h2 ⟨v, hv, ht⟩
        rw [ht0, ht1]
        omega
    · by_cases h2 : ∃ v ∈ s, v.type = 2
      · obtain ⟨q, hq, ht2⟩ := h2
        apply common_of_two_types F hs hp hq
        intro v hv
        have hn : v.type ≠ 1 := fun ht => h1 ⟨v, hv, ht⟩
        rw [ht0, ht2]
        omega
      · apply common_of_two_types F hs hp hp
        intro v hv
        have hn1 : v.type ≠ 1 := fun ht => h1 ⟨v, hv, ht⟩
        have hn2 : v.type ≠ 2 := fun ht => h2 ⟨v, hv, ht⟩
        rw [ht0]
        omega
  · by_cases h1 : ∃ v ∈ s, v.type = 1
    · obtain ⟨l, hl, ht1⟩ := h1
      by_cases h2 : ∃ v ∈ s, v.type = 2
      · obtain ⟨q, hq, ht2⟩ := h2
        apply common_of_two_types F hs hl hq
        intro v hv
        have hn : v.type ≠ 0 := fun ht => h0 ⟨v, hv, ht⟩
        rw [ht1, ht2]
        omega
      · apply common_of_two_types F hs hl hl
        intro v hv
        have hn0 : v.type ≠ 0 := fun ht => h0 ⟨v, hv, ht⟩
        have hn2 : v.type ≠ 2 := fun ht => h2 ⟨v, hv, ht⟩
        rw [ht1]
        omega
    · by_cases h2 : ∃ v ∈ s, v.type = 2
      · obtain ⟨q, hq, ht2⟩ := h2
        apply common_of_two_types F hs hq hq
        intro v hv
        have hn0 : v.type ≠ 0 := fun ht => h0 ⟨v, hv, ht⟩
        have hn1 : v.type ≠ 1 := fun ht => h1 ⟨v, hv, ht⟩
        rw [ht2]
        omega
      · refine ⟨1, fun v hv => ?_⟩
        have hn0 : v.type ≠ 0 := fun ht => h0 ⟨v, hv, ht⟩
        have hn1 : v.type ≠ 1 := fun ht => h1 ⟨v, hv, ht⟩
        have hn2 : v.type ≠ 2 := fun ht => h2 ⟨v, hv, ht⟩
        omega

/-- A representative also describes the vertex as a translated standard vertex. -/
theorem smul_base_eq_of_representative {i : Fin 3} {q : G ⧸ F i} {g : G}
    (h : (g : G ⧸ F i) = q) : g • base F i = (⟨i, q⟩ : Vertex F) := by
  change Vertex.mk i (g • ((1 : G) : G ⧸ F i)) = _
  rw [MulAction.Quotient.smul_mk]
  simp only [smul_eq_mul, mul_one, h]

/-- Every rank-three flag is a translate of standard vertices of its types. -/
theorem IsFlag.exists_smul_base {s : Set (Vertex F)} (hs : IsFlag F s)
    (hprod : MiddleProduct F) : ∃ g : G, ∀ v ∈ s, g • base F v.type = v := by
  obtain ⟨g, hg⟩ := hs.common_representative F hprod
  refine ⟨g, fun v hv => ?_⟩
  exact smul_base_eq_of_representative F (hg v hv)

/-- Flags with the same types are in the same orbit. -/
theorem flag_transitive (hprod : MiddleProduct F)
    {s t : Set (Vertex F)} (hs : IsFlag F s) (ht : IsFlag F t)
    (htypes : Vertex.type '' s = Vertex.type '' t) :
    ∃ g : G, (fun v : Vertex F => g • v) '' s = t := by
  obtain ⟨a, ha⟩ := hs.exists_smul_base F hprod
  obtain ⟨b, hb⟩ := ht.exists_smul_base F hprod
  have hmap : ∀ v ∈ s, ∀ w ∈ t, v.type = w.type → (b * a⁻¹) • v = w := by
    intro v hv w hw htype
    rw [← ha v hv, mul_smul, inv_smul_smul, htype, hb w hw]
  refine ⟨b * a⁻¹, Set.ext fun w => ?_⟩
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hmem : v.type ∈ Vertex.type '' t := htypes ▸ Set.mem_image_of_mem _ hv
    obtain ⟨w, hw, htype⟩ := hmem
    change (b * a⁻¹) • v ∈ t
    rwa [hmap v hv w hw htype.symm]
  · intro hw
    have hmem : w.type ∈ Vertex.type '' s := htypes.symm ▸ Set.mem_image_of_mem _ hw
    obtain ⟨v, hv, htype⟩ := hmem
    exact ⟨v, hv, hmap v hv w hw htype⟩

/-- The product condition turns pairwise incidence of three vertices into joint incidence. -/
theorem common_representative_three (hprod : MiddleProduct F) {u v w : Vertex F}
    (huv : Incident F u v) (huw : Incident F u w) (hvw : Incident F v w) :
    ∃ g : G, (g : G ⧸ F u.type) = u.coset ∧
      (g : G ⧸ F v.type) = v.coset ∧ (g : G ⧸ F w.type) = w.coset := by
  have hs : IsFlag F {u, v, w} := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first | exact incident_refl F _ | exact huv | exact huw | exact hvw |
      exact huv.symm F | exact huw.symm F | exact hvw.symm F
  obtain ⟨g, hg⟩ := hs.common_representative F hprod
  exact ⟨g, hg u (by simp), hg v (by simp), hg w (by simp)⟩

/-- Each cross-type pair in a line residue is incident: the residue is complete bipartite. -/
theorem line_residue_complete (hprod : MiddleProduct F) (l : G ⧸ F 1)
    (u v : Residue F (⟨1, l⟩ : Vertex F)) (hne : u.val.type ≠ v.val.type) :
    Incident F u.val v.val := by
  rcases u with ⟨⟨i, p⟩, hpi, hp⟩
  rcases v with ⟨⟨j, q⟩, hqj, hq⟩
  change i ≠ 1 at hpi
  change j ≠ 1 at hqj
  change i ≠ j at hne
  have hcases : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact incident_of_incident_line F hprod (hp.symm F) hq
  · exact (incident_of_incident_line F hprod (hq.symm F) hp).symm F

/-- I.5.6: all points of a line belong to every plane on that line. -/
theorem points_on_line_subset (hprod : MiddleProduct F)
    {l : G ⧸ F 1} {q : G ⧸ F 2} (hq : Incident F ⟨1, l⟩ ⟨2, q⟩) :
    {p : G ⧸ F 0 | Incident F ⟨0, p⟩ ⟨1, l⟩} ⊆
      {p : G ⧸ F 0 | Incident F ⟨0, p⟩ ⟨2, q⟩} :=
  fun _ hp => incident_of_incident_line F hprod hp hq

/-- I.5.6, dual form: all planes on a line contain every point of that line. -/
theorem planes_on_line_subset (hprod : MiddleProduct F)
    {l : G ⧸ F 1} {p : G ⧸ F 0} (hp : Incident F ⟨0, p⟩ ⟨1, l⟩) :
    {q : G ⧸ F 2 | Incident F ⟨1, l⟩ ⟨2, q⟩} ⊆
      {q : G ⧸ F 2 | Incident F ⟨0, p⟩ ⟨2, q⟩} :=
  fun _ hq => incident_of_incident_line F hprod hp hq

end Subgroup.CosetGeometry

module

public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Typed coset incidence

For a family of subgroups, vertices are cosets tagged by their type. Two
vertices are incident precisely when their cosets intersect. Thus a flag is
a pairwise incident set; a common representative is not assumed for a flag.
The group acts by left translation, preserving types and incidence.

The action kernel is the normal core of the intersection of the family.
This follows by restricting the action to each type and using the usual
coset-action kernel theorem. No finiteness or flag transitivity is needed.

Source: the standard coset geometry construction, Aschbacher, *Sporadic
Groups* (1994), section 4; used in Aschbacher–Smith I.5.3–4.
-/

@[expose] public section

namespace Subgroup.CosetGeometry

variable {G I : Type*} [Group G] (F : I → Subgroup G)

/-- Vertices tagged by their coset type. -/
structure Vertex where
  type : I
  coset : G ⧸ F type

instance : MulAction G (Vertex F) where
  smul g v := ⟨v.type, g • v.coset⟩
  one_smul v := by
    change Vertex.mk v.type ((1 : G) • v.coset) = v
    rw [one_smul]
  mul_smul g h v := by
    change Vertex.mk v.type ((g * h) • v.coset) = Vertex.mk v.type (g • h • v.coset)
    rw [mul_smul]

/-- The standard vertex of a specified type. -/
def base (i : I) : Vertex F := ⟨i, (1 : G)⟩

/-- Incidence is nonempty intersection of the represented left cosets. -/
def Incident (v w : Vertex F) : Prop :=
  ∃ g : G, (g : G ⧸ F v.type) = v.coset ∧ (g : G ⧸ F w.type) = w.coset

/-- A flag is a pairwise incident set. -/
def IsFlag (s : Set (Vertex F)) : Prop :=
  ∀ v ∈ s, ∀ w ∈ s, Incident F v w

/-- The vertices in a residue have a different type from its base vertex. -/
def Residue (v : Vertex F) := {w : Vertex F // w.type ≠ v.type ∧ Incident F v w}

@[simp] theorem base_type (i : I) : (base F i).type = i := rfl

@[simp] theorem smul_type (g : G) (v : Vertex F) : (g • v).type = v.type := rfl

theorem incident_refl (v : Vertex F) : Incident F v v := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective v.coset
  exact ⟨g, hg, hg⟩

theorem Incident.symm {v w : Vertex F} (h : Incident F v w) : Incident F w v := by
  obtain ⟨g, hv, hw⟩ := h
  exact ⟨g, hw, hv⟩

@[simp] theorem incident_same_type (i : I) (v w : G ⧸ F i) :
    Incident F ⟨i, v⟩ ⟨i, w⟩ ↔ v = w := by
  constructor
  · rintro ⟨g, hv, hw⟩
    exact hv.symm.trans hw
  · rintro rfl
    exact incident_refl F _

theorem Incident.smul {v w : Vertex F} (h : Incident F v w) (a : G) :
    Incident F (a • v) (a • w) := by
  obtain ⟨g, hv, hw⟩ := h
  refine ⟨a * g, ?_, ?_⟩
  · exact (MulAction.Quotient.smul_mk (F v.type) a g).symm.trans (congrArg (a • ·) hv)
  · exact (MulAction.Quotient.smul_mk (F w.type) a g).symm.trans (congrArg (a • ·) hw)

@[simp] theorem incident_smul_iff (a : G) (v w : Vertex F) :
    Incident F (a • v) (a • w) ↔ Incident F v w := by
  refine ⟨fun h => ?_, fun h => h.smul F a⟩
  simpa only [inv_smul_smul] using h.smul F a⁻¹

theorem incident_base (i j : I) : Incident F (base F i) (base F j) :=
  ⟨1, rfl, rfl⟩

/-- An incident coset has a representative in the standard vertex subgroup. -/
theorem incident_base_iff (i : I) (v : Vertex F) :
    Incident F (base F i) v ↔ ∃ g : G, g ∈ F i ∧ (g : G ⧸ F v.type) = v.coset := by
  constructor
  · rintro ⟨g, hg, hv⟩
    refine ⟨g, ?_, hv⟩
    change (g : G ⧸ F i) = ((1 : G) : G ⧸ F i) at hg
    simpa only [QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff] using hg
  · rintro ⟨g, hg, hv⟩
    refine ⟨g, ?_, hv⟩
    change (g : G ⧸ F i) = ((1 : G) : G ⧸ F i)
    simpa only [QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff] using hg

/-- A flag contains at most one vertex of each type. -/
theorem IsFlag.type_injective {s : Set (Vertex F)} (hs : IsFlag F s) :
    Set.InjOn Vertex.type s := by
  rintro ⟨i, a⟩ ha ⟨j, b⟩ hb hij
  change i = j at hij
  subst j
  have hab := (incident_same_type F i a b).mp (hs _ ha _ hb)
  exact congrArg (Vertex.mk i) hab

/-- The stabilizer of a standard vertex is the indicated subgroup. -/
@[simp] theorem stabilizer_base (i : I) : MulAction.stabilizer G (base F i) = F i := by
  ext g
  change Vertex.mk i (g • ((1 : G) : G ⧸ F i)) = Vertex.mk i ((1 : G) : G ⧸ F i) ↔ _
  rw [Vertex.mk.injEq]
  simp only [heq_eq_eq, true_and, eq_self]
  change g ∈ MulAction.stabilizer G ((1 : G) : G ⧸ F i) ↔ g ∈ F i
  rw [MulAction.stabilizer_quotient]

/-- Every vertex is a translate of the standard vertex of its type. -/
theorem exists_smul_base (v : Vertex F) : ∃ g : G, g • base F v.type = v := by
  rcases v with ⟨i, q⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, ?_⟩
  change Vertex.mk i (g • ((1 : G) : G ⧸ F i)) = _
  simp [MulAction.Quotient.smul_mk, smul_eq_mul]

/-- Pairwise incidence is weaker a priori than having a common coset representative. -/
theorem isFlag_of_common_representative (s : Set (Vertex F))
    (h : ∃ g : G, ∀ v ∈ s, (g : G ⧸ F v.type) = v.coset) : IsFlag F s := by
  obtain ⟨g, hg⟩ := h
  exact fun v hv w hw => ⟨g, hg v hv, hg w hw⟩

/-- The kernel of the action on all typed cosets is the chamber normal core. -/
theorem action_kernel :
    (MulAction.toPermHom G (Vertex F)).ker = (⨅ i, F i).normalCore := by
  apply le_antisymm
  · apply Subgroup.normal_le_normalCore.mpr
    intro g hg
    apply Subgroup.mem_iInf.mpr
    intro i
    have hfix : g • base F i = base F i := Equiv.Perm.ext_iff.mp hg _
    have hmem : g ∈ MulAction.stabilizer G (base F i) := hfix
    rwa [stabilizer_base] at hmem
  · intro g hg
    apply Equiv.Perm.ext
    rintro ⟨i, q⟩
    have hi : g ∈ (F i).normalCore := Subgroup.normalCore_mono (iInf_le F i) hg
    rw [(F i).normalCore_eq_ker] at hi
    have hfix : g • q = q := Equiv.Perm.ext_iff.mp hi q
    exact congrArg (Vertex.mk i) hfix

/-- Core-freeness of the chamber gives a faithful action on the geometry. -/
theorem faithful_of_core_free (h : (⨅ i, F i).normalCore = ⊥) :
    FaithfulSMul G (Vertex F) := by
  rw [faithfulSMul_iff]
  intro g hg
  have hmem : g ∈ (MulAction.toPermHom G (Vertex F)).ker := Equiv.Perm.ext hg
  rw [action_kernel, h] at hmem
  exact hmem

end Subgroup.CosetGeometry

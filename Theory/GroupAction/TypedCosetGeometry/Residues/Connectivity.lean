module

public import Theory.GroupAction.TypedCosetGeometry.Residues.Flags
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Connectivity of typed coset incidence graphs

The incidence graph joins incident vertices of distinct types. It is connected
when the vertex subgroups generate the ambient group. Each vertex residue is
connected when its intersections with the other vertex subgroups generate that
vertex subgroup, viewed intrinsically.

Standard vertices form a connected chamber. An element of a generating subgroup
fixes one standard vertex, so its translated chamber stays in the same connected
component. Induction over subgroup generation reaches every translate. The same
argument inside a vertex subgroup proves connectivity at its standard vertex;
translation transports this to every vertex of that type. In particular, no
finiteness, common-representative theorem for flags, or residue identification
is required.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.3(1),
printed pp. 419–420; cf. Aschbacher, *Sporadic Groups*, section 4.
-/

@[expose] public section

namespace Subgroup.CosetGeometry
variable {G I : Type*} [Group G] (F : I → Subgroup G)

/-- The full typed coset incidence graph, with edges only between distinct types. -/
def incidenceGraph : SimpleGraph (Vertex F) where
  Adj v w := v.type ≠ w.type ∧ Incident F v w
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm F⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Adjacency is incidence together with distinct types. -/
@[simp] theorem incidenceGraph_adj (v w : Vertex F) :
    (incidenceGraph F).Adj v w ↔ v.type ≠ w.type ∧ Incident F v w := Iff.rfl

/-- Left translation is an automorphism of the full incidence graph. -/
def translationGraphIso (g : G) : incidenceGraph F ≃g incidenceGraph F where
  toFun v := g • v
  invFun v := g⁻¹ • v
  left_inv v := inv_smul_smul g v
  right_inv v := smul_inv_smul g v
  map_rel_iff' := by intro v w; simp

/-- The graph automorphism acts on vertices by the original group action. -/
@[simp] theorem translationGraphIso_apply (g : G) (v : Vertex F) :
    translationGraphIso F g v = g • v := rfl

/-- The graph induced on the vertices incident with a fixed vertex of another type. -/
def residueGraph (v : Vertex F) : SimpleGraph (Residue F v) :=
  (incidenceGraph F).induce {w : Vertex F | w.type ≠ v.type ∧ Incident F v w}

/-- The residue graph inherits adjacency from the full incidence graph. -/
@[simp] theorem residueGraph_adj (v : Vertex F) (x y : Residue F v) :
    (residueGraph F v).Adj x y ↔ x.val.type ≠ y.val.type ∧ Incident F x.val y.val := Iff.rfl

/-- Left translation identifies the graphs of translated residues. -/
def translationResidueGraphIso (g : G) (v : Vertex F) :
    residueGraph F v ≃g residueGraph F (g • v) where
  toFun w := ⟨g • w.val, w.property.1, w.property.2.smul F g⟩
  invFun w := ⟨g⁻¹ • w.val, w.property.1, by
    have h := w.property.2.smul F g⁻¹
    simpa only [inv_smul_smul] using h⟩
  left_inv w := Subtype.ext (inv_smul_smul g w.val)
  right_inv w := Subtype.ext (smul_inv_smul g w.val)
  map_rel_iff' := by
    intro x y
    change ((g • x.val).type ≠ (g • y.val).type ∧
      Incident F (g • x.val) (g • y.val)) ↔ _
    simp

/-- Residue translation agrees with ambient vertex translation. -/
@[simp] theorem translationResidueGraphIso_apply (g : G) (v : Vertex F) (w : Residue F v) :
    (translationResidueGraphIso F g v w).val = g • w.val := rfl

private theorem connected_of_generating_translations
    {H J V : Type*} [Group H] [Nonempty J] (S : J → Subgroup H)
    (Γ : SimpleGraph V) (b : J → V) (act : H → V → V)
    (act_one : ∀ v, act 1 v = v)
    (act_mul : ∀ g h v, act (g * h) v = act g (act h v))
    (preserve : ∀ g v w, Γ.Adj v w → Γ.Adj (act g v) (act g w))
    (base_conn : ∀ j k, Γ.Reachable (b j) (b k))
    (fix : ∀ j g, g ∈ S j → act g (b j) = b j)
    (cover : ∀ v, ∃ g j, act g (b j) = v)
    (gen : (⨆ j, S j) = ⊤) : Γ.Connected := by
  have trans_reach (g : H) {v w : V} (h : Γ.Reachable v w) :
      Γ.Reachable (act g v) (act g w) :=
    h.map { toFun := act g, map_rel' := preserve g _ _ }
  have reach (g : H) : ∀ j k, Γ.Reachable (b j) (act g (b k)) := by
    have hg : g ∈ ⨆ j, S j := by rw [gen]; trivial
    refine Subgroup.iSup_induction S (C := fun g => ∀ j k,
      Γ.Reachable (b j) (act g (b k))) hg ?_ ?_ ?_
    · intro i g hg j k
      have h := trans_reach g (base_conn i k)
      rw [fix i g hg] at h
      exact (base_conn j i).trans h
    · intro j k; simpa only [act_one] using base_conn j k
    · intro g h hg hh j k
      rw [act_mul]
      exact (hg j j).trans (trans_reach g (hh j k))
  obtain ⟨j⟩ := ‹Nonempty J›
  apply (SimpleGraph.connected_iff_exists_forall_reachable Γ).mpr
  refine ⟨b j, fun v => ?_⟩
  obtain ⟨g, k, rfl⟩ := cover v
  exact reach g j k

private theorem base_reachable (i j : I) :
    (incidenceGraph F).Reachable (base F i) (base F j) := by
  by_cases h : i = j
  · subst j; exact .rfl
  · exact SimpleGraph.Adj.reachable ⟨h, incident_base F i j⟩

/-- A nonempty family generating the group has connected typed coset incidence graph. -/
theorem incidenceGraph_connected [Nonempty I] (hgen : (⨆ i, F i) = ⊤) :
    (incidenceGraph F).Connected := by
  apply connected_of_generating_translations F (incidenceGraph F) (base F)
    (fun g v => g • v) (one_smul G) mul_smul
  · intro g v w h
    exact ⟨h.1, h.2.smul F g⟩
  · exact base_reachable F
  · intro i g hg
    have h : g ∈ MulAction.stabilizer G (base F i) := by rwa [stabilizer_base]
    exact h
  · intro v
    obtain ⟨g, hg⟩ := exists_smul_base F v
    exact ⟨g, v.type, hg⟩
  · exact hgen

/-- Local generation inside a vertex subgroup connects its standard residue. -/
theorem base_residueGraph_connected (i : I) [Nonempty {j : I // j ≠ i}]
    (hgen : (⨆ j : {j : I // j ≠ i}, (F j.val).subgroupOf (F i)) = ⊤) :
    (residueGraph F (base F i)).Connected := by
  let b : {j : I // j ≠ i} → Residue F (base F i) := fun j =>
    ⟨base F j.val, j.property, incident_base F i j.val⟩
  have fixes (g : F i) : (g : G) • base F i = base F i := by
    have h : (g : G) ∈ MulAction.stabilizer G (base F i) := by
      rw [stabilizer_base]; exact g.property
    exact h
  let act : F i → Residue F (base F i) → Residue F (base F i) := fun g w =>
    ⟨(g : G) • w.val, w.property.1, by
      have h := w.property.2.smul F (g : G)
      rwa [fixes g] at h⟩
  apply connected_of_generating_translations
    (fun j : {j : I // j ≠ i} => (F j.val).subgroupOf (F i))
    (residueGraph F (base F i)) b act
  · intro v; apply Subtype.ext; exact one_smul G v.val
  · intro g h v; apply Subtype.ext; exact mul_smul (g : G) (h : G) v.val
  · intro g v w h; exact ⟨h.1, h.2.smul F (g : G)⟩
  · intro j k
    by_cases h : j = k
    · subst k; exact .rfl
    · exact SimpleGraph.Adj.reachable ⟨fun heq => h (Subtype.ext heq),
        incident_base F j.val k.val⟩
  · intro j g hg
    apply Subtype.ext
    have h : (g : G) ∈ MulAction.stabilizer G (base F j.val) := by
      rw [stabilizer_base]; exact hg
    exact h
  · intro v
    obtain ⟨g, hg, hq⟩ := (incident_base_iff F i v.val).mp v.property.2
    refine ⟨⟨g, hg⟩, ⟨v.val.type, v.property.1⟩, ?_⟩
    apply Subtype.ext
    change g • base F v.val.type = v.val
    rcases v with ⟨⟨j, q⟩, hv⟩
    change Vertex.mk j (g • ((1 : G) : G ⧸ F j)) = Vertex.mk j q
    rw [MulAction.Quotient.smul_mk]
    simpa only [smul_eq_mul, mul_one] using congrArg (Vertex.mk j) hq
  · exact hgen

/-- Connectivity of one residue needs generation only at its own vertex type. -/
theorem residueGraph_connected_of_local_generation (v : Vertex F)
    [Nonempty {j : I // j ≠ v.type}]
    (hgen : (⨆ j : {j : I // j ≠ v.type}, (F j.val).subgroupOf (F v.type)) = ⊤) :
    (residueGraph F v).Connected := by
  obtain ⟨g, hg⟩ := exists_smul_base F v
  have hc := (base_residueGraph_connected F v.type hgen).map
    (translationResidueGraphIso F g (base F v.type)).toHom
    (translationResidueGraphIso F g (base F v.type)).toEquiv.surjective
  rwa [hg] at hc

/-- In rank three, local generation at each type makes every vertex residue connected. -/
theorem residueGraph_connected (F : Fin 3 → Subgroup G)
    (hgen : ∀ i, (⨆ j : {j : Fin 3 // j ≠ i}, (F j.val).subgroupOf (F i)) = ⊤)
    (v : Vertex F) : (residueGraph F v).Connected := by
  have : Nonempty {j : Fin 3 // j ≠ v.type} := by
    by_cases h : v.type = 0
    · exact ⟨⟨1, by rw [h]; decide⟩⟩
    · exact ⟨⟨0, fun heq => h heq.symm⟩⟩
  exact residueGraph_connected_of_local_generation F v (hgen v.type)

end Subgroup.CosetGeometry

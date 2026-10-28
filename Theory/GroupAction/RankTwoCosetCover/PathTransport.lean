module

public import Theory.GroupAction.RankTwoCosetCover
public import Theory.Combinatorics.SimpleGraph.PathLifting
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Equivariant path transport for coset coverings

The vertex stabilizer acts on based walks by translating every vertex. Unique
lifting intertwines this action with the stabilizer isomorphism induced by the
original group homomorphism. Hence the literal pointwise path stabilizers have
equal images and are isomorphic, and transitivity on nonbacktracking paths
transfers. Composing the inverse of one correspondence with another gives the
same results for two coverings from a common group.

All path types are `SimpleGraph.BasedWalk`; the forward equivalences are the
existing `coveringEquiv` and `nonbacktrackingEquiv`. Ordered vertex lists justify
equivariance and identify the action stabilizer with the pointwise fixer.
Lengths zero and arbitrary finite lengths are included.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, F.3.2–F.3.4,
printed p.270. The left-action convention corresponds to the source right action
by inversion, as recorded by `rightVertex_mul` and `vertex_rightVertex`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace SimpleGraph.BasedWalk
variable {V : Type*} {G : SimpleGraph V}

def rebase {n : ℕ} {x y : V} (h : x = y) (p : BasedWalk G n x) : BasedWalk G n y := h ▸ p
@[simp] theorem vertices_rebase {n : ℕ} {x y : V} (h : x = y) (p : BasedWalk G n x) :
    (rebase h p).vertices = p.vertices := by subst y; rfl
@[simp] theorem nonbacktracking_rebase {n : ℕ} {x y : V} (h : x = y) (p : BasedWalk G n x) :
    (rebase h p).Nonbacktracking ↔ p.Nonbacktracking := by subst y; rfl
end SimpleGraph.BasedWalk

namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.BasedWalk
variable {A : Type*} [Group A] (F : Bool → Subgroup A)

def actPath {n : ℕ} {v : Vertex F} (a : stabilizer F v) (p : BasedWalk (graph F) n v) :
    BasedWalk (graph F) n v :=
  rebase (MulAction.mem_stabilizer_iff.mp a.property) (p.map (translationGraphIso F (a : A)).toHom)

@[simp] theorem vertices_actPath {n : ℕ} {v : Vertex F} (a : stabilizer F v)
    (p : BasedWalk (graph F) n v) :
    (actPath F a p).vertices = p.vertices.map ((a : A) • ·) := by
  simp only [actPath, vertices_rebase, vertices_map]
  rfl

instance pathAction (n : ℕ) (v : Vertex F) : MulAction (stabilizer F v) (BasedWalk (graph F) n v) where
  smul := actPath F
  one_smul p := by
    apply vertices_injective n v
    change (actPath F 1 p).vertices = p.vertices
    rw [vertices_actPath]
    simp only [OneMemClass.coe_one, one_smul]
    exact List.map_id _
  mul_smul a b p := by
    apply vertices_injective n v
    change (actPath F (a * b) p).vertices = (actPath F a (actPath F b p)).vertices
    rw [vertices_actPath, vertices_actPath, vertices_actPath, List.map_map]
    simp only [Subgroup.coe_mul, mul_smul, Function.comp_def]

@[simp] theorem vertices_smul_path {n : ℕ} {v : Vertex F} (a : stabilizer F v)
    (p : BasedWalk (graph F) n v) :
    (a • p).vertices = p.vertices.map ((a : A) • ·) := vertices_actPath F a p

theorem nonbacktracking_smul_path {n : ℕ} {v : Vertex F} (a : stabilizer F v)
    (p : BasedWalk (graph F) n v) : (a • p).Nonbacktracking ↔ p.Nonbacktracking := by
  change (actPath F a p).Nonbacktracking ↔ _
  rw [actPath, nonbacktracking_rebase]
  exact nonbacktracking_map_iff (translationGraphIso F (a : A)).toHom
    (fun v => (translationGraphIso F (a : A)).mapNeighborSet v |>.injective) p

instance nonbacktrackingAction (n : ℕ) (v : Vertex F) :
    MulAction (stabilizer F v) {p : BasedWalk (graph F) n v // p.Nonbacktracking} where
  smul a p := ⟨a • p.val, (nonbacktracking_smul_path F a p.val).mpr p.property⟩
  one_smul p := Subtype.ext (one_smul _ p.val)
  mul_smul a b p := Subtype.ext (mul_smul a b p.val)

instance allPathAction (v : Vertex F) : MulAction (stabilizer F v) (Σ n, BasedWalk (graph F) n v) where
  smul a p := ⟨p.1, a • p.2⟩
  one_smul p := by rcases p with ⟨n, p⟩; exact congrArg (Sigma.mk n) (one_smul _ p)
  mul_smul a b p := by rcases p with ⟨n, p⟩; exact congrArg (Sigma.mk n) (mul_smul a b p)

instance allNonbacktrackingAction (v : Vertex F) :
    MulAction (stabilizer F v) (Σ n, {p : BasedWalk (graph F) n v // p.Nonbacktracking}) where
  smul a p := ⟨p.1, a • p.2⟩
  one_smul p := by rcases p with ⟨n, p⟩; exact congrArg (Sigma.mk n) (one_smul _ p)
  mul_smul a b p := by rcases p with ⟨n, p⟩; exact congrArg (Sigma.mk n) (mul_smul a b p)

/-- The ambient subgroup fixing each vertex of the ordered path. -/
def pathStabilizer {n : ℕ} {v : Vertex F} (p : BasedWalk (graph F) n v) : Subgroup A where
  carrier := {a | ∀ w ∈ p.vertices, a • w = w}
  one_mem' := by intro w _; exact one_smul A w
  mul_mem' := by intro a b ha hb w hw; rw [mul_smul, hb w hw, ha w hw]
  inv_mem' := by
    intro a ha w hw
    exact inv_smul_eq_iff.mpr (ha w hw).symm

theorem origin_mem_vertices {n : ℕ} {v : Vertex F} (p : BasedWalk (graph F) n v) : v ∈ p.vertices := by
  cases n <;> exact List.mem_cons_self

theorem pathStabilizer_le {n : ℕ} {v : Vertex F} (p : BasedWalk (graph F) n v) :
    pathStabilizer F p ≤ stabilizer F v := fun _ ha => ha v (origin_mem_vertices F p)

theorem mem_pathStabilizer_iff {n : ℕ} {v : Vertex F} (p : BasedWalk (graph F) n v)
    (a : stabilizer F v) : (a : A) ∈ pathStabilizer F p ↔ a • p = p := by
  rw [← (vertices_injective n v).eq_iff, vertices_smul_path]
  change (∀ w ∈ p.vertices, (a : A) • w = w) ↔ _
  simpa only [List.map_id, id_eq] using
    (List.map_inj_left (l := p.vertices) (f := fun w => (a : A) • w) (g := id)).symm

end Subgroup.CosetGeometry.RankTwo

namespace Subgroup.CosetGeometry.RankTwo.CoverData
open SimpleGraph SimpleGraph.BasedWalk
variable {A B C : Type*} [Group A] [Group B] [Group C]
variable {F : Bool → Subgroup A} {E : Bool → Subgroup B} {D : Bool → Subgroup C}
variable {f : A →* B} {g : A →* C} (c : CoverData F E f)

@[simp] theorem stabilizerEquiv_val (v : Vertex F) (a : stabilizer F v) :
    (c.stabilizerEquiv v a : B) = f a := rfl

/-- The path lifting bijection of F.3.3(1), at a prescribed length. -/
noncomputable def pathEquiv (n : ℕ) (v : Vertex F) :
    BasedWalk (graph F) n v ≃ BasedWalk (graph E) n (c.vertex v) :=
  coveringEquiv c.hom c.neighbor_bijective n v

@[simp] theorem pathEquiv_apply {n : ℕ} {v : Vertex F} (p : BasedWalk (graph F) n v) :
    c.pathEquiv n v p = p.map c.hom := coveringEquiv_apply _ _ p

@[simp] theorem pathEquiv_vertices {n : ℕ} {v : Vertex F} (p : BasedWalk (graph F) n v) :
    (c.pathEquiv n v p).vertices = p.vertices.map c.vertex := by
  rw [pathEquiv_apply, vertices_map]
  rfl

/-- The bijection intertwines the actual vertex-stabilizer representations. -/
theorem pathEquiv_smul {n : ℕ} {v : Vertex F} (a : stabilizer F v)
    (p : BasedWalk (graph F) n v) :
    c.pathEquiv n v (a • p) = c.stabilizerEquiv v a • c.pathEquiv n v p := by
  apply vertices_injective n (c.vertex v)
  rw [pathEquiv_vertices, vertices_smul_path, vertices_smul_path, pathEquiv_vertices,
    List.map_map, List.map_map]
  apply List.map_congr_left
  intro w _
  exact c.vertex_smul a w

/-- The same correspondence on nonbacktracking paths. -/
noncomputable def nbPathEquiv (n : ℕ) (v : Vertex F) :
    {p : BasedWalk (graph F) n v // p.Nonbacktracking} ≃
      {p : BasedWalk (graph E) n (c.vertex v) // p.Nonbacktracking} :=
  nonbacktrackingEquiv c.hom c.neighbor_bijective n v

theorem nbPathEquiv_smul {n : ℕ} {v : Vertex F} (a : stabilizer F v)
    (p : {p : BasedWalk (graph F) n v // p.Nonbacktracking}) :
    c.nbPathEquiv n v (a • p) = c.stabilizerEquiv v a • c.nbPathEquiv n v p := by
  apply Subtype.ext
  exact c.pathEquiv_smul a p.val

/-- All finite lengths, including repeated vertices and circuits. -/
noncomputable def allPathEquiv (v : Vertex F) :
    (Σ n, BasedWalk (graph F) n v) ≃ (Σ n, BasedWalk (graph E) n (c.vertex v)) :=
  allLengthsEquiv c.hom c.neighbor_bijective v

theorem allPathEquiv_smul {v : Vertex F} (a : stabilizer F v)
    (p : Σ n, BasedWalk (graph F) n v) :
    c.allPathEquiv v (a • p) = c.stabilizerEquiv v a • c.allPathEquiv v p := by
  rcases p with ⟨n, p⟩
  exact congrArg (Sigma.mk n) (c.pathEquiv_smul a p)

noncomputable def allNbPathEquiv (v : Vertex F) :
    (Σ n, {p : BasedWalk (graph F) n v // p.Nonbacktracking}) ≃
      (Σ n, {p : BasedWalk (graph E) n (c.vertex v) // p.Nonbacktracking}) :=
  allNonbacktrackingEquiv c.hom c.neighbor_bijective v

theorem allNbPathEquiv_smul {v : Vertex F} (a : stabilizer F v)
    (p : Σ n, {p : BasedWalk (graph F) n v // p.Nonbacktracking}) :
    c.allNbPathEquiv v (a • p) = c.stabilizerEquiv v a • c.allNbPathEquiv v p := by
  rcases p with ⟨n, p⟩
  exact congrArg (Sigma.mk n) (c.nbPathEquiv_smul a p)

/-- An element of the origin stabilizer fixes a path exactly when its image does. -/
theorem fixes_path_iff {n : ℕ} {v : Vertex F} (a : stabilizer F v)
    (p : BasedWalk (graph F) n v) :
    (c.stabilizerEquiv v a : B) ∈ pathStabilizer E (c.pathEquiv n v p) ↔
      (a : A) ∈ pathStabilizer F p := by
  rw [mem_pathStabilizer_iff, mem_pathStabilizer_iff, ← pathEquiv_smul]
  exact (c.pathEquiv n v).injective.eq_iff

/-- Literal image equality for the pointwise path stabilizers, F.3.3(3). -/
theorem pathStabilizer_map {n : ℕ} {v : Vertex F} (p : BasedWalk (graph F) n v) :
    (pathStabilizer F p).map f = pathStabilizer E (c.pathEquiv n v p) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (c.fixes_path_iff ⟨a, pathStabilizer_le F p ha⟩ p).mpr ha
  · intro hb
    let b' : stabilizer E (c.vertex v) := ⟨b, pathStabilizer_le E _ hb⟩
    obtain ⟨a, ha⟩ := (c.stabilizerEquiv v).surjective b'
    have hval : f (a : A) = b := congrArg Subtype.val ha
    have hfix : (c.stabilizerEquiv v a : B) ∈ pathStabilizer E (c.pathEquiv n v p) := by
      change f (a : A) ∈ _
      rwa [hval]
    exact mem_map.mpr ⟨a, (c.fixes_path_iff a p).mp hfix, hval⟩

/-- The isomorphism on path stabilizers is induced by the original homomorphism. -/
noncomputable def pathStabilizerEquiv {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph F) n v) :
    pathStabilizer F p ≃* pathStabilizer E (c.pathEquiv n v p) := by
  let h : pathStabilizer F p →* pathStabilizer E (c.pathEquiv n v p) :=
    { toFun := fun a => ⟨f a, by rw [← c.pathStabilizer_map p]; exact mem_map.mpr ⟨a, a.property, rfl⟩⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f (a : A) (b : A)) }
  apply MulEquiv.ofBijective h
  constructor
  · intro a b hab
    have ha : (a : A) ∈ stabilizer F v := pathStabilizer_le F p a.property
    have hb : (b : A) ∈ stabilizer F v := pathStabilizer_le F p b.property
    have hfa : f (a : A) = f (b : A) := congrArg
      (fun x : pathStabilizer E (c.pathEquiv n v p) => (x : B)) hab
    have he : c.stabilizerHom v ⟨a, ha⟩ = c.stabilizerHom v ⟨b, hb⟩ := Subtype.ext hfa
    exact Subtype.ext (congrArg (fun x : stabilizer F v => (x : A))
      ((c.stabilizerHom_bijective v).1 he))
  · intro b
    have hb : (b : B) ∈ (pathStabilizer F p).map f := by
      rw [c.pathStabilizer_map p]
      exact b.property
    obtain ⟨a, ha, he⟩ := mem_map.mp hb
    exact ⟨⟨a, ha⟩, Subtype.ext he⟩

@[simp] theorem pathStabilizerEquiv_val {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph F) n v) (a : pathStabilizer F p) :
    (c.pathStabilizerEquiv p a : B) = f a := rfl

/-- Transitivity descends through the nonbacktracking correspondence. -/
theorem nbPath_transitive (n : ℕ) (v : Vertex F)
    (h : MulAction.IsPretransitive (stabilizer F v)
      {p : BasedWalk (graph F) n v // p.Nonbacktracking}) :
    MulAction.IsPretransitive (stabilizer E (c.vertex v))
      {p : BasedWalk (graph E) n (c.vertex v) // p.Nonbacktracking} := by
  constructor
  intro p q
  obtain ⟨p', rfl⟩ := (c.nbPathEquiv n v).surjective p
  obtain ⟨q', rfl⟩ := (c.nbPathEquiv n v).surjective q
  obtain ⟨a, ha⟩ := h.exists_smul_eq p' q'
  exact ⟨c.stabilizerEquiv v a, (c.nbPathEquiv_smul a p').symm.trans (congrArg _ ha)⟩

end Subgroup.CosetGeometry.RankTwo.CoverData

namespace Subgroup.CosetGeometry.RankTwo.CoverData
open SimpleGraph SimpleGraph.BasedWalk
variable {A B C : Type*} [Group A] [Group B] [Group C]
variable {F : Bool → Subgroup A} {E : Bool → Subgroup B} {D : Bool → Subgroup C}
variable {f : A →* B} {g : A →* C} (c : CoverData F E f) (d : CoverData F D g)

/-- The local group isomorphism obtained from the two faithful completions. -/
noncomputable def transportStabilizer (v : Vertex F) :
    stabilizer E (c.vertex v) ≃* stabilizer D (d.vertex v) :=
  (c.stabilizerEquiv v).symm.trans (d.stabilizerEquiv v)

/-- Lift through the first covering, then project through the second. -/
noncomputable def transportPathEquiv (n : ℕ) (v : Vertex F) :
    BasedWalk (graph E) n (c.vertex v) ≃ BasedWalk (graph D) n (d.vertex v) :=
  (c.pathEquiv n v).symm.trans (d.pathEquiv n v)

/-- F.3.4(1), with the literal composite of the two path correspondences. -/
theorem transportPathEquiv_smul {n : ℕ} {v : Vertex F}
    (b : stabilizer E (c.vertex v)) (p : BasedWalk (graph E) n (c.vertex v)) :
    c.transportPathEquiv d n v (b • p) =
      c.transportStabilizer d v b • c.transportPathEquiv d n v p := by
  obtain ⟨a, rfl⟩ := (c.stabilizerEquiv v).surjective b
  obtain ⟨q, rfl⟩ := (c.pathEquiv n v).surjective p
  rw [← c.pathEquiv_smul]
  simpa only [transportPathEquiv, transportStabilizer, Equiv.trans_apply,
    MulEquiv.trans_apply, Equiv.symm_apply_apply, MulEquiv.symm_apply_apply] using
    d.pathEquiv_smul a q

noncomputable def transportNbPathEquiv (n : ℕ) (v : Vertex F) :
    {p : BasedWalk (graph E) n (c.vertex v) // p.Nonbacktracking} ≃
      {p : BasedWalk (graph D) n (d.vertex v) // p.Nonbacktracking} :=
  (c.nbPathEquiv n v).symm.trans (d.nbPathEquiv n v)

theorem transportNbPathEquiv_smul {n : ℕ} {v : Vertex F}
    (b : stabilizer E (c.vertex v))
    (p : {p : BasedWalk (graph E) n (c.vertex v) // p.Nonbacktracking}) :
    c.transportNbPathEquiv d n v (b • p) =
      c.transportStabilizer d v b • c.transportNbPathEquiv d n v p := by
  obtain ⟨a, rfl⟩ := (c.stabilizerEquiv v).surjective b
  obtain ⟨q, rfl⟩ := (c.nbPathEquiv n v).surjective p
  rw [← c.nbPathEquiv_smul]
  simpa only [transportNbPathEquiv, transportStabilizer, Equiv.trans_apply,
    MulEquiv.trans_apply, Equiv.symm_apply_apply, MulEquiv.symm_apply_apply] using
    d.nbPathEquiv_smul a q

noncomputable def transportAllPathEquiv (v : Vertex F) :
    (Σ n, BasedWalk (graph E) n (c.vertex v)) ≃
      (Σ n, BasedWalk (graph D) n (d.vertex v)) :=
  (c.allPathEquiv v).symm.trans (d.allPathEquiv v)

theorem transportAllPathEquiv_smul {v : Vertex F}
    (b : stabilizer E (c.vertex v)) (p : Σ n, BasedWalk (graph E) n (c.vertex v)) :
    c.transportAllPathEquiv d v (b • p) =
      c.transportStabilizer d v b • c.transportAllPathEquiv d v p := by
  obtain ⟨a, rfl⟩ := (c.stabilizerEquiv v).surjective b
  obtain ⟨q, rfl⟩ := (c.allPathEquiv v).surjective p
  rw [← c.allPathEquiv_smul]
  simpa only [transportAllPathEquiv, transportStabilizer, Equiv.trans_apply,
    MulEquiv.trans_apply, Equiv.symm_apply_apply, MulEquiv.symm_apply_apply] using
    d.allPathEquiv_smul a q

noncomputable def transportAllNbPathEquiv (v : Vertex F) :
    (Σ n, {p : BasedWalk (graph E) n (c.vertex v) // p.Nonbacktracking}) ≃
      (Σ n, {p : BasedWalk (graph D) n (d.vertex v) // p.Nonbacktracking}) :=
  (c.allNbPathEquiv v).symm.trans (d.allNbPathEquiv v)

theorem transportAllNbPathEquiv_smul {v : Vertex F}
    (b : stabilizer E (c.vertex v))
    (p : Σ n, {p : BasedWalk (graph E) n (c.vertex v) // p.Nonbacktracking}) :
    c.transportAllNbPathEquiv d v (b • p) =
      c.transportStabilizer d v b • c.transportAllNbPathEquiv d v p := by
  obtain ⟨a, rfl⟩ := (c.stabilizerEquiv v).surjective b
  obtain ⟨q, rfl⟩ := (c.allNbPathEquiv v).surjective p
  rw [← c.allNbPathEquiv_smul]
  simpa only [transportAllNbPathEquiv, transportStabilizer, Equiv.trans_apply,
    MulEquiv.trans_apply, Equiv.symm_apply_apply, MulEquiv.symm_apply_apply] using
    d.allNbPathEquiv_smul a q

/-- The full pointwise path stabilizers correspond inside the local vertex groups. -/
theorem transport_pathStabilizer_map {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph E) n (c.vertex v)) :
    ((pathStabilizer E p).subgroupOf (stabilizer E (c.vertex v))).map
      (c.transportStabilizer d v).toMonoidHom =
    (pathStabilizer D (c.transportPathEquiv d n v p)).subgroupOf
      (stabilizer D (d.vertex v)) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    change (c.transportStabilizer d v a : C) ∈ pathStabilizer D _
    apply (mem_pathStabilizer_iff D _ _).mpr
    rw [← transportPathEquiv_smul, (mem_pathStabilizer_iff E p a).mp ha]
  · intro hb
    obtain ⟨a, rfl⟩ := (c.transportStabilizer d v).surjective b
    apply mem_map.mpr
    refine ⟨a, ?_, rfl⟩
    apply (mem_pathStabilizer_iff E p a).mpr
    apply (c.transportPathEquiv d n v).injective
    rw [transportPathEquiv_smul]
    exact (mem_pathStabilizer_iff D _ _).mp hb

/-- F.3.4(2): the literal local isomorphism restricts to an isomorphism of path stabilizers. -/
noncomputable def transportPathStabilizerEquiv {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph E) n (c.vertex v)) :
    pathStabilizer E p ≃* pathStabilizer D (c.transportPathEquiv d n v p) :=
  (subgroupOfEquivOfLe (pathStabilizer_le E p)).symm.trans
    (((c.transportStabilizer d v).subgroupMap
      ((pathStabilizer E p).subgroupOf (stabilizer E (c.vertex v)))).trans
      ((MulEquiv.subgroupCongr (c.transport_pathStabilizer_map d p)).trans
        (subgroupOfEquivOfLe (pathStabilizer_le D _))))

/-- The resulting isomorphism uses precisely the local composite, not an arbitrary isomorphism. -/
@[simp] theorem transportPathStabilizerEquiv_val {n : ℕ} {v : Vertex F}
    (p : BasedWalk (graph E) n (c.vertex v)) (a : pathStabilizer E p) :
    (c.transportPathStabilizerEquiv d p a : C) =
      (c.transportStabilizer d v ⟨a, pathStabilizer_le E p a.property⟩ : C) := rfl

/-- F.3.4(3): transitivity transfers between the two completions. -/
theorem transport_nbPath_transitive (n : ℕ) (v : Vertex F)
    (h : MulAction.IsPretransitive (stabilizer E (c.vertex v))
      {p : BasedWalk (graph E) n (c.vertex v) // p.Nonbacktracking}) :
    MulAction.IsPretransitive (stabilizer D (d.vertex v))
      {p : BasedWalk (graph D) n (d.vertex v) // p.Nonbacktracking} := by
  constructor
  intro p q
  obtain ⟨p', rfl⟩ := (c.transportNbPathEquiv d n v).surjective p
  obtain ⟨q', rfl⟩ := (c.transportNbPathEquiv d n v).surjective q
  obtain ⟨a, ha⟩ := h.exists_smul_eq p' q'
  exact ⟨c.transportStabilizer d v a,
    (c.transportNbPathEquiv_smul d a p').symm.trans (congrArg _ ha)⟩

end Subgroup.CosetGeometry.RankTwo.CoverData

namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.BasedWalk
variable {A B C : Type*} [Group A] [Group B] [Group C]
variable (F : Bool → Subgroup A)

/-- The two tagged coset spaces are the actual bipartition. -/
theorem coset_bipartition : (graph F).IsBipartiteWith
    {v : Vertex F | v.type = false} {v : Vertex F | v.type = true} where
  disjoint := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    exact Bool.false_ne_true (hv.symm.trans hw)
  mem_of_adj := by
    intro v w h
    change (v.type = false ∧ w.type = true) ∨ (v.type = true ∧ w.type = false)
    have ht := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all

/-- Pointwise vertex fixation equals the stabilizer of the ordered based path. -/
theorem pathStabilizer_subgroupOf {n : ℕ} {v : Vertex F} (p : BasedWalk (graph F) n v) :
    (pathStabilizer F p).subgroupOf (stabilizer F v) = MulAction.stabilizer (stabilizer F v) p := by
  ext a
  exact mem_pathStabilizer_iff F p a

namespace CoverData
variable {F} {E : Bool → Subgroup B} {D : Bool → Subgroup C}
variable {f : A →* B} {g : A →* C} (c : CoverData F E f) (d : CoverData F D g)

/-- Under the inverse left-coset convention, this is exactly the source's right-coset map. -/
@[simp] theorem vertex_rightVertex (i : Bool) (a : A) :
    c.vertex (rightVertex F i a) = rightVertex E i (f a) := by
  simp only [rightVertex, vertex_smul, vertex_base, map_inv]

/-- The nonbacktracking bijection is the restriction of the same path bijection. -/
@[simp] theorem nbPathEquiv_val {n : ℕ} {v : Vertex F}
    (p : {p : BasedWalk (graph F) n v // p.Nonbacktracking}) :
    (c.nbPathEquiv n v p).val = c.pathEquiv n v p.val := rfl

/-- Composing the restricted correspondences agrees with restricting the composite. -/
@[simp] theorem transportNbPathEquiv_val {n : ℕ} {v : Vertex F}
    (p : {p : BasedWalk (graph E) n (c.vertex v) // p.Nonbacktracking}) :
    (c.transportNbPathEquiv d n v p).val = c.transportPathEquiv d n v p.val := by
  obtain ⟨q, rfl⟩ := (c.nbPathEquiv n v).surjective p
  simp only [transportNbPathEquiv, transportPathEquiv, Equiv.trans_apply,
    Equiv.symm_apply_apply, nbPathEquiv_val]

/-- The unrestricted correspondence preserves each fixed length. -/
@[simp] theorem allPathEquiv_length (v : Vertex F) (p : Σ n, BasedWalk (graph F) n v) :
    (c.allPathEquiv v p).1 = p.1 := rfl

@[simp] theorem transportAllPathEquiv_length (v : Vertex F)
    (p : Σ n, BasedWalk (graph E) n (c.vertex v)) :
    (c.transportAllPathEquiv d v p).1 = p.1 := by
  obtain ⟨q, rfl⟩ := (c.allPathEquiv v).surjective p
  simp only [transportAllPathEquiv, Equiv.trans_apply, Equiv.symm_apply_apply, allPathEquiv_length]

/-- Image equality for stabilizers in the full, all-length path representation. -/
theorem allPath_stabilizer_map (v : Vertex F) (p : Σ n, BasedWalk (graph F) n v) :
    (MulAction.stabilizer (stabilizer F v) p).map (c.stabilizerEquiv v).toMonoidHom =
      MulAction.stabilizer (stabilizer E (c.vertex v)) (c.allPathEquiv v p) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    change c.stabilizerEquiv v a • c.allPathEquiv v p = c.allPathEquiv v p
    rw [← allPathEquiv_smul, show a • p = p from ha]
  · intro hb
    obtain ⟨a, rfl⟩ := (c.stabilizerEquiv v).surjective b
    refine mem_map.mpr ⟨a, ?_, rfl⟩
    apply (c.allPathEquiv v).injective
    rw [allPathEquiv_smul]
    exact hb

/-- F.3.4(2) in the all-length permutation representation. -/
theorem transport_allPath_stabilizer_map (v : Vertex F)
    (p : Σ n, BasedWalk (graph E) n (c.vertex v)) :
    (MulAction.stabilizer (stabilizer E (c.vertex v)) p).map
      (c.transportStabilizer d v).toMonoidHom =
      MulAction.stabilizer (stabilizer D (d.vertex v)) (c.transportAllPathEquiv d v p) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    change c.transportStabilizer d v a • c.transportAllPathEquiv d v p =
      c.transportAllPathEquiv d v p
    rw [← transportAllPathEquiv_smul, show a • p = p from ha]
  · intro hb
    obtain ⟨a, rfl⟩ := (c.transportStabilizer d v).surjective b
    refine mem_map.mpr ⟨a, ?_, rfl⟩
    apply (c.transportAllPathEquiv d v).injective
    rw [transportAllPathEquiv_smul]
    exact hb

end CoverData
end Subgroup.CosetGeometry.RankTwo

module

public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.LocalGeometry

/-!
# Lifting translated local cycles

The actual local orbit graph embeds in the coset graph of the presentation.
Its isolated ambient vertices receive arbitrary representatives, which do not
enter any nonempty walk. Every lift of a local-orbit vertex lies in a chart
translated by a presentation element with the prescribed ambient image.
Transport along a supported walk follows that chart, so each translated local
closed walk has trivial transport at every point of its fiber.

Source: Aschbacher, *Sporadic Groups* (1994), §§35–37, especially 37.5.
-/

@[expose] public section

namespace Theory.GroupTheory.GraphUniquenessSystem.System.PathPresentation

universe u v
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable (U : System G V)

/-- A coset representing a local-orbit vertex; arbitrary at isolated vertices. -/
noncomputable def localSection (a : V) : Coset U := by
  classical
  exact if h : ∃ h : U.H, (h : G) • U.x = a then coset U (localMap U h.choose)
  else coset U 1

/-- The section agrees with every representative of a local-orbit vertex. -/
theorem localSection_eq (a : V) (h : U.H) (ha : (h : G) • U.x = a) :
    localSection U a = coset U (localMap U h) := by
  classical
  have hex : ∃ h : U.H, (h : G) • U.x = a := ⟨h, ha⟩
  simp only [localSection, dif_pos hex]
  exact (coset_local_eq_iff U _ h).mpr (hex.choose_spec.trans ha.symm)

/-- On the local vertex orbit, the section is a right inverse to projection. -/
theorem localSection_project {a : V} (ha : ∃ h : U.H, (h : G) • U.x = a) :
    project U (localSection U a) = a := by
  obtain ⟨h, hh⟩ := ha
  rw [localSection_eq U a h hh, project_coset, canonical_local, hh]

variable (t : U.H) (htx : (t : G) • U.x = U.y)

/-- The section lifts every edge of the actual local graph. -/
theorem localSection_adj {a b : V} (hab : U.localGraph.Adj a b) :
    (cosetGraph U t htx).Adj (localSection U a) (localSection U b) := by
  obtain ⟨h, hh | hh⟩ := hab
  · rw [localSection_eq U a h hh.1,
      localSection_eq U b (h * t) (by simpa only [Subgroup.coe_mul, mul_smul, htx] using hh.2),
      map_mul]
    exact cosetGraph_adj U t htx _
  · rw [localSection_eq U b h hh.1,
      localSection_eq U a (h * t) (by simpa only [Subgroup.coe_mul, mul_smul, htx] using hh.2),
      map_mul]
    exact (cosetGraph_adj U t htx _).symm

include htx in
/-- Both endpoints of a local edge belong to the local vertex orbit. -/
theorem localEdge_orbits {a b : V} (hab : U.localEdge a b) :
    (∃ h : U.H, (h : G) • U.x = a) ∧ (∃ h : U.H, (h : G) • U.x = b) := by
  obtain ⟨h, hh | hh⟩ := hab
  · exact ⟨⟨h, hh.1⟩, ⟨h * t, by simpa only [Subgroup.coe_mul, mul_smul, htx] using hh.2⟩⟩
  · exact ⟨⟨h * t, by simpa only [Subgroup.coe_mul, mul_smul, htx] using hh.2⟩, ⟨h, hh.1⟩⟩

/-- Every lift of a local-orbit vertex lies in a translated local chart whose
 translating presentation element has the specified ambient image. -/
theorem exists_local_chart (g : G) (a : Coset U) (h : U.H)
    (hh : (h : G) • U.x = g⁻¹ • project U a) :
    ∃ r : U.PathPresentation, canonical U r = g ∧ coset U (r * localMap U h) = a := by
  induction a using QuotientGroup.induction_on with
  | H p =>
    have hv : (canonical U p)⁻¹ * g * (h : G) ∈ U.vertexGroup := by
      change ((canonical U p)⁻¹ * g * (h : G)) • U.x = U.x
      rw [mul_smul, mul_smul, hh, smul_inv_smul]
      exact inv_smul_smul _ _
    let a : U.vertexGroup := ⟨(canonical U p)⁻¹ * g * (h : G), hv⟩
    refine ⟨p * vertex U a * (localMap U h)⁻¹, ?_, ?_⟩
    · simp [map_mul, map_inv, a, mul_assoc]
    · rw [inv_mul_cancel_right, coset_mul_vertex]
      rfl

variable (hf : ∀ a, Function.Bijective ((projection U t htx).mapNeighborSet a))

private theorem transport_edge_section {a b : V} (h : U.graph.Adj a b)
    {c d : Coset U} (ha : project U c = a) (hb : project U d = b)
    (hc : (cosetGraph U t htx).Adj c d) :
    ((projection U t htx).coverTransport hf).edge h ⟨c, ha⟩ = ⟨d, hb⟩ := by
  subst a b
  exact (projection U t htx).coverTransport_edge hf hc

/-- Transport along a supported walk follows any section lifting its edges. -/
private theorem transport_supported_section (R : V → V → Prop) (s : V → Coset U)
    (hadj : ∀ a b, R a b → (cosetGraph U t htx).Adj (s a) (s b))
    (hproj : ∀ a b, R a b → project U (s a) = a ∧ project U (s b) = b)
    {a b : V} (p : U.graph.Walk a b) (hp : SimpleGraph.WalkClosure.Supported R p)
    (ha : project U (s a) = a) (hb : project U (s b) = b) :
    ((projection U t htx).coverTransport hf).along p ⟨s a, ha⟩ = ⟨s b, hb⟩ := by
  induction p with
  | nil => rfl
  | @cons a c b hac p ih =>
    change ((projection U t htx).coverTransport hf).along p
      (((projection U t htx).coverTransport hf).edge hac ⟨s a, ha⟩) = _
    rw [transport_edge_section U t htx hf hac ha (hproj a c hp.1).2 (hadj a c hp.1)]
    exact ih hp.2 (hproj a c hp.1).2 hb

/-- Every translated local generator lifts closed, at every point of its fiber. -/
theorem baseCycles_transport (a : V) (p : U.graph.Walk a a) (hp : p ∈ U.baseCycles a) :
    ((projection U t htx).coverTransport hf).along p = Equiv.refl _ := by
  obtain ⟨g, hg⟩ := hp
  cases p with
  | nil => rfl
  | @cons _ b _ hab p =>
    ext z
    obtain ⟨h, hh⟩ := (localEdge_orbits U t htx hg.1).1
    have hzproj : project U z.val = a := z.property
    obtain ⟨r, hr, hz⟩ := exists_local_chart U g z.val h (by simpa only [hzproj] using hh)
    let s : V → Coset U := fun c => r • localSection U (g⁻¹ • c)
    have hproj (c d : V) (hcd : U.localEdge (g⁻¹ • c) (g⁻¹ • d)) :
        project U (s c) = c ∧ project U (s d) = d := by
      obtain ⟨hc, hd⟩ := localEdge_orbits U t htx hcd
      constructor
      · change project U (r • localSection U (g⁻¹ • c)) = c
        rw [project_smul, hr, localSection_project U hc, smul_inv_smul]
      · change project U (r • localSection U (g⁻¹ • d)) = d
        rw [project_smul, hr, localSection_project U hd, smul_inv_smul]
    have hadj (c d : V) (hcd : U.localEdge (g⁻¹ • c) (g⁻¹ • d)) :
        (cosetGraph U t htx).Adj (s c) (s d) :=
      cosetGraph_smul U t htx r (localSection_adj U t htx hcd)
    have hs : s a = z.val := by
      change r • localSection U (g⁻¹ • a) = z.val
      rw [localSection_eq U _ h hh]
      exact hz
    have ha : project U (s a) = a := (hproj a b hg.1).1
    have he := transport_supported_section U t htx hf
      (fun c d => U.localEdge (g⁻¹ • c) (g⁻¹ • d)) s hadj hproj
      (.cons hab p) hg ha ha
    have hz' : (⟨s a, ha⟩ : {c // projection U t htx c = a}) = z := Subtype.ext hs
    exact congrArg Subtype.val (show
      ((projection U t htx).coverTransport hf).along (.cons hab p) z = z by
        simpa only [hz'] using he)

end Theory.GroupTheory.GraphUniquenessSystem.System.PathPresentation

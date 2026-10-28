module

public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.CosetGeometry

/-!
# Local bijectivity and connectedness of the presentation graph

Neighbors of a coset are represented by a vertex-group element followed by a
local reversal. The edge-group intersection relations identify exactly the
representatives with the same projected endpoint, giving local bijectivity.
The local generation identity then shows that the vertex group and the
reversal generate the presentation, so its coset graph is connected.

Source: Aschbacher, *Sporadic Groups* (1994), §§35–37, especially 37.5.
-/

@[expose] public section

namespace Theory.GroupTheory.GraphUniquenessSystem.System.PathPresentation

universe u v
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable (U : System G V) (t : U.H)
variable (htx : (t : G) • U.x = U.y) (hty : (t : G) • U.y = U.x)
include htx hty

/-- The reversal square fixes the vertex coset, without requiring order two. -/
theorem coset_mul_swap_sq (p : U.PathPresentation) :
    coset U (p * localMap U t * localMap U t) = coset U p := by
  have hv : ((t * t : U.H) : G) ∈ U.vertexGroup := by
    change ((t : G) * (t : G)) • U.x = U.x
    rw [mul_smul, htx, hty]
  have he : localMap U (t * t) = vertex U ⟨t * t, hv⟩ :=
    (inclusions U).local_vertex _ (t * t).property hv
  rw [mul_assoc, ← map_mul, he, coset_mul_vertex]

/-- All neighbors have a vertex-group representative followed by the reversal. -/
theorem adj_coset_iff (p : U.PathPresentation) (b : Coset U) :
    (cosetGraph U t htx).Adj (coset U p) b ↔
      ∃ a : U.vertexGroup, b = coset U (p * vertex U a * localMap U t) := by
  constructor
  · intro h
    have ho : ∃ q, coset U q = coset U p ∧ coset U (q * localMap U t) = b := by
      obtain ⟨q, h | h⟩ := h
      · exact ⟨q, h⟩
      · exact ⟨q * localMap U t, h.2, (coset_mul_swap_sq U t htx hty q).trans h.1⟩
    obtain ⟨q, hq, hb⟩ := ho
    obtain ⟨a, ha⟩ := (coset_eq_iff U p q).mp hq.symm
    have he : q = p * vertex U a := by rw [ha, mul_inv_cancel_left]
    exact ⟨a, by simpa only [he] using hb.symm⟩
  · rintro ⟨a, rfl⟩
    simpa only [coset_mul_vertex] using cosetGraph_adj U t htx (p * vertex U a)

/-- Conjugating a pointwise edge fixer by the reversal gives a vertex fixer. -/
theorem conjugate_vertex_mem (a : U.vertexGroup) (hay : (a : G) • U.y = U.y) :
    (localMap U t)⁻¹ * vertex U a * localMap U t ∈ (vertex U).range := by
  let te : U.edgeSetGroup := ⟨t, Or.inr ⟨htx, hty⟩⟩
  let ae : U.edgeSetGroup := ⟨a, Or.inl ⟨a.property, hay⟩⟩
  let e := te⁻¹ * ae * te
  have hv : (e : G) ∈ U.vertexGroup := by
    change ((t : G)⁻¹ * (a : G) * (t : G)) • U.x = U.x
    rw [mul_smul, mul_smul, htx, hay]
    exact inv_smul_eq_iff.mpr htx.symm
  have hvE : vertex U ⟨e, hv⟩ = edge U e := (inclusions U).vertex_edge e hv e.property
  have htE : localMap U t = edge U te := (inclusions U).local_edge t t.property te.property
  have haE : vertex U a = edge U ae := (inclusions U).vertex_edge a a.property ae.property
  refine ⟨⟨e, hv⟩, ?_⟩
  rw [hvE, htE, haE]
  exact (map_mul (edge U) (te⁻¹ * ae) te).trans (by rw [map_mul, map_inv])

/-- The coset projection is bijective on each neighbor set. -/
theorem neighbor_bijective :
    ∀ q, Function.Bijective ((projection U t htx).mapNeighborSet q) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H p =>
    constructor
    · intro b c he
      obtain ⟨a, ha⟩ := (adj_coset_iff U t htx hty p b.val).mp b.property
      obtain ⟨d, hd⟩ := (adj_coset_iff U t htx hty p c.val).mp c.property
      have he' : (a : G) • U.y = (d : G) • U.y := by
        have h := congrArg Subtype.val he
        change project U b.val = project U c.val at h
        rw [ha, hd] at h
        simp only [project_coset, map_mul, canonical_vertex, canonical_local, mul_smul,
          htx] at h
        exact MulAction.injective (canonical U p) h
      apply Subtype.ext
      rw [ha, hd, coset_eq_iff]
      have hfix : ((a⁻¹ * d : U.vertexGroup) : G) • U.y = U.y := by
        change ((a : G)⁻¹ * (d : G)) • U.y = U.y
        rw [mul_smul, ← he', inv_smul_smul]
      have hm := conjugate_vertex_mem U t htx hty (a⁻¹ * d) hfix
      simpa only [map_mul, map_inv, mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hm
    · intro b
      have hb : U.graph.Adj U.x ((canonical U p)⁻¹ • b.val) := by
        have hh := U.preserves (canonical U p)⁻¹ b.property
        change U.graph.Adj ((canonical U p)⁻¹ • (canonical U p • U.x)) _ at hh
        simpa only [inv_smul_smul] using hh
      obtain ⟨g, h | h⟩ := U.edge_transitive _ _ hb
      · let a : U.vertexGroup := ⟨g, h.1⟩
        refine ⟨⟨coset U (p * vertex U a * localMap U t),
          (adj_coset_iff U t htx hty p _).mpr ⟨a, rfl⟩⟩, ?_⟩
        apply Subtype.ext
        change project U (coset U _) = b.val
        simp only [project_coset, map_mul, canonical_vertex, canonical_local, mul_smul, htx]
        exact (congrArg (fun z => canonical U p • z) h.2).trans (smul_inv_smul _ _)
      · let a : U.vertexGroup := ⟨g * t, by
          change (g * (t : G)) • U.x = U.x
          rw [mul_smul, htx, h.2]⟩
        refine ⟨⟨coset U (p * vertex U a * localMap U t),
          (adj_coset_iff U t htx hty p _).mpr ⟨a, rfl⟩⟩, ?_⟩
        apply Subtype.ext
        change project U (coset U _) = b.val
        simp only [project_coset, map_mul, canonical_vertex, canonical_local, mul_smul, htx]
        change canonical U p • ((g * (t : G)) • U.y) = b.val
        rw [mul_smul, hty, h.1, smul_inv_smul]

/-- The embedded vertex group and any local reversal generate the presentation. -/
theorem eq_top_of_vertex_swap (S : Subgroup U.PathPresentation)
    (hv : (vertex U).range ≤ S) (ht : localMap U t ∈ S) : S = ⊤ := by
  have he (g : U.edgeSetGroup) : edge U g ∈ S := by
    rcases U.edgeSetGroup_cases t htx hty g.property with hg | hg
    · have hi : vertex U ⟨g, hg.1⟩ = edge U g :=
        (inclusions U).vertex_edge g hg.1 g.property
      rw [← hi]
      exact hv ⟨_, rfl⟩
    · let b : U.edgeSetGroup := ⟨(g : G) * (t : G)⁻¹, Or.inl hg⟩
      let te : U.edgeSetGroup := ⟨t, Or.inr ⟨htx, hty⟩⟩
      have hi : vertex U ⟨b, hg.1⟩ = edge U b :=
        (inclusions U).vertex_edge b hg.1 b.property
      have hj : localMap U t = edge U te :=
        (inclusions U).local_edge t t.property te.property
      have hh : g = b * te := Subtype.ext (by simp [b, te])
      rw [hh, map_mul, ← hi, ← hj]
      exact S.mul_mem (hv ⟨_, rfl⟩) ht
  let D : Subgroup G := (S.comap (localMap U)).map U.H.subtype
  have hD : U.H ≤ D := by
    rw [← U.local_generate]
    apply sup_le
    · intro g hg
      refine ⟨⟨g, hg.1⟩, ?_, rfl⟩
      change localMap U ⟨g, hg.1⟩ ∈ S
      have hi : localMap U ⟨g, hg.1⟩ = edge U ⟨g, hg.2⟩ :=
        (inclusions U).local_edge g hg.1 hg.2
      rw [hi]
      exact he _
    · intro g hg
      refine ⟨⟨g, hg.1⟩, ?_, rfl⟩
      change localMap U ⟨g, hg.1⟩ ∈ S
      have hi : localMap U ⟨g, hg.1⟩ = vertex U ⟨g, hg.2⟩ :=
        (inclusions U).local_vertex g hg.1 hg.2
      rw [hi]
      exact hv ⟨_, rfl⟩
  have hh (h : U.H) : localMap U h ∈ S := by
    obtain ⟨k, hk, heq⟩ := hD h.property
    have hk' : k = h := Subtype.ext heq
    exact hk' ▸ hk
  apply top_unique
  rw [← generate U]
  exact sup_le (sup_le hv (by rintro _ ⟨g, rfl⟩; exact he g))
    (by rintro _ ⟨h, rfl⟩; exact hh h)

/-- Left translation as a graph homomorphism. -/
def translation (p : U.PathPresentation) : cosetGraph U t htx →g cosetGraph U t htx where
  toFun := (p • ·)
  map_rel' := cosetGraph_smul U t htx p

/-- The coset graph is connected using the defining local generation identities. -/
theorem cosetGraph_preconnected : (cosetGraph U t htx).Preconnected := by
  let Γ := cosetGraph U t htx
  have hmap (p a b : U.PathPresentation) (h : Γ.Reachable (coset U a) (coset U b)) :
      Γ.Reachable (coset U (p * a)) (coset U (p * b)) :=
    h.map (translation U t htx p)
  let R : Subgroup U.PathPresentation :=
    { carrier := {p | Γ.Reachable (coset U 1) (coset U p)}
      one_mem' := .refl _
      mul_mem' := by
        intro p q hp hq
        exact hp.trans (by simpa only [mul_one] using hmap p 1 q hq)
      inv_mem' := by
        intro p hp
        change Γ.Reachable (coset U 1) (coset U p⁻¹)
        simpa only [mul_one, inv_mul_cancel] using (hmap p⁻¹ 1 p hp).symm }
  have hv : (vertex U).range ≤ R := by
    rintro _ ⟨a, rfl⟩
    change Γ.Reachable (coset U 1) (coset U (vertex U a))
    have he : coset U (vertex U a) = coset U 1 := by
      simpa only [one_mul] using coset_mul_vertex U 1 a
    rw [he]
  have ht : localMap U t ∈ R := by
    exact (show Γ.Adj (coset U 1) (coset U (localMap U t)) by
      simpa only [one_mul] using cosetGraph_adj U t htx 1).reachable
  have hR := eq_top_of_vertex_swap U t htx hty R hv ht
  intro a b
  induction a using QuotientGroup.induction_on with
  | H p =>
    induction b using QuotientGroup.induction_on with
    | H q =>
      have hp : p ∈ R := by rw [hR]; trivial
      have hq : q ∈ R := by rw [hR]; trivial
      exact hp.symm.trans hq

end Theory.GroupTheory.GraphUniquenessSystem.System.PathPresentation

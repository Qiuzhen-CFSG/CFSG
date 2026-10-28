module
public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.Amalgam
public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.PathPresentation
import all Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.EdgeAmalgam

/-!
# Lifting local homomorphisms without a target uniqueness system

Vertex and local homomorphisms into an arbitrary group determine a map of
the genuine rank-three amalgam if they agree on their intersection and
respect conjugation by one local edge reversal. The setwise-edge group has
two cosets of its pointwise fixer. Agreement on the square of the reversal
supplies the remaining relation, so no target action or injectivity is needed.
The cycle-base theorem then gives a unique homomorphism on the acting group.

The private `import all` intentionally shares `EdgeAmalgam`'s internal
two-coset extension proof within this package. Its helper does not occur in
the public signatures or an exposed definition body.

Source: Aschbacher, *Sporadic Groups* (1994), 37.4--37.6; the direct lifting
form is used in Aschbacher--Smith F.5.7.
-/

public section
namespace Theory.GroupTheory.GraphUniquenessSystem.System
universe u v w
variable {K : Type u} {X : Type v} [Group K] [MulAction K X]
variable {G : Type w} [Group G]
variable (U : System K X)

private theorem edgeHom_of_local_conjugation
    (vertexHom : U.vertexGroup →* G) (localHom : U.H →* G)
    (agree : ∀ (g : K) (hgH : g ∈ U.H) (hgx : g ∈ U.vertexGroup),
      vertexHom ⟨g,hgx⟩ = localHom ⟨g,hgH⟩)
    (t : U.H) (htx : (t : K) • U.x = U.y) (hty : (t : K) • U.y = U.x)
    (hconj : ∀ b : U.edgeGroup,
      vertexHom ⟨(t : K) * b * (t : K)⁻¹,
        (U.conj_mem_edgeGroup htx hty b.property).1⟩ =
      localHom t * vertexHom ⟨b,b.property.1⟩ * (localHom t)⁻¹) :
    ∃ f : U.edgeSetGroup →* G,
      (∀ b : U.edgeGroup,
        f ⟨b,U.edgeGroup_le_edgeSetGroup b.property⟩ = vertexHom ⟨b,b.property.1⟩) ∧
      (∀ (h : U.H) (he : (h : K) ∈ U.edgeSetGroup),
        f ⟨h,he⟩ = localHom h) := by
  let B := U.edgeGroup.subgroupOf U.edgeSetGroup
  let t₀ : U.edgeSetGroup := ⟨t,Or.inr ⟨htx,hty⟩⟩
  let φ : B →* G := vertexHom.comp
    { toFun := fun b => ⟨b,b.property.1⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have ht : t₀ ∉ B := fun h => U.adjacent.ne (h.1.symm.trans htx)
  have htt : t₀ * t₀ ∈ B := by
    exact ⟨by change ((t : K) * t) • U.x = U.x; rw [mul_smul,htx,hty],
      by change ((t : K) * t) • U.y = U.y; rw [mul_smul,hty,htx]⟩
  have hc (b : B) : t₀ * b * t₀⁻¹ ∈ B :=
    U.conj_mem_edgeGroup htx hty b.property
  have hsq : φ ⟨t₀ * t₀,htt⟩ = localHom t * localHom t := by
    change vertexHom ⟨(t : K) * t,htt.1⟩ = _
    exact (agree _ (U.H.mul_mem t.property t.property) htt.1).trans
      (localHom.map_mul t t)
  have hconj' (b : B) : φ ⟨t₀ * b * t₀⁻¹,hc b⟩ =
      localHom t * φ b * (localHom t)⁻¹ := hconj ⟨b,b.property⟩
  obtain ⟨f,fb,ft⟩ := twoCosetHom B t₀ (localHom t) φ ht htt hc hsq hconj'
    (fun g => U.edgeSetGroup_cases t htx hty g.property)
  have fe (b : U.edgeGroup) : f ⟨b,U.edgeGroup_le_edgeSetGroup b.property⟩ =
      vertexHom ⟨b,b.property.1⟩ :=
    fb ⟨⟨b,U.edgeGroup_le_edgeSetGroup b.property⟩,b.property⟩
  refine ⟨f,fe,?_⟩
  intro h he
  rcases U.edgeSetGroup_cases t htx hty he with hb | hb
  · exact (fe ⟨h,hb⟩).trans (agree h h.property hb.1)
  · let b : U.edgeGroup := ⟨(h : K) * (t : K)⁻¹,hb⟩
    have hbH : (b : K) ∈ U.H := U.H.mul_mem h.property (U.H.inv_mem t.property)
    have heq : (⟨h,he⟩ : U.edgeSetGroup) =
        (⟨b,U.edgeGroup_le_edgeSetGroup b.property⟩ : U.edgeSetGroup) * t₀ := by
      apply Subtype.ext
      simp [b,t₀]
    rw [heq,map_mul,fe,agree b hbH]
    rw [ft]
    change localHom (h * t⁻¹) * localHom t = _
    simp

variable (vertexHom : U.vertexGroup →* G) (localHom : U.H →* G)
variable (agree : ∀ (g : K) (hgH : g ∈ U.H) (hgx : g ∈ U.vertexGroup),
  vertexHom ⟨g,hgx⟩ = localHom ⟨g,hgH⟩)
variable (t : U.H) (htx : (t : K) • U.x = U.y) (hty : (t : K) • U.y = U.x)
variable (hconj : ∀ b : U.edgeGroup,
  vertexHom ⟨(t : K) * b * (t : K)⁻¹,
    (U.conj_mem_edgeGroup htx hty b.property).1⟩ =
  localHom t * vertexHom ⟨b,b.property.1⟩ * (localHom t)⁻¹)

/-- Compatible vertex and local homomorphisms extend to the genuine rank-three
amalgam when they respect conjugation by one local edge reversal. -/
noncomputable def amalgamMapOfLocalConjugation : U.AmalgamMap G := by
  let h := edgeHom_of_local_conjugation U vertexHom localHom agree t htx hty hconj
  exact
    { vertexHom := vertexHom
      edgeHom := h.choose
      localHom := localHom
      vertex_edge := fun g hx he =>
        (h.choose_spec.1 ⟨g,U.mem_edgeGroup_of_vertex_of_edgeSet hx he⟩).symm
      local_vertex := fun g hH hx => (agree g hH hx).symm
      local_edge := fun g hH he => (h.choose_spec.2 ⟨g,hH⟩ he).symm }

@[simp] theorem amalgamMapOfLocalConjugation_vertexHom :
    (U.amalgamMapOfLocalConjugation vertexHom localHom agree t htx hty hconj).vertexHom =
      vertexHom := by rfl

@[simp] theorem amalgamMapOfLocalConjugation_localHom :
    (U.amalgamMapOfLocalConjugation vertexHom localHom agree t htx hty hconj).localHom =
      localHom := by rfl

include agree hconj in
/-- A cycle base lifts the two compatible homomorphisms directly into the
target group. No action or graph on the target is required. -/
theorem existsUnique_hom_of_local_conjugation (hb : U.IsBase) :
    ∃! f : K →* G,
      (∀ a : U.vertexGroup, f a = vertexHom a) ∧
      (∀ a : U.H, f a = localHom a) := by
  let m := U.amalgamMapOfLocalConjugation vertexHom localHom agree t htx hty hconj
  let f := m.liftOfBase hb
  have hv (a : U.vertexGroup) : f.hom a = vertexHom a := by
    simpa only [m,amalgamMapOfLocalConjugation_vertexHom] using f.onVertex a
  have hl (a : U.H) : f.hom a = localHom a := by
    simpa only [m,amalgamMapOfLocalConjugation_localHom] using f.onLocal a
  refine ⟨f.hom,⟨hv,hl⟩,?_⟩
  intro g hg
  apply U.hom_ext
  · intro a
    exact (hg.2 a).trans (hl a).symm
  · intro a
    exact (hg.1 a).trans (hv a).symm

end Theory.GroupTheory.GraphUniquenessSystem.System

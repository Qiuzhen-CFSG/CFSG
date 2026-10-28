module
public import Theory.GroupTheory.GraphUniquenessSystem
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Edge conjugation from a residual and the local intersection

Two compatible vertex and local homomorphisms respect conjugation by a local
edge reversal if they do so on the edge residual and the local intersection
supplements that residual. The two conjugation maps agree on the residual by
centralization, and on the local intersection by the local homomorphism law.
Their equality subgroup therefore contains the entire edge group.

This is the residual-generation step in Aschbacher--Smith F.5.7.
-/

public noncomputable section
namespace Theory.GroupTheory.GraphUniquenessSystem.System
open Subgroup
variable {K X G : Type*} [Group K] [MulAction K X] [Group G]
    (U : System K X)

theorem conjugation_of_residual_and_local
    (v : U.vertexGroup →* G) (l : U.H →* G)
    (agree : ∀ (g : K) (hgH : g ∈ U.H) (hgv : g ∈ U.vertexGroup),
      v ⟨g,hgv⟩ = l ⟨g,hgH⟩)
    (t : U.H) (htx : (t:K) • U.x=U.y) (hty : (t:K) • U.y=U.x)
    (gen : pResidual 2 U.edgeGroup ⊔ U.H.subgroupOf U.edgeGroup = ⊤)
    (model : ∀ b : U.edgeGroup, b∈pResidual 2 U.edgeGroup →
      (t:K)*b*(t:K)⁻¹=b)
    (source : ∀ b : U.edgeGroup, b∈pResidual 2 U.edgeGroup →
      l t * v ⟨b,b.property.1⟩ = v ⟨b,b.property.1⟩ * l t) :
    ∀ b : U.edgeGroup,
      v ⟨(t:K)*b*(t:K)⁻¹,(U.conj_mem_edgeGroup htx hty b.property).1⟩ =
        l t * v ⟨b,b.property.1⟩ * (l t)⁻¹ := by
  let f : U.edgeGroup →* G := v.comp
    { toFun b := ⟨(t:K)*b*(t:K)⁻¹,(U.conj_mem_edgeGroup htx hty b.property).1⟩
      map_one' := Subtype.ext (by simp)
      map_mul' a b := Subtype.ext (by simp [mul_assoc]) }
  let k : U.edgeGroup →* G := (MulAut.conj (l t)).toMonoidHom.comp
    (v.comp (Subgroup.inclusion (show U.edgeGroup≤U.vertexGroup from inf_le_left)))
  have heq : f.eqLocus k = ⊤ := by
    apply top_unique
    rw [←gen]
    apply sup_le
    · intro b hb
      change v ⟨(t:K)*b*(t:K)⁻¹,_⟩ = l t*v ⟨b,b.property.1⟩*(l t)⁻¹
      have he : (⟨(t:K)*b*(t:K)⁻¹,
          (U.conj_mem_edgeGroup htx hty b.property).1⟩ : U.vertexGroup) =
          ⟨b,b.property.1⟩ := Subtype.ext (model b hb)
      rw [he,source b hb,mul_inv_cancel_right]
    · intro b hb
      have hcH : (t:K)*b*(t:K)⁻¹∈U.H := U.H.mul_mem
        (U.H.mul_mem t.property hb) (U.H.inv_mem t.property)
      change v ⟨(t:K)*b*(t:K)⁻¹,_⟩ = l t*v ⟨b,b.property.1⟩*(l t)⁻¹
      rw [agree _ hcH,agree b hb]
      exact l.map_mul (t*⟨b,hb⟩) t⁻¹ |>.trans (by rw [map_mul,map_inv])
  intro b
  exact heq.ge (mem_top b)

end Theory.GroupTheory.GraphUniquenessSystem.System

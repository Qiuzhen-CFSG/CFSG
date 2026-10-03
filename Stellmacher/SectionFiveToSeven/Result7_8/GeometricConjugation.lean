module
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricExtraction

/-!
# Conjugation of an actual geometric extraction

Transport every field of a supplied geometric extraction along the graph
actor g. The vertices become Γ.act g d and Γ.act g l, while the subgroups
and prescribed actor are conjugated by g⁻¹, as required by the graph's
right-action convention. The transported conjugator is exactly g⁻¹*x*g,
and its extracted vertex is Γ.act g of the original extracted vertex.
Both equations are retained in the theorem's conclusion.

Stabilizer and core equivariance transport containment and the geometric
coatom identity. Residual functoriality transports the conjugator's membership
in O²(E). Injective maps preserve the coatom cardinality, intersections,
commutators, and generation. For the outside-actor generation field, lift
the supplied conjugate actor back through the automorphism and map the
original closure equality. Graph action associativity identifies the new
extracted vertex, so adjacency transports to the same concrete witness.

This is the conjugation used to normalize the second extracted neighbor
in Stellmacher (9.3), Journal of Algebra 190 (1997), p.49. Source:
`refs/files/stellmacher-n-group.pdf`. The generic (7.8) extraction retains
its established SectionNine data namespace. No new geometry assumptions
or assertion about all Sylow subgroups is introduced.
-/
namespace Stellmacher.SectionsFiveToSeven
open CosetGraphContext SevenSix Stellmacher.SectionNine
universe u

private theorem map_conjugate_subgroup
    {G H : Type*} [Group G] [Group H] (f : G →* H) (A : Subgroup G) (x : G) :
    (A.conjBy x).map f = (A.map f).conjBy (f x) := by
  simp only [Subgroup.conjBy,Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply]

public theorem geometric_extraction_conjugation
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (d l : Γ.Vertex)
    (A E A0 : Subgroup G) (actor : G)
    (data : NineThreeGeometricData Γ d l A E A0 actor) (g : G) :
    ∃ newdata : NineThreeGeometricData Γ (Γ.act g d) (Γ.act g l)
      (A.map (MulAut.conj g⁻¹).toMonoidHom)
      (E.map (MulAut.conj g⁻¹).toMonoidHom)
      (A0.map (MulAut.conj g⁻¹).toMonoidHom) ((MulAut.conj g⁻¹) actor),
      newdata.x = (MulAut.conj g⁻¹) data.x ∧
      Γ.act newdata.x⁻¹ (Γ.act g l) = Γ.act g (Γ.act data.x⁻¹ l) := by
  let c := MulAut.conj g⁻¹
  let x := c data.x
  let m := Γ.act data.x⁻¹ l
  have hvertex : Γ.act x⁻¹ (Γ.act g l) = Γ.act g m := by
    change Γ.act x⁻¹ (Γ.act g l) = Γ.act g (Γ.act data.x⁻¹ l)
    rw [← Γ.act_mul,← Γ.act_mul]
    congr 1
    simp [x,c,MulAut.conj_apply,mul_assoc]
  have hG (v : Γ.Vertex) : (stabilizer Γ v).map c.toMonoidHom = stabilizer Γ (Γ.act g v) := by
    rw [stabilizer_act]
    rfl
  have hQ (v : Γ.Vertex) : (q Γ v).map c.toMonoidHom = q Γ (Γ.act g v) := by
    rw [q_act]
  have hGm : (stabilizer Γ m).map c.toMonoidHom =
      stabilizer Γ (Γ.act x⁻¹ (Γ.act g l)) := by rw [hvertex]; exact hG m
  have hQm : (q Γ m).map c.toMonoidHom = q Γ (Γ.act x⁻¹ (Γ.act g l)) := by
    rw [hvertex]
    exact hQ m
  have hAconj : (A.conjBy data.x).map c.toMonoidHom =
      (A.map c.toMonoidHom).conjBy x := map_conjugate_subgroup c.toMonoidHom A data.x
  have hRmap : (twoResidualAmbient E).map c.toMonoidHom =
      twoResidualAmbient (E.map c.toMonoidHom) :=
    map_twoResidualAmbient_of_subgroup_image E c.toMonoidHom (E.map c.toMonoidHom) rfl
  have hxR : x ∈ twoResidualAmbient (E.map c.toMonoidHom) := by
    rw [← hRmap]
    exact Subgroup.mem_map_of_mem c.toMonoidHom data.residual_mem
  have hE : E.map c.toMonoidHom ≤ stabilizer Γ (Γ.act g d) := by
    rw [← hG d]
    exact Subgroup.map_mono data.group_le
  have hgen : E.map c.toMonoidHom = A.map c.toMonoidHom ⊔
      (A.map c.toMonoidHom).conjBy x := by
    rw [data.generated,Subgroup.map_sup,hAconj]
  have hneighbor : Γ.act x⁻¹ (Γ.act g l) ∈ neighborhood Γ (Γ.act g d) := by
    rw [hvertex]
    apply (mem_neighborhood_iff_adjacent Γ).mpr
    exact adjacent_act Γ g ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor)
  have houtside : c actor ∉ stabilizer Γ (Γ.act x⁻¹ (Γ.act g l)) := by
    rw [← hGm]
    intro ha
    obtain ⟨a,ha,he⟩ := ha
    have heq : a = actor := c.injective he
    exact data.actor_outside (heq ▸ ha)
  have h0 : A0.map c.toMonoidHom = A.map c.toMonoidHom ⊓
      stabilizer Γ (Γ.act x⁻¹ (Γ.act g l)) := by
    rw [data.coatom_eq,Subgroup.map_inf _ _ _ c.injective,hGm]
  have hcard : Nat.card (A.map c.toMonoidHom) = 2 * Nat.card (A0.map c.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective c.injective,Subgroup.card_map_of_injective c.injective]
    exact data.coatom_card
  have hAcore : (A.map c.toMonoidHom).conjBy x ≤ q Γ (Γ.act x⁻¹ (Γ.act g l)) := by
    rw [← hAconj,← hQm]
    exact Subgroup.map_mono data.conjugate_core_le
  have hedge : E.map c.toMonoidHom ⊔ (stabilizer Γ (Γ.act g d) ⊓
      stabilizer Γ (Γ.act x⁻¹ (Γ.act g l))) = stabilizer Γ (Γ.act g d) := by
    rw [← hG d,← hGm,← Subgroup.map_inf _ _ _ c.injective,← Subgroup.map_sup,
      data.edge_generated]
  have hcomm : ⁅E.map c.toMonoidHom,A0.map c.toMonoidHom⁆ ≤ q Γ (Γ.act g d) := by
    rw [← Subgroup.map_commutator,← hQ d]
    exact Subgroup.map_mono data.coatom_commutator
  have hby (b : G) (hb : b ∈ A.map c.toMonoidHom)
      (hbn : b ∉ stabilizer Γ (Γ.act x⁻¹ (Γ.act g l))) :
      E.map c.toMonoidHom = Subgroup.closure ({b} : Set G) ⊔
        (A.map c.toMonoidHom).conjBy x := by
    obtain ⟨a,ha,rfl⟩ := hb
    have han : a ∉ stabilizer Γ m := by
      intro ham
      apply hbn
      rw [← hGm]
      exact Subgroup.mem_map_of_mem c.toMonoidHom ham
    have hh := congrArg (Subgroup.map c.toMonoidHom) (data.actor_generated a ha han)
    rw [Subgroup.map_sup,hAconj,MonoidHom.map_closure,Set.image_singleton] at hh
    exact hh
  refine ⟨⟨x,hxR,hE,hgen,hneighbor,houtside,h0,hcard,hAcore,hedge,hby,hcomm⟩,rfl,?_⟩
  exact hvertex
end Stellmacher.SectionsFiveToSeven

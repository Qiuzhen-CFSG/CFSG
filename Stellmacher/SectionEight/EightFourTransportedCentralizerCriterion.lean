module
public import Stellmacher.SectionEight.EightFourLocalContext
public import Stellmacher.SectionEight.EightFourCentralizerCriterion
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The (6.4) vector criterion along the actual edge orbit

The offender fixed subgroup at the initial edge extends to an equivariant
family. A vector in any transported member lies in the next vertex center
whenever its centralizer generates that vertex stabilizer with the full edge.
The exact original quotient-module witness is retained throughout. The local
context supplies the initial vector criterion on the same graph; canonical
wrappers retain the original ambient-context API.

Pull the vector back by the supplied conjugator. Conjugation preserves
stabilizers, intersections, joins, and element centralizers, so the initial
criterion applies. Transport its conclusion using covariance of vertex
centers. For arbitrary vertex pairs, the defining join formula either supplies
an edge transporter or makes the family member trivial.

This is the equivariant vector-centralizer implication used in Stellmacher
(8.4), Journal of Algebra 190 (1997), printed p.39. It transports the proved
initial-edge criterion without constructing a new quotient action or witness.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem map_singleton_centralizer
    {G : Type*} [Group G] (e : G ≃* G) (v : G) :
    (Subgroup.centralizer ({v} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e v} : Set G) := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hm := congrArg e h
    simpa only [map_mul, e.apply_symm_apply] using hm
  · intro h
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using h

/-- The initial vector criterion transports along the supplied graph actor. -/
public theorem eight_four_transported_vector_centralizer_criterion_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : EightFourLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (g v : H)
    (hv : v ∈ F (ctx.Γ.act g ctx.criticalPath.a)
      (ctx.Γ.act g ctx.criticalPath.firstStep))
    (hgen : (GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) ⊓
      Subgroup.centralizer ({v} : Set H)) ⊔
      (GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.a) ⊓
        GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)) =
      GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)) :
    v ∈ ZAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) := by
  let e : H ≃* H := MulAut.conj g⁻¹
  rw [hcov, hbase] at hv
  obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
  have hG (d : ctx.Γ.Vertex) :
      GAt ctx.Γ (ctx.Γ.act g d) = (GAt ctx.Γ d).map e.toMonoidHom :=
    stabilizer_act ctx.Γ g d
  have hZ (d : ctx.Γ.Vertex) :
      ZAt ctx.Γ (ctx.Γ.act g d) = (ZAt ctx.Γ d).map e.toMonoidHom :=
    z_act ctx.Γ g d
  have hgen₀ : (GAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer ({v₀} : Set H)) ⊔
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
        GAt ctx.Γ ctx.criticalPath.firstStep := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simp only [Subgroup.map_sup, Subgroup.map_inf _ _ e.toMonoidHom e.injective,
      map_singleton_centralizer]
    simpa only [hG, e, MulEquiv.coe_toMonoidHom] using hgen
  rw [hZ]
  exact Subgroup.mem_map.mpr ⟨v₀,
    eight_four_vector_centralizer_criterion_local ctx hcenter w v₀ hv₀ hgen₀, rfl⟩

/-- The vector criterion holds on every member of the actual equivariant edge family. -/
public theorem eight_four_edge_vector_centralizer_criterion_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : EightFourLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (d l : ctx.Γ.Vertex) (v : H) (hv : v ∈ F d l)
    (hgen : (GAt ctx.Γ l ⊓ Subgroup.centralizer ({v} : Set H)) ⊔
      (GAt ctx.Γ d ⊓ GAt ctx.Γ l) = GAt ctx.Γ l) :
    v ∈ ZAt ctx.Γ l := by
  by_cases hactor : ∃ g : H, ctx.Γ.act g ctx.criticalPath.a = d ∧
      ctx.Γ.act g ctx.criticalPath.firstStep = l
  · obtain ⟨g, rfl, rfl⟩ := hactor
    exact eight_four_transported_vector_centralizer_criterion_local
      ctx hcenter w F hbase hcov g v hv hgen
  · have hFbot : F d l = ⊥ := by
      rw [hformula]
      apply bot_unique
      apply iSup_le
      intro g
      apply iSup_le
      intro hg
      exact (hactor ⟨g, hg⟩).elim
    have hvone : v = 1 := by simpa only [hFbot, Subgroup.mem_bot] using hv
    rw [hvone]
    exact Subgroup.one_mem _

/-- Canonical-context wrapper for transport along a supplied graph actor. -/
public theorem eight_four_transported_vector_centralizer_criterion
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (g v : H)
    (hv : v ∈ F (ctx.Γ.act g ctx.criticalPath.a)
      (ctx.Γ.act g ctx.criticalPath.firstStep))
    (hgen : (GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) ⊓
      Subgroup.centralizer ({v} : Set H)) ⊔
      (GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.a) ⊓
        GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)) =
      GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)) :
    v ∈ ZAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) := by
  exact eight_four_transported_vector_centralizer_criterion_local
    ctx.toEightFourContext hcenter w F hbase hcov g v hv hgen

/-- Canonical-context wrapper for every member of the equivariant edge family. -/
public theorem eight_four_edge_vector_centralizer_criterion
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (d l : ctx.Γ.Vertex) (v : H) (hv : v ∈ F d l)
    (hgen : (GAt ctx.Γ l ⊓ Subgroup.centralizer ({v} : Set H)) ⊔
      (GAt ctx.Γ d ⊓ GAt ctx.Γ l) = GAt ctx.Γ l) :
    v ∈ ZAt ctx.Γ l := by
  exact eight_four_edge_vector_centralizer_criterion_local
    ctx.toEightFourContext hcenter w F hbase hcov hformula d l v hv hgen

end Stellmacher.SectionEight

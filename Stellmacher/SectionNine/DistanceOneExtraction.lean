module

public import Stellmacher.SectionFiveToSeven.Result7_8.InvolutionConfiguration
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionNine.GeneratedContext

/-!
# Distance-one extraction and product intersections

For an ambient-retaining Section Nine context with critical length one,
the proved elementary-actor configuration supplies one conjugator, its
index-two actor coatom, the generated group, the dihedral quotient, swapping
involutions, and the residual commutator relation. The record retains all
these witnesses together. The conjugate vertex is `Gamma.act x⁻¹ cp.a`:
`conjugateBy A x` is left conjugation, whereas the graph uses a right action.
The intersection of the two elementary vertex centers is central in their join.

The cross intersections of the vertex centers and stabilizers normalize one
another, so their join is the source product V. Its intersection with the
first vertex center is C. For an actor outside the extracted coatom, write
an element of its centralizer in V as a product from the two factors. Its
second factor centralizes the actor and the second elementary center, hence
the generated group. The self-containing conjugator then puts this factor
in the first center as well. Thus the actor centralizer in V is C. Since
the first two-core centralizes its vertex center, this also gives V ∩ Q = C.

Source: Stellmacher (9.1), journal p.46, initial extraction and the product
and centralizer reductions in (1)--(2). The coatom in this record is still
the intersection with O₂(E), not an assumed intersection with the next
stabilizer. Identifying those intersections and proving the remaining
relations through (4) are separate obligations for the local-geometry assembly.
-/

namespace Stellmacher.SectionNine

open Stellmacher.SectionsFiveToSeven CosetGraphContext Stellmacher.Later
open scoped Pointwise

universe u

public structure DistanceOneExtractionData
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) where
  x : G
  coatom : Subgroup G
  E : Subgroup G
  E_le : E ≤ stabilizer ctx.Γ ctx.criticalPath.a'
  x_mem : x ∈ stabilizer ctx.Γ ctx.criticalPath.a'
  generated : E = z ctx.Γ ctx.criticalPath.a ⊔
    z ctx.Γ (ctx.Γ.act x⁻¹ ctx.criticalPath.a)
  coatom_card : Nat.card (z ctx.Γ ctx.criticalPath.a) = 2 * Nat.card coatom
  x_mem_E : x ∈ E
  x_sq_mem : x ^ 2 ∈ q ctx.Γ ctx.criticalPath.a'
  coatom_eq : coatom = z ctx.Γ ctx.criticalPath.a ⊓ twoCoreIn E
  edge_generated : E ⊔ (stabilizer ctx.Γ ctx.criticalPath.a ⊓
    stabilizer ctx.Γ ctx.criticalPath.a') = stabilizer ctx.Γ ctx.criticalPath.a'
  quotient : Nonempty (QuotientDihedralProduct E (q ctx.Γ ctx.criticalPath.a') coatom)
  swapping : ∀ first second : Subgroup G,
    first ∈ conjugateSubgroupOrbit (z ctx.Γ ctx.criticalPath.a) E →
    second ∈ conjugateSubgroupOrbit (z ctx.Γ ctx.criticalPath.a) E →
    ∃ actor : E, _root_.IsInvolution (actor : G) ∧
      first.conjBy (actor : G) = second ∧ second.conjBy (actor : G) = first
  actor_generated : ∀ actor : G, actor ∈ z ctx.Γ ctx.criticalPath.a → actor ∉ coatom →
    E = Subgroup.closure ({actor} : Set G) ⊔
      z ctx.Γ (ctx.Γ.act x⁻¹ ctx.criticalPath.a)
  residual_commutator : twoResidualIn E ≤ ⁅twoResidualIn E, q ctx.Γ ctx.criticalPath.a⁆
  intersection_central : z ctx.Γ ctx.criticalPath.a ⊓
    z ctx.Γ (ctx.Γ.act x⁻¹ ctx.criticalPath.a) ≤ (Subgroup.center E).map E.subtype

private theorem intersection_le_center_join
    {G : Type*} [Group G] (first second : Subgroup G)
    [IsMulCommutative first] [IsMulCommutative second] :
    first ⊓ second ≤ (Subgroup.center (first ⊔ second : Subgroup G)).map
      (first ⊔ second).subtype := by
  have hcentral : first ⊔ second ≤ Subgroup.centralizer (first ⊓ second : Set G) :=
    sup_le
      ((Subgroup.le_centralizer first).trans (Subgroup.centralizer_le inf_le_left))
      ((Subgroup.le_centralizer second).trans (Subgroup.centralizer_le inf_le_right))
  intro element helement
  refine ⟨⟨element, (show first ≤ first ⊔ second from le_sup_left) helement.1⟩, ?_, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro other
  exact Subtype.ext ((hcentral other.property element helement).symm)

public theorem distance_one_extraction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) :
    Nonempty (DistanceOneExtractionData ctx) := by
  let Gamma := ctx.Γ
  let cp := ctx.criticalPath
  have hforward : cp.a' ∈ neighborhood Gamma cp.a := by
    rw [neighborhood, Gamma.neighbors_def]
    exact (Gamma.distance_symm cp.a' cp.a).trans (cp.endpoint_distance.trans hb)
  have hbackward : cp.a ∈ neighborhood Gamma cp.a' := by
    rw [neighborhood, Gamma.neighbors_def]
    exact cp.endpoint_distance.trans hb
  let _ : IsElementaryAbelian 2 (z Gamma cp.a) :=
    SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven Gamma hforward
  let _ : Fact (IsPGroup 2 (z Gamma cp.a)) :=
    ⟨IsElementaryAbelian.isPGroup 2 (z Gamma cp.a)⟩
  have hA : z Gamma cp.a ≤ q Gamma cp.a :=
    ((lemma_seven_three ctx.sectionSeven Gamma).center_core cp.a cp.a' hforward).trans
      ((Subgroup.map_mono (Subgroup.map_subtype_le _)).trans
        (Subgroup.map_subtype_le _))
  have hPhi : frattiniAmbient (z Gamma cp.a) ≤ q Gamma cp.a' := by
    simp only [frattiniAmbient,
      frattini_eq_bot_of_isElementaryAbelian (R := z Gamma cp.a) (p := 2),
      Subgroup.map_bot, bot_le]
  have hAexp : ∀ actor : G, actor ∈ z Gamma cp.a → actor ^ 2 = 1 := by
    intro actor hactor
    exact elemPow_eq_one_of_isElementaryAbelian actor hactor
  obtain ⟨x, A₀, E, hE, hx, _, hgen, hcard, hxE, hxsq, hA₀,
      hedge, hquot, hswap, hall, hres⟩ :=
    sevenEight_involution_configuration_of_actor_exponent_two ctx.sectionSeven Gamma
      cp.a' cp.a hbackward (z Gamma cp.a) hA cp.critical.2 hPhi hAexp
  have hnext : z Gamma (Gamma.act x⁻¹ cp.a) = conjugateBy (z Gamma cp.a) x := by
    simp only [z_act, inv_inv, conjugateBy]
  refine ⟨⟨x, A₀, E, hE, hx, ?_, hcard, hxE, hxsq, hA₀, hedge, hquot, hswap, ?_, hres, ?_⟩⟩
  · exact hgen.trans (congrArg (z Gamma cp.a ⊔ ·) hnext.symm)
  · intro actor hactor houtside
    exact (hall actor hactor houtside).trans
      (congrArg (Subgroup.closure ({actor} : Set G) ⊔ ·) hnext.symm)
  · change z Gamma cp.a ⊓ z Gamma (Gamma.act x⁻¹ cp.a) ≤ _
    rw [hnext, hgen]
    exact intersection_le_center_join (z Gamma cp.a)
      ((z Gamma cp.a).map (MulAut.conj x).toMonoidHom)

private theorem vertex_center_le_stabilizer
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Gamma : CosetGraphContext G T A B) (vertex : Gamma.Vertex) :
    z Gamma vertex ≤ stabilizer Gamma vertex := by
  rw [z, Gamma.zAt_def]
  apply sSup_le
  rintro center ⟨sylow, rfl⟩
  exact (SevenSix.omegaOneCenter_le_centerAmbient _).trans
    ((Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _))

public theorem distance_one_product_factors
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Gamma : CosetGraphContext G T A B) (alpha next : Gamma.Vertex) :
    let C := z Gamma alpha ⊓ stabilizer Gamma next
    let D := z Gamma next ⊓ stabilizer Gamma alpha
    C ≤ Subgroup.normalizer (D : Set G) ∧
    D ≤ Subgroup.normalizer (C : Set G) ∧
    C ⊔ D ≤ stabilizer Gamma alpha ⊓ stabilizer Gamma next ∧
    (C ⊔ D) ⊓ z Gamma alpha = C ∧
    C ⊓ D = z Gamma alpha ⊓ z Gamma next := by
  dsimp only
  have hfirst := vertex_center_le_stabilizer Gamma alpha
  have hsecond := vertex_center_le_stabilizer Gamma next
  have hjoin : (z Gamma alpha ⊓ stabilizer Gamma next) ⊔
      (z Gamma next ⊓ stabilizer Gamma alpha) ≤
        stabilizer Gamma alpha ⊓ stabilizer Gamma next :=
    sup_le (le_inf (inf_le_left.trans hfirst) inf_le_right)
      (le_inf inf_le_right (inf_le_left.trans hsecond))
  refine ⟨?_, ?_, hjoin, ?_, ?_⟩
  · exact (le_inf (inf_le_right.trans (stabilizer_le_normalizer_z Gamma next))
      (inf_le_left.trans (hfirst.trans Subgroup.le_normalizer))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  · exact (le_inf (inf_le_right.trans (stabilizer_le_normalizer_z Gamma alpha))
      (inf_le_left.trans (hsecond.trans Subgroup.le_normalizer))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  · exact le_antisymm (le_inf inf_le_right (inf_le_left.trans (hjoin.trans inf_le_right)))
      (le_inf le_sup_left inf_le_left)
  · exact le_antisymm (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left))
      (le_inf (le_inf inf_le_left (inf_le_right.trans hsecond))
        (le_inf inf_le_right (inf_le_left.trans hfirst)))

private theorem centralizer_product_actor
    {G : Type u} [Group G] (first second left right E : Subgroup G)
    [IsMulCommutative first] [IsMulCommutative second]
    (hleft : left ≤ first) (hright : right ≤ second)
    (hnormalize : left ≤ Subgroup.normalizer (right : Set G))
    (x actor : G) (hx : x ∈ E)
    (hsecond : second = first.map (MulAut.conj x).toMonoidHom)
    (hactor : actor ∈ first)
    (hgen : E = Subgroup.closure ({actor} : Set G) ⊔ second)
    (hintersection : (left ⊔ right) ⊓ first = left) :
    (left ⊔ right) ⊓ Subgroup.centralizer ({actor} : Set G) = left := by
  have hleftcentral : left ≤ Subgroup.centralizer ({actor} : Set G) :=
    hleft.trans ((Subgroup.le_centralizer first).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hactor)))
  apply le_antisymm ?_ (le_inf le_sup_left hleftcentral)
  intro element helement
  have hproduct := Subgroup.coe_mul_of_left_le_normalizer_right left right hnormalize
  obtain ⟨leftElement, hleftElement, rightElement, hrightElement, rfl⟩ :=
    show element ∈ (left : Set G) * (right : Set G) from hproduct ▸ helement.1
  have hrightcentral : rightElement ∈ Subgroup.centralizer ({actor} : Set G) := by
    have := (Subgroup.centralizer ({actor} : Set G)).mul_mem
      ((Subgroup.centralizer ({actor} : Set G)).inv_mem (hleftcentral hleftElement))
      helement.2
    simpa only [inv_mul_cancel_left] using this
  have hEcentral : E ≤ Subgroup.centralizer ({rightElement} : Set G) := by
    rw [hgen]
    apply sup_le
    · apply (Subgroup.closure_le _).mpr
      rw [Set.singleton_subset_iff]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hrightcentral).symm
    · exact (Subgroup.le_centralizer second).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (hright hrightElement)))
  have hrightfirst : rightElement ∈ first := by
    obtain ⟨original, horiginal, heq⟩ := hsecond ▸ hright hrightElement
    have hxcomm := Subgroup.mem_centralizer_singleton_iff.mp (hEcentral hx)
    have horiginalEq : original = rightElement := by
      have hconj : x * original * x⁻¹ = rightElement := heq
      calc
        original = x⁻¹ * (x * original * x⁻¹) * x := by group
        _ = x⁻¹ * rightElement * x := by rw [hconj]
        _ = rightElement := by rw [mul_assoc, ← hxcomm]; simp
    exact horiginalEq ▸ horiginal
  exact hintersection ▸ ⟨helement.1, first.mul_mem (hleft hleftElement) hrightfirst⟩

public theorem distance_one_extracted_centralizer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneExtractionData ctx)
    (actor : G) (hactor : actor ∈ z ctx.Γ ctx.criticalPath.a)
    (houtside : actor ∉ data.coatom) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let C := z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next
    let D := z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a
    (C ⊔ D) ⊓ Subgroup.centralizer ({actor} : Set G) = C := by
  have hneighbor : ctx.criticalPath.a' ∈ neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [neighborhood, ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hb)
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hneighbor
  have hnext : z ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) =
      (z ctx.Γ ctx.criticalPath.a).map (MulAut.conj data.x).toMonoidHom := by
    rw [z_act, inv_inv]
  let _ : IsMulCommutative (z ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a)) := by
    rw [hnext]
    infer_instance
  have hproduct := distance_one_product_factors ctx.Γ ctx.criticalPath.a
    (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a)
  exact centralizer_product_actor _ _ _ _ data.E inf_le_left inf_le_left hproduct.1
    data.x actor data.x_mem_E hnext hactor (data.actor_generated actor hactor houtside)
    hproduct.2.2.2.1

public theorem distance_one_extracted_core_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneExtractionData ctx) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let C := z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next
    let D := z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a
    (C ⊔ D) ⊓ q ctx.Γ ctx.criticalPath.a = C := by
  have hneighbor : ctx.criticalPath.a' ∈ neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [neighborhood, ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hb)
  have hcenter := ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core
    ctx.criticalPath.a ctx.criticalPath.a' hneighbor).trans
      (SevenSix.omegaOneCenter_le_centerAmbient _)
  have hcore := hcenter.trans (Subgroup.map_subtype_le _)
  have hcentral := Subgroup.le_centralizer_iff.mp
    (hcenter.trans (SevenSix.centerAmbient_le_centralizer _))
  have hnot : ¬ z ctx.Γ ctx.criticalPath.a ≤ data.coatom := by
    intro hle
    have heq := le_antisymm hle (data.coatom_eq ▸ inf_le_left)
    have hcard := data.coatom_card
    rw [heq] at hcard
    have hpos : 0 < Nat.card data.coatom := Nat.card_pos
    omega
  obtain ⟨actor, hactor, houtside⟩ := SetLike.not_le_iff_exists.mp hnot
  have hfixed := distance_one_extracted_centralizer ctx hb data actor hactor houtside
  apply le_antisymm ?_ (le_inf le_sup_left (inf_le_left.trans hcore))
  exact (inf_le_inf_left _ (hcentral.trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hactor)))).trans hfixed.le


end Stellmacher.SectionNine

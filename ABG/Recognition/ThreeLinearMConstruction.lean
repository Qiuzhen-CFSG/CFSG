module

public import ABG.Recognition.ThreeLinearCentralizerFixedSpaces
public import Theory.SpecificGroups.GL2.ThreeBorelGenerators
public import Theory.GroupTheory.ThreeCentralizerSylow
public import Theory.GroupTheory.SpecificGroups.DihedralThreeSquareConstruction

/-!
# Wong's order-thirty-six overgroup of the shared Borel

Transport the upper unipotent and diagonal reflection through the supplied
GL₂(3) equivalence. Together with the distinguished involution they generate
exactly the shared Borel subgroup. The two commuting involutions have no
common nonidentity fixed element of cube one.

The unique Sylow-three subgroup of the unipotent centralizer is normalized
by both involutions. Inside this nonabelian group of order 27, the fixed
subgroup of the reflection supplies a second rotation, inverted by the
distinguished involution. The two commuting dihedral factors give an actual
dihedral-square overgroup of the specified shared subgroup.
Source: Wong (1964), Appendix (b), pp.109–110.
-/

namespace ABG.ThreeLinearLocalData
open Matrix Matrix.GeneralLinearGroup
noncomputable section

variable {G : Type*} [Group G] [Finite G] (c : ThreeLinearLocalData G)

/-- Wong's second involution, the transported diagonal reflection. -/
@[expose] public def borelReflection : G := c.centralizerEmbedding threeReflection

/-- Wong's element `ρ`, in the prescribed centralizer coordinates. -/
@[expose] public def borelUnipotent : G := c.centralizerEmbedding threeUnipotent

public theorem centralizerEmbedding_threeCentral :
    c.centralizerEmbedding threeCentral = c.involution := by
  have h := threeCentralizerEquiv_involution c.involution c.order_involution c.centralizerEquiv
  have h' := congrArg (threeCentralizerEquiv c.involution c.centralizerEquiv).symm h
  exact (congrArg Subtype.val (by simpa using h')).symm

public theorem borelUnipotent_eq_linearUnipotent :
    c.borelUnipotent = (c.toThreeGlobalDegreeData.linearUnipotent : G) := by
  rw [c.toThreeGlobalDegreeData.linearUnipotent_eq]
  rfl

public theorem borelUnipotent_order : orderOf c.borelUnipotent = 3 := by
  rw [c.borelUnipotent_eq_linearUnipotent]
  exact c.toThreeGlobalDegreeData.linearUnipotent_order

public theorem borelReflection_order : orderOf c.borelReflection = 2 := by
  change orderOf (c.centralizerEmbedding threeReflection) = 2
  rw [orderOf_injective _ c.centralizerEmbedding_injective]
  exact three_conjugacy_data.2.1 5

public theorem involution_commute_borelReflection : Commute c.involution c.borelReflection := by
  rw [← c.centralizerEmbedding_threeCentral]
  exact threeCentral_commute_reflection.map c.centralizerEmbedding

public theorem involution_commute_borelUnipotent : Commute c.involution c.borelUnipotent := by
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    ((threeCentralizerEquiv c.involution c.centralizerEquiv).symm threeUnipotent).property).symm

public theorem borelReflection_inverts_unipotent :
    c.borelReflection * c.borelUnipotent * c.borelReflection⁻¹ = c.borelUnipotent⁻¹ := by
  simpa only [borelReflection, borelUnipotent, map_mul, map_inv] using
    congrArg c.centralizerEmbedding threeReflection_inverts_unipotent

/-- The generated subgroup is the exact transported upper-triangular subgroup. -/
public theorem sharedSubgroup_eq_closure : c.sharedSubgroup =
    Subgroup.closure ({c.involution, c.borelReflection, c.borelUnipotent} : Set G) := by
  rw [sharedSubgroup, three_borel_eq_closure, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, c.centralizerEmbedding_threeCentral,
    borelReflection, borelUnipotent]

/-- No nontrivial cubic element can commute with both specified involutions. -/
public theorem borel_pair_cubic_fixed_free (x : G) (hx : x ^ 3 = 1)
    (ht : Commute c.involution x) (hm : Commute c.borelReflection x) : x = 1 := by
  let xC : Subgroup.centralizer ({c.involution} : Set G) :=
    ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr ht.symm.eq⟩
  let y := threeCentralizerEquiv c.involution c.centralizerEquiv xC
  have hy : c.centralizerEmbedding y = x := by
    simp [y, centralizerEmbedding, xC]
  have hy3 : y ^ 3 = 1 := by
    apply c.centralizerEmbedding_injective
    simpa only [map_pow, map_one, hy] using hx
  have hym : Commute threeReflection y := by
    apply c.centralizerEmbedding_injective
    simpa only [map_mul, hy, borelReflection] using hm.eq
  have h1 := threeReflection_cubic_centralizer y hy3 hym
  rw [← hy, h1, map_one]

public theorem borelUnipotent_centralizer_card :
    Nat.card (Subgroup.centralizer ({c.borelUnipotent} : Set G)) = 54 := by
  rw [c.borelUnipotent_eq_linearUnipotent]
  exact c.three_class_census.choose_spec.2.2.2.2.1

/-- Both specified involutions preserve the cyclic unipotent subgroup. -/
public theorem borel_involutions_mem_unipotent_normalizer :
    c.involution ∈ Subgroup.normalizer (Subgroup.zpowers c.borelUnipotent : Set G) ∧
    c.borelReflection ∈ Subgroup.normalizer (Subgroup.zpowers c.borelUnipotent : Set G) := by
  constructor
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (c.involution * c.borelUnipotent * c.involution⁻¹) = _
    rw [c.involution_commute_borelUnipotent.eq, mul_assoc, mul_inv_cancel, mul_one]
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (c.borelReflection * c.borelUnipotent * c.borelReflection⁻¹) = _
    rw [c.borelReflection_inverts_unipotent, Subgroup.zpowers_inv]

/-- The second involution has the same actual GL₂(3) centralizer order. -/
public theorem borelReflection_centralizer_card
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1) :
    Nat.card (Subgroup.centralizer ({c.borelReflection} : Set G)) = 48 := by
  calc
    _ = Nat.card (GL (Fin 2) (ZMod 3)) :=
      Nat.card_congr (threeCentralizerEquiv c.borelReflection
        (hC c.borelReflection c.borelReflection_order)).toEquiv
    _ = 48 := by rw [Matrix.card_GL_field]; decide

/-- The prescribed shared Borel lies in an actual dihedral square. The original
recognition hypotheses have already supplied `c`; only the actual centralizer
equivalence for the second involution is additionally needed here. -/
public theorem exists_dihedral_square
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1) :
    ∃ M : Subgroup G, c.sharedSubgroup ≤ M ∧
      Nonempty (M ≃* (DihedralGroup 3 × DihedralGroup 3)) := by
  obtain ⟨P, hrP, hcentral, hnormalizer⟩ :=
    Theory.GroupTheory.exists_normalized_sylow_three c.borelUnipotent
      c.borelUnipotent_order c.borelUnipotent_centralizer_card c.sylow_three_card
  obtain ⟨ht, hm⟩ := c.borel_involutions_mem_unipotent_normalizer
  rw [c.sharedSubgroup_eq_closure]
  apply Subgroup.exists_dihedral_three_square_of_nonabelian_three_group
    (P : Subgroup G) c.involution c.borelReflection c.borelUnipotent
    (c.sylow_three_card P) (c.sylow_three_nonabelian P)
    c.order_involution c.borelReflection_order c.borelUnipotent_order
    hrP hcentral (hnormalizer ht) (hnormalizer hm)
    c.involution_commute_borelReflection c.involution_commute_borelUnipotent
    c.borelReflection_inverts_unipotent (c.borelReflection_centralizer_card hC)
  intro x hx htx hmx
  apply c.borel_pair_cubic_fixed_free x _ htx hmx
  simpa only [c.sylow_three_exponent P] using Subgroup.pow_exponent_eq_one hx

end
end ABG.ThreeLinearLocalData

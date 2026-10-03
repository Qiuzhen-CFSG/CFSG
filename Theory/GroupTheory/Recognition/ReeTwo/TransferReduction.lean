module

public import Theory.SpecificGroups.ReeTwo.Sylow
public import Theory.SpecificGroups.ReeTwo.CentralizerCenter
public import Theory.GroupTheory.FusionInvariantTransfer
public import Theory.GroupTheory.OrderFourTransfer

/-!
# Transfer reductions from an actual Ree two centralizer

An actual isomorphism from the centralizer of a Sylow-central involution
to `ReeTwo.Centralizer` induces an isomorphism from the ambient Sylow
subgroup to the concrete 4096-element model. No identification by order
is used. Abelian characters of the concrete centralizer transport through
this equivalence and respect conjugation in the actual centralizer.
Nonsolvable simplicity then forces an ambient conjugate of root 1
into the binary character kernel, by order-four transfer.

These are reductions for the q = 2 exclusion in Shinoda (1975), p. 79 and
(4.5), p. 85. The remaining local fusion separation is not proved here.
In particular, the presence of the local character is not asserted to
imply that it is invariant under ambient fusion. Such invariance, or just
exclusion of the forced root-1 conjugate, is the outstanding recognition
step (Parrott (1973), pp. 341–357; alternatively van Beek (2024), Prop. 3.1).
-/

namespace ReeTwo

open scoped IsMulCommutative

/-- An actual centralizer isomorphism sends the given involution to root 12;
this identification is forced by the verified center, not an extra hypothesis. -/
public theorem centralizerEquiv_apply_involution
    {G : Type*} [Group G] (z : G) (hz : orderOf z = 2)
    (centralizerEquiv : Subgroup.centralizer {z} ≃* Centralizer) :
    centralizerEquiv ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ =
      Centralizer.root 9 := by
  let distinguished : Subgroup.centralizer {z} :=
    ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hcenter : distinguished ∈ Subgroup.center (Subgroup.centralizer {z}) := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.property)
  apply Centralizer.eq_root_twelve_of_mem_center_of_ne_one
  · apply Subgroup.mem_center_iff.mpr
    intro x
    obtain ⟨y, rfl⟩ := centralizerEquiv.surjective x
    simpa only [map_mul] using congrArg centralizerEquiv
      (Subgroup.mem_center_iff.mp hcenter y)
  · intro h
    have hone : distinguished = 1 := centralizerEquiv.injective
      (h.trans (map_one centralizerEquiv).symm)
    have hzone : z = 1 := congrArg Subtype.val hone
    simp [hzone] at hz

/-- Restrict an actual centralizer isomorphism to the ambient Sylow subgroup,
then use Sylow conjugacy in the concrete model. The construction is exposed
so recognition lemmas can follow the specified root transport. -/
@[expose] public noncomputable def sylowEquivOfCentralizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (centralizerEquiv : Subgroup.centralizer {z} ≃* Centralizer) :
    S ≃* SylowModel := by
  let localSylow := S.subtype hcentral
  let imageSylow := localSylow.mapSurjective
    (f := centralizerEquiv.toMonoidHom) centralizerEquiv.surjective
  let imageEquiv : localSylow ≃* imageSylow := MulEquiv.ofBijective
    (centralizerEquiv.toMonoidHom.subgroupMap (localSylow : Subgroup _))
    ⟨fun x y h => Subtype.ext (centralizerEquiv.injective (congrArg Subtype.val h)),
      centralizerEquiv.toMonoidHom.subgroupMap_surjective _⟩
  exact (Subgroup.subgroupOfEquivOfLe hcentral).symm.trans
    (imageEquiv.trans (SylowModel.equiv imageSylow).symm)

private theorem abelianCharacter_sylow_equiv
    {A : Type*} [CommGroup A] (χ : Centralizer →* A)
    (P Q : Sylow 2 Centralizer) (x : P) :
    χ (Sylow.equiv P Q x : Centralizer) = χ (x : Centralizer) := by
  unfold Sylow.equiv
  generalize_proofs h hcast
  generalize hg : Classical.choose (MulAction.exists_smul_eq Centralizer P Q) = g at hcast ⊢
  have he : g • P = Q := hg ▸ Classical.choose_spec h
  subst Q
  change χ (g * (x : Centralizer) * g⁻¹) = _
  simp

private theorem abelianCharacter_model_equiv
    {A : Type*} [CommGroup A] (χ : Centralizer →* A)
    (P : Sylow 2 Centralizer) (x : SylowModel) :
    χ (SylowModel.equiv P x : Centralizer) = χ (SylowModel.embedding x) :=
  abelianCharacter_sylow_equiv χ SylowModel.sylow P (SylowModel.equivSylow x)

/-- Every abelian character of the concrete centralizer transports through the
chosen Sylow equivalence. The choice of Sylow conjugator has no effect. -/
public theorem abelianCharacter_sylowEquivOfCentralizer
    {A : Type*} [CommGroup A] (χ : Centralizer →* A)
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer) (x : S) :
    χ (SylowModel.embedding (sylowEquivOfCentralizer S z hcentral ec x)) =
      χ (ec ⟨x, hcentral x.property⟩) := by
  let P := (S.subtype hcentral).mapSurjective
    (f := ec.toMonoidHom) ec.surjective
  rw [← abelianCharacter_model_equiv χ P]
  let y : P := ⟨ec ⟨x, hcentral x.property⟩,
    ⟨⟨x, hcentral x.property⟩, x.property, rfl⟩⟩
  change χ (SylowModel.equiv P ((SylowModel.equiv P).symm y) : Centralizer) = _
  rw [MulEquiv.apply_symm_apply]

/-- Conjugation inside the involution centralizer preserves every transported
abelian character that extends to the concrete centralizer. -/
public theorem abelianCharacter_eq_of_conjugator_mem_centralizer
    {A : Type*} [CommGroup A] (χ : Centralizer →* A)
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer)
    {x y : S} {g : G} (hg : g ∈ Subgroup.centralizer {z})
    (hxy : g * (x : G) * g⁻¹ = (y : G)) :
    χ (SylowModel.embedding (sylowEquivOfCentralizer S z hcentral ec x)) =
      χ (SylowModel.embedding (sylowEquivOfCentralizer S z hcentral ec y)) := by
  rw [abelianCharacter_sylowEquivOfCentralizer, abelianCharacter_sylowEquivOfCentralizer]
  let f := χ.comp ec.toMonoidHom
  have h : IsConj (⟨x, hcentral x.property⟩ : Subgroup.centralizer {z})
      ⟨y, hcentral y.property⟩ :=
    isConj_iff.mpr ⟨⟨g, hg⟩, Subtype.ext hxy⟩
  exact isConj_iff_eq.mp (f.map_isConj h)

/-- The Sylow order follows from the multiplication-preserving identification. -/
public theorem sylow_card_of_centralizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (centralizerEquiv : Subgroup.centralizer {z} ≃* Centralizer) :
    Nat.card S = 4096 :=
  (Nat.card_congr (sylowEquivOfCentralizer S z hcentral centralizerEquiv).toEquiv).trans
    SylowModel.card

private theorem no_normal_index_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hi
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · have hcard : Nat.card G = 2 := by simpa [hbot] using hi
    let : IsCyclic G := isCyclic_of_prime_card hcard
    exact hns (Group.isSolvable_of_comm (fun a b => mul_comm a b))
  · simp [htop] at hi

/-- Simplicity forces root 1 to fuse into the character kernel. This is the
specific order-four fusion which a centralizer exclusion proof must rule out. -/
public theorem exists_rootOne_conjugate_in_character_kernel
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G) (e : S ≃* SylowModel) :
    ∃ other : S, IsConj ((e.symm SylowModel.rootOne : S) : G) (other : G) ∧
      SylowModel.character (e other) = 1 := by
  let character := SylowModel.character.comp e.toMonoidHom
  have hinvol (other : S) (h : other ^ 2 = 1) : character other = 1 := by
    change SylowModel.character (e other) = 1
    apply SylowModel.character_eq_one_of_square_eq_one
    simpa only [map_pow, map_one] using congrArg e h
  have horder : orderOf (e.symm SylowModel.rootOne) = 4 :=
    (orderOf_injective e.symm.toMonoidHom e.symm.injective _).trans SylowModel.rootOne_order
  exact S.exists_isConj_ker_of_order_four (no_normal_index_two hns)
    character (by change Nat.card (ZMod 2) = 2; simp) hinvol _ horder

/-- The full-centralizer input supplies the actual Sylow equivalence in the
forced order-four fusion statement. -/
public theorem exists_rootOne_conjugate_of_centralizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G) (z : G)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (centralizerEquiv : Subgroup.centralizer {z} ≃* Centralizer) :
    let e := sylowEquivOfCentralizer S z hcentral centralizerEquiv
    ∃ other : S, IsConj ((e.symm SylowModel.rootOne : S) : G) (other : G) ∧
      SylowModel.character (e other) = 1 :=
  exists_rootOne_conjugate_in_character_kernel hns S
    (sylowEquivOfCentralizer S z hcentral centralizerEquiv)

/-- Any nontrivial fusion-invariant binary character on the identified Sylow
contradicts simplicity. The character need not be the particular parity map. -/
public theorem false_of_fusion_invariant_character
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G) (e : S ≃* SylowModel)
    (character : SylowModel →* FiveFour.Cyclic 2)
    (hnontrivial : ∃ x, character x ≠ 1)
    (hrespect : ∀ x y : S, IsConj (x : G) (y : G) → character (e x) = character (e y)) :
    False := by
  obtain ⟨x, hx⟩ := hnontrivial
  have h := S.fusion_invariant_eq_one_of_simple hns
    (character.comp e.toMonoidHom) (by change Nat.card (ZMod 2) = 2; simp)
    hrespect (e.symm x)
  exact hx (by simpa using h)

end ReeTwo

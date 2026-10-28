module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.ExtraspecialPlus
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceRigidity
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.GroupTheory.QuaternionCentralProductOuterWreath
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Reduction
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Defs
public import Theory.GroupAction.ElementaryEightPointEnlargement
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Conditional helpers and a source obstruction for the Aut(M₁₂) branch

These results derive consequences of supplied quaternion factors, quotient
equivalences, cardinalities and normalizer inclusions. They do not construct
the Aut(M₁₂) parabolics, classify their invariant cores, or prove the required
four-dimensional indecomposable action. In particular, the elementary-eight
enlargement below does not establish that four-dimensional alternative.

The source contradiction needs an element of `N_{Kc}(J(T))` moving `V`.
The final normalizer lemma records that exact membership requirement.  The
source-facing structures below retain the actual quotient maps, axis action,
factor embeddings and marked subgroups, so that their conclusions can be
transported to a concrete parabolic pair without replacing it by an
unrelated abstract group.

The legacy `AutM12OuterWreathData` instead identifies `QH/Z` with the full
outer wreath group `SL₂(2) ≀ C₂`, of order 72. The source identifies it with
`E₄ ≀ C₂`, of order 32. The obstruction theorems below prove that the legacy
record cannot be instantiated on the actual two-core, including with its
ambient embedding. Its conditional theorem is retained, but cannot supply
this source identification.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal

open Subgroup

/-! ### The quaternion core -/

/-- The commutator core `[QH, O²(H)]` is the plus extraspecial group of order
32 as soon as its two quaternion factors are supplied.  `d` contains the
actual factor embeddings, so this does not replace the local core by an
abstract group of order 32. -/
public theorem autM12_qk_extraspecial_plus
    {QK : Type*} [Group QK] [Finite QK]
    (d : QuaternionCentralProductData QK) :
    Nat.card QK = 32 ∧ IsExtraspecial 2 QK := by
  exact ⟨d.card, d.extraspecial⟩

/-- The central quotient of the Aut(M₁₂) quaternion core has order sixteen and
is elementary abelian. -/
public theorem autM12_qk_quotient_elementary
    {QK : Type*} [Group QK] [Finite QK]
    (d : QuaternionCentralProductData QK) :
    Nat.card (QK ⧸ center QK) = 16 ∧
      IsElementaryAbelian 2 (QK ⧸ center QK) := by
  exact ⟨d.quotient_card, d.quotient_elementary⟩

/-- A wrapper retaining a supplied quotient equivalence to an arbitrary
group `W`. It does not identify a wreath group or establish action
compatibility. The subgroup being factored out is explicit. -/
public structure AutM12WreathQuotient
    (QH : Type*) [Group QH] (Z : Subgroup QH) (W : Type*) [Group W]
    [Z.Normal] where
  model : Nonempty ((QH ⧸ Z) ≃* W)

public theorem autM12_qh_quotient_wreath
    {QH : Type*} [Group QH] (Z : Subgroup QH) {W : Type*} [Group W]
    [Z.Normal] (model : Nonempty ((QH ⧸ Z) ≃* W)) :
    Nonempty ((QH ⧸ Z) ≃* W) :=
  model

/-! ### Legacy full-outer wreath interface -/

/- This record keeps the action on six cyclic-four axes and its kernel
   equality visible. Its quotient actor is the full Frattini automorphism
   image, with order 72. That is not the source two-core quotient `QH/Z`.
   See `autM12_no_outer_wreath_data_on_mapped_two_core` below. -/

/-- Legacy full-outer action data, incompatible with the source `QH = O₂(H)`.
The public interface is retained for its conditional consequences. -/
public structure AutM12OuterWreathData
    (QH : Type*) [Group QH] (Z : Subgroup QH) [Z.Normal]
    (K : Type*) [Group K] where
  axisCoordinates : Subgroup.CyclicFourSubgroups K ≃
    (Fin 3 × Multiplicative (ZMod 2))
  blocks : ∀ a : MulAut K, ∃ q : Multiplicative (ZMod 2),
    ∀ D : Subgroup.CyclicFourSubgroups K,
      (axisCoordinates (Subgroup.cyclicFourAction a D)).2 =
        q * (axisCoordinates D).2
  kernel_eq : (Subgroup.quotientAut (frattini K)).ker =
    (Subgroup.cyclicFourAction (G := K)).ker
  quotient_actor : (QH ⧸ Z) ≃*
    (Subgroup.quotientAut (frattini K)).range
  quotient_card : Nat.card (QH ⧸ Z) = 72

private theorem autM12_wreath_card :
    Nat.card (RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
      (Multiplicative (ZMod 2))) = 72 := by
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  rw [RegularWreathProduct.card, hSL]
  norm_num [Nat.card_eq_fintype_card]

/-- The legacy data identify the supplied quotient with `SL₂(2) ≀ C₂`.
The equivalence is built from the supplied range embedding. This does not
identify the source two-core quotient, whose wreath base is `E₄`. -/
public theorem autM12_qh_quotient_actual_wreath
    {QH : Type*} [Group QH] (Z : Subgroup QH) [Z.Normal]
    {K : Type*} [Group K] (d : AutM12OuterWreathData QH Z K) :
    Nonempty (QH ⧸ Z ≃*
      RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
        (Multiplicative (ZMod 2))) := by
  obtain ⟨f, hf⟩ := Subgroup.exists_frattini_outer_wreath_embedding_of_cyclicFour_coordinates
    d.axisCoordinates d.blocks d.kernel_eq
  let F : QH ⧸ Z →*
      RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
        (Multiplicative (ZMod 2)) := f.comp d.quotient_actor.toMonoidHom
  have hFi : Function.Injective F := hf.comp d.quotient_actor.injective
  have hbij : Function.Bijective F :=
    (Nat.bijective_iff_injective_and_card F).mpr
      ⟨hFi, d.quotient_card.trans autM12_wreath_card.symm⟩
  exact ⟨MulEquiv.ofBijective F hbij⟩

/-! ### Obstruction to using the full outer image as the two-core quotient -/

/-- The wreath group appearing in source 14.2.21 has order 32. -/
public theorem autM12_source_wreath_card :
    Nat.card (RegularWreathProduct (Multiplicative (Fin 2 → ZMod 2))
      (Multiplicative (ZMod 2))) = 32 := by
  rw [RegularWreathProduct.card]
  norm_num [Nat.card_eq_fintype_card]

/-- A quotient of a finite two-group cannot have the order 72 required by
the legacy full-outer interface. No choice of axis coordinates repairs this. -/
public theorem autM12_no_outer_wreath_data_of_two_group
    {QH : Type*} [Group QH] [Finite QH]
    (Z : Subgroup QH) [Z.Normal] {K : Type*} [Group K]
    (hQH : IsPGroup 2 QH) : ¬ Nonempty (AutM12OuterWreathData QH Z K) := by
  rintro ⟨d⟩
  obtain ⟨n, hn⟩ := (hQH.to_quotient Z).exists_card_eq
  have hthree : 3 ∣ 2 ^ n := by
    rw [← hn, d.quotient_card]
    decide
  have hbad := (by decide : Nat.Prime 3).dvd_of_dvd_pow hthree
  norm_num at hbad

/-- The obstruction applies to the actual ambient image of `O₂(H)` for
every finite local group `H`, hence also to an Aut(M₁₂) parabolic. -/
public theorem autM12_no_outer_wreath_data_on_mapped_two_core
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (Z : Subgroup ((pCore 2 H).map H.subtype)) [Z.Normal]
    {K : Type*} [Group K] :
    ¬ Nonempty (AutM12OuterWreathData ((pCore 2 H).map H.subtype) Z K) := by
  exact autM12_no_outer_wreath_data_of_two_group Z (pCore_isPGroup.map H.subtype)

/-- The source `E₄ ≀ C₂` identification and the legacy full-outer data
cannot both hold for the same quotient. -/
public theorem autM12_no_outer_wreath_data_of_source_wreath
    {QH : Type*} [Group QH] (Z : Subgroup QH) [Z.Normal]
    {K : Type*} [Group K]
    (e : QH ⧸ Z ≃* RegularWreathProduct (Multiplicative (Fin 2 → ZMod 2))
      (Multiplicative (ZMod 2))) :
    ¬ Nonempty (AutM12OuterWreathData QH Z K) := by
  rintro ⟨d⟩
  have hcard : Nat.card (QH ⧸ Z) = 32 :=
    (Nat.card_congr e.toEquiv).trans autM12_source_wreath_card
  have h := d.quotient_card
  omega

/-! ### The actual commutator core -/

/- The source notation `QK = [QH,O²(H)]` is represented by the subgroup
   commutator in the ambient group.  The residual equality is retained as an
   explicit field because `O²(H)` is a subgroup of `H`, while the commutator
   lives in the ambient group. -/

public structure AutM12QuaternionCoreData
    {G : Type*} [Group G] [Finite G]
    (QH K QK H : Subgroup G) where
  residual_eq : K = (pResidual 2 H).map H.subtype
  commutator_eq : QK = ⁅QH, K⁆
  core_le_qh : QK ≤ QH
  factors : Subgroup.QuaternionCentralProductData QK

/-- The displayed commutator is the source `QK=[QH,O²(H)]`, and the supplied
    factor embeddings prove its order and plus extraspecial type. -/
public theorem autM12_qk_identified
    {G : Type*} [Group G] [Finite G]
    {QH K QK H : Subgroup G} (d : AutM12QuaternionCoreData QH K QK H) :
    QK = ⁅QH, (pResidual 2 H).map H.subtype⁆ ∧
      Nat.card QK = 32 ∧ IsExtraspecial 2 QK := by
  refine ⟨d.commutator_eq.trans (congrArg (fun X => ⁅QH, X⁆) d.residual_eq), ?_⟩
  exact autM12_qk_extraspecial_plus d.factors

/-! ### Invariant cores and the S₄/L₃(2) alternative -/

/-- The abelian branch of the centralizer chain (*) forces the full local core.
This does not apply to the nonabelian wreath quotient in the Aut(M₁₂) branch.
The map is the literal quotient map modulo the supplied central subgroup. -/
public theorem autM12_core_eq_qh_of_abelian_chain
    {D : Type*} [Group D] (Z Q QH : Subgroup D) [Z.Normal]
    (hZQ : Z ≤ Q) (hQQH : Q ≤ QH)
    [IsMulCommutative (QH.map (QuotientGroup.mk' Z))]
    (hcentralizer : Subgroup.centralizer (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z)) : Q = QH := by
  exact core_eq_of_abelian_quotient Z Q QH hZQ hQQH hcentralizer

/-- In the remaining elementary-eight branch, an actual quotient of order
eight over a central subgroup of order two has order sixteen. -/
public theorem autM12_other_core_card_sixteen
    {D : Type*} [Group D] [Finite D]
    (Z Q : Subgroup D) [Z.Normal] (hZQ : Z ≤ Q)
    (hZ : Nat.card Z = 2)
    (hquot : Nat.card (Q ⧸ Z.subgroupOf Q) = 8) :
    Nat.card Q = 16 := by
  have h := (Z.subgroupOf Q).card_mul_index
  have hZ' : Nat.card (Z.subgroupOf Q) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZQ).toEquiv).trans hZ
  rw [index_eq_card, hquot, hZ'] at h
  omega

/-! ### The invariant-core trichotomy -/

/- The following reduction is deliberately stated at the level of the actual
   subgroups in `Mc`.  `other` is the second maximal abelian E₈ over `Z`; it is
   not an arbitrary subgroup of the ambient group.  The finite calculation in
   the compatible Aut(M₁₂) model supplies `core_reduction`.  The theorem below
   then performs the source-level transport and records the three alternatives
   with their ambient embeddings. -/

public structure AutM12InvariantCoreData
    {G : Type*} [Group G] [Finite G]
    (Z Q QH QK : Subgroup G) where
  z_le_q : Z ≤ Q
  q_le_qh : Q ≤ QH
  qk_le_q : QK ≤ Q
  z_le_qk : Z ≤ QK
  qk_eq_qh_core : QK ≤ QH
  other : Subgroup G
  other_le_qh : other ≤ QH
  z_le_other : Z ≤ other
  other_quotient_card : Nat.card (other ⧸ Z.subgroupOf other) = 8
  /-- The centralizer-chain conclusion of the actual wreath calculation. -/
  core_reduction :
    Q = QH ∨ Q = QK ∨ Q = other

/-- The source centralizer-chain calculation yields exactly `QH`, `QK`, or the
    other maximal abelian E₈.  The hypotheses retain the actual `Z`, `QK` and
    `other` subgroups, so the result is transportable to a marked parabolic
    pair. -/
public theorem autM12_invariant_core_trichotomy
    {G : Type*} [Group G] [Finite G]
    {Z Q QH QK : Subgroup G} (d : AutM12InvariantCoreData Z Q QH QK) :
    Q = QH ∨ Q = QK ∨ Q = d.other :=
  d.core_reduction

/-! ### The E₁₆ indecomposable `L₃(2)` alternative -/

/- The action record uses the actual actor and action homomorphism.  Its
   `indecomposable` field is the source invariant-subspace assertion, stated
   with subgroup complements so it is meaningful for the actual elementary
   abelian group rather than for an abstract order-16 placeholder. -/

public structure AutM12E16ActionData
    (L E : Type*) [Group L] [Group E] [Finite E]
    [IsElementaryAbelian 2 E] where
  four_space : Nonempty (E ≃* Multiplicative (Fin 4 → ZMod 2))
  actor : Nonempty (L ≃* Matrix.PSL3Two.PSL)
  action : L →* MulAut E
  action_injective : Function.Injective action
  z : E
  fixes_z : ∀ l : L, action l z = z
  indecomposable : ∀ U V : Subgroup E,
    (∀ l : L, U.map (action l).toMonoidHom = U) →
    (∀ l : L, V.map (action l).toMonoidHom = V) →
    IsCompl U V → U = ⊥ ∨ V = ⊥

/-- The compatible four-dimensional action is faithful, fixes the marked point,
    identifies the actor with `L₃(2)`, and is indecomposable in the source
    sense. -/
public theorem autM12_e16_indecomposable_l3
    {L E : Type*} [Group L] [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (d : AutM12E16ActionData L E) :
    Nat.card E = 16 ∧
      Nonempty (E ≃* Multiplicative (Fin 4 → ZMod 2)) ∧
      Nonempty (L ≃* Matrix.PSL3Two.PSL) ∧
      Function.Injective d.action ∧
      (∀ l : L, d.action l d.z = d.z) ∧
      (∀ U V : Subgroup E,
        (∀ l : L, U.map (d.action l).toMonoidHom = U) →
        (∀ l : L, V.map (d.action l).toMonoidHom = V) →
        IsCompl U V → U = ⊥ ∨ V = ⊥) := by
  obtain ⟨e⟩ := d.four_space
  have hcard : Nat.card E = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  exact ⟨hcard, d.four_space, d.actor, d.action_injective, d.fixes_z,
    d.indecomposable⟩

/-! ### The marked normalizer witness -/

/- The residual recognition theorem supplies actual commuting SL₂(3) factors.
   The source movement calculation is retained as non-preservation of the
   marked subgroup by one of those factors.  From that calculation we build
   the ambient element in the *relative* normalizer; the moving element is
   consequently a conclusion of this module. -/

public structure AutM12MarkedResidualData
    {G : Type*} [Group G] [Finite G]
    {Q : Subgroup G} [Q.Normal]
    (d : Subgroup.QuaternionCentralProductData Q)
    (Kc J V : Subgroup G) where
  residual : Subgroup.QuaternionResidualCentralProduct Q d
  left_le_Kc : residual.left ≤ Kc
  right_le_Kc : residual.right ≤ Kc
  left_le_normalizer_J : residual.left ≤ Subgroup.normalizer (J : Set G)
  right_le_normalizer_J : residual.right ≤ Subgroup.normalizer (J : Set G)
  /-- The compatible factor action on the marked `V` is nontrivial. -/
  left_not_normalizes_V : ¬ residual.left ≤ Subgroup.normalizer (V : Set G)

/-- An actual element of `Kc ∩ N_G(J)` moves the marked source subgroup `V`.
    This is the witness required before applying the normalizer obstruction. -/
public theorem autM12_construct_marked_movement
    {G : Type*} [Group G] [Finite G]
    {Q : Subgroup G} [Q.Normal]
    (d : Subgroup.QuaternionCentralProductData Q)
    (Kc J V : Subgroup G)
    (r : AutM12MarkedResidualData d Kc J V) :
    (∃ g : (Kc ⊓ Subgroup.normalizer (J : Set G) : Subgroup G),
      V.map (MulAut.conj (g : G)).toMonoidHom ≠ V) ∧
      ¬ Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  have hex : ∃ x : G, x ∈ r.residual.left ∧
      x ∉ Subgroup.normalizer (V : Set G) := by
    classical
    by_contra h
    apply r.left_not_normalizes_V
    intro x hx
    by_contra hxn
    apply h
    exact ⟨x, hx, hxn⟩
  obtain ⟨x, hx, hxn⟩ := hex
  have hmove : V.map (MulAut.conj (x : G)).toMonoidHom ≠ V := by
    intro heq
    exact hxn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
  let g : (Kc ⊓ Subgroup.normalizer (J : Set G) : Subgroup G) :=
    ⟨(x : G), ⟨r.left_le_Kc hx, r.left_le_normalizer_J hx⟩⟩
  have hg : V.map (MulAut.conj (g : G)).toMonoidHom ≠ V := by
    simpa [g] using hmove
  refine ⟨⟨g, hg⟩, ?_⟩
  intro hJ
  exact hg (Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (hJ g.property.2))

/-- An E₈ point-stabilizer enlargement consequence. It is not the E₁₆
indecomposable-action alternative in the Aut(M₁₂) branch. The moving
normalizer element and the actual S₄ stabilizer are supplied as hypotheses. -/
public theorem autM12_strict_residual_l3_alternative
    {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) (z : E)
    (hS : Nonempty (MulAction.stabilizer (MulAut E) z ≃* Equiv.Perm (Fin 4)))
    (hSimage : MulAction.stabilizer (MulAut E) z ≤ E.normalizerMonoidHom.range)
    (hmoves : ∃ g : Subgroup.normalizer (E : Set G),
      E.normalizerMonoidHom g z ≠ z) :
    ∃ e : MulAut E ≃* Matrix.PSL3Two.PSL,
      Function.Surjective (e.toMonoidHom.comp E.normalizerMonoidHom) ∧
        (e.toMonoidHom.comp E.normalizerMonoidHom).ker =
          (Subgroup.centralizer (E : Set G)).subgroupOf
            (Subgroup.normalizer (E : Set G)) := by
  exact normalizer_PSL3_of_moves E hE z hS hSimage hmoves

/-! ### Normality and the residual movement obstruction -/

/-- A concrete normalizer inclusion proves normality of the commutator core in
the larger local group. -/
public theorem autM12_qk_normal_in_larger_local
    {G : Type*} [Group G] (QK Mc : Subgroup G)
    (hQK : QK ≤ Mc)
    (hMc : Mc ≤ Subgroup.normalizer (QK : Set G)) :
    (QK.subgroupOf Mc).Normal := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mpr hMc

/-- The Thompson subgroup `J(T)` is normal in a second parabolic as soon as
its actual normalizer contains that parabolic. -/
public theorem autM12_JT_normal_in_second_parabolic
    {G : Type*} [Group G] (J Y : Subgroup G)
    (hJY : J ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (J : Set G)) :
    (J.subgroupOf Y).Normal := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJY).mpr hYN

/-- A supplied moving element rules out preservation by the whole residual.
The source contradiction additionally requires that element to normalize
`J(T)`; this theorem alone does not supply that condition. -/
public theorem autM12_residual_does_not_preserve_V
    {G : Type*} [Group G] (Kc V : Subgroup G)
    (hmoves : ∃ g : Kc, V.map (MulAut.conj (g : G)).toMonoidHom ≠ V) :
    ¬ Kc ≤ Subgroup.normalizer (V : Set G) := by
  intro hK
  obtain ⟨g, hg⟩ := hmoves
  exact hg (mem_normalizer_iff_map_conj_eq.mp (hK g.property))

/-- The normalizer obstruction used in the Aut(M₁₂) branch of 14.2.21.
The moving element belongs to the relative normalizer `N_{Kc}(J(T))`,
represented in the ambient group by an intersection. Thus the source
inclusion `N_G(J(T)) ≤ N_G(V)` contradicts this conclusion. Constructing
the displayed witness from the actual local pair remains a separate input. -/
public theorem autM12_JT_normalizer_does_not_preserve_V
    {G : Type*} [Group G] (Kc J V : Subgroup G)
    (hmoves : ∃ g : (Kc ⊓ Subgroup.normalizer (J : Set G) : Subgroup G),
      V.map (MulAut.conj (g : G)).toMonoidHom ≠ V) :
    ¬ Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  intro hJ
  exact autM12_residual_does_not_preserve_V
    (Kc ⊓ Subgroup.normalizer (J : Set G)) V hmoves (inf_le_right.trans hJ)

/-! ### Strict residual enlargement -/

/-- The strict residual branch retains the source's order calculation and the
independent cubic actors on the two embedded quaternion factors. -/
public theorem autM12_strict_residual_order_and_cubics
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hcentral : centralizer (Q : Set G) ≤ Q)
    (H : Subgroup G) (hQH : Q ≤ H)
    (e : H ⧸ Q.subgroupOf H ≃* Equiv.Perm (Fin 3))
    (S : Sylow 2 G) (hSH : (S : Subgroup G) ≤ H)
    (hstrict : (pResidual 2 H).map H.subtype < pResidual 2 G) :
    Nat.card G = 576 ∧
      Nonempty (QuaternionIndependentCubics
        (d.left.map Q.subtype) (d.right.map Q.subtype)) := by
  have hcard := card_eq_576_of_quaternion_product_residual_enlargement
    Q d hcentral H hQH e S hSH hstrict
  exact ⟨hcard, independent_cubics_of_normal_quaternion_product_card_576
    Q d hcentral hcard⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal

module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.Quotients
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.Theta
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# Source inputs and actual component images for 15.3.24

The earlier inputs retain the intrinsic two-cores, the Frattini denominator
of 15.3.11(5i), and normality relative to the local overgroup. They construct
both required source quotients, the component Sylow intersection, and the
actual action of S on L/O₂(L). They contain no assertion of innerness or
parabolic recognition.

A homomorphism with two-group kernel preserves the quotient by the two-core
of each subgroup, but need not identify that subgroup with its whole image.
We apply this to the marked linear action. The image of Y₊(S ∩ L) is
solvable and has three-part nine. Order-three lifting also identifies the
image of Y₊ with the cubic-generated subgroup of the intersection image.
Thus any constructed plane marking identifies the actual Y₊ image.

The section map explicitly identifies (X ∩ L)/(X ∩ O₂(L)) with its marked
image. For X = R ∩ L the earlier core containment recovers all of O₂(L).
`ParabolicData` is the remaining geometric output to construct, including
its literal radical image and the elementary group of order sixteen.

Source: Aschbacher–Smith, 15.3.11(1),(5i),(6), 15.3.12(1),
15.3.15(3), 15.3.17(2), and 15.3.24, printed pp.1123–1129.
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation
variable {G : Type*} [Group G]

/-- The exact earlier clauses used in the binary preparation. The quotient conclusions of 15.3.24 and its plane marking are not inputs. -/
structure Earlier (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I) : Prop where
  sylow : Chapter1.IsSylowIn 2 d.S I
  yplus_le : d.Yplus ≤ c.L
  component_eq_theta : c.L = theta I
  theta_local : theta (d.MI I) = d.Yplus
  cubic_quotient : OutsideStructure.CubicQuotient (d.Yplus ⧸ pCore 2 d.Yplus)
  frattini_shadow : Nonempty (((d.Yplus ⊔ d.S : Subgroup G) ⧸
    OutsideStructure.coreFrattiniSubgroup (d.Yplus ⊔ d.S : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
  solvable_control : SolvableInvariantControl d I
  core_le_R : c.L.pCoreIn 2 ≤ d.R

/-- The specified Sylow subgroup lies in the actual outside overgroup. -/
theorem Earlier.sylow_le {d : LocalData G} {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d c) : d.S ≤ I := by
  obtain ⟨P, hP⟩ := h.sylow
  rw [← hP]
  exact map_subtype_le _

/-- The equality L = θ(I) gives relative normalization by S. -/
theorem Earlier.sylow_normalizes_component {d : LocalData G} {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d c) :
    d.S ≤ normalizer (c.L : Set G) :=
  h.sylow_le.trans (normalizes_of_eq_theta h.component_eq_theta)

/-- The local theta equality gives the actual S-invariance of Y₊. -/
theorem Earlier.sylow_normalizes_yplus {d : LocalData G} {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d c) :
    d.S ≤ normalizer (d.Yplus : Set G) := by
  rw [← h.theta_local]
  exact (le_inf (inf_le_left.trans d.sylow_le) h.sylow_le).trans
    ((d.MI I).le_normalizer.trans (normalizer_le_normalizer_theta _))

/-- The literal S ∩ L is Sylow in L, using relative component normality. -/
theorem Earlier.sylow_component [Finite G] {d : LocalData G} {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d c) :
    Chapter1.IsSylowIn 2 (d.S ⊓ c.L) c.L :=
  sylow_intersection_of_eq_theta d h.sylow h.component_eq_theta

/-- Construct both quotients in the first paragraph of 15.3.24 from the precise earlier alternatives. -/
theorem source_quotients [Finite G] {d : LocalData G} {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d c) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective n) :
    Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3)) ∧
    Nonempty (((d.Yplus ⊔ d.S : Subgroup G) ⧸ pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
  ⟨yplus_quotient d hn e h.yplus_le h.cubic_quotient,
    join_quotient d hn e h.yplus_le h.cubic_quotient
      h.sylow_normalizes_yplus h.frattini_shadow⟩

/-- The actual image of X ∩ L in the binary linear model fixed by e. -/
noncomputable def modelImage {L : Subgroup G} {n : ℕ} (hn : 0 < n)
    (e : (L ⧸ pCore 2 L) ≃* Projective n) (X : Subgroup G) :
    Subgroup (LinearGroup n) := (X.subgroupOf L).map (linearAction hn e)

/-- The marked linear action has exactly the intrinsic two-core as its kernel. -/
theorem linearAction_ker {L : Subgroup G} {n : ℕ} (hn : 0 < n)
    (e : (L ⧸ pCore 2 L) ≃* Projective n) :
    (linearAction hn e).ker = pCore 2 L := by
  ext x
  change projectiveEquivLinear hn (e (QuotientGroup.mk' (pCore 2 L) x)) = 1 ↔ _
  rw [(projectiveEquivLinear hn).map_eq_one_iff, e.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

/-- The intrinsic section (X ∩ L)/(X ∩ O₂(L)); the denominator is a restricted subgroup of L, not the two-core of X. -/
abbrev CoreSection (L X : Subgroup G) :=
  (X.subgroupOf L) ⧸ (pCore 2 L).subgroupOf (X.subgroupOf L)

/-- The first-isomorphism equivalence from the literal component section to its marked image. -/
noncomputable def coreSectionEquiv {L : Subgroup G} {n : ℕ} (hn : 0 < n)
    (e : (L ⧸ pCore 2 L) ≃* Projective n) (X : Subgroup G) :
    CoreSection L X ≃* modelImage hn e X := by
  let f := (linearAction hn e).subgroupMap (X.subgroupOf L)
  have hk : f.ker = (pCore 2 L).subgroupOf (X.subgroupOf L) := by
    rw [ker_subgroupMap, linearAction_ker]
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f ((linearAction hn e).subgroupMap_surjective _))

/-- The section equivalence uses the specified quotient map on every representative. -/
theorem coreSectionEquiv_apply {L : Subgroup G} {n : ℕ} (hn : 0 < n)
    (e : (L ⧸ pCore 2 L) ≃* Projective n) (X : Subgroup G) (x : X.subgroupOf L) :
    (coreSectionEquiv hn e X (QuotientGroup.mk' _ x) : LinearGroup n) =
      linearAction hn e x.val := rfl

/-- For R ∩ L, the earlier core bound makes the restricted denominator the whole O₂(L). -/
theorem radical_denominator {d : LocalData G} {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d c) :
    ((pCore 2 c.L).subgroupOf ((d.R ⊓ c.L).subgroupOf c.L)).map
      ((d.R ⊓ c.L).subgroupOf c.L).subtype = pCore 2 c.L := by
  apply map_subgroupOf_eq_of_le
  intro l hl
  exact ⟨h.core_le_R (mem_map.mpr ⟨l, hl, rfl⟩), l.property⟩

/-- Removing the respective two-cores identifies a subgroup with its actual image; this does not identify the whole image with the original quotient. -/
theorem modelImage_quotient [Finite G] {L X : Subgroup G} {n : ℕ} (hn : 0 < n)
    (e : (L ⧸ pCore 2 L) ≃* Projective n) (hXL : X ≤ L) :
    Nonempty ((X ⧸ pCore 2 X) ≃*
      (modelImage hn e X ⧸ pCore 2 (modelImage hn e X))) := by
  let f := linearAction hn e
  let : Finite (LinearGroup n) :=
    Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  have hk : IsPGroup 2 (f.subgroupMap (X.subgroupOf L)).ker := by
    rw [ker_subgroupMap, linearAction_ker]
    exact pCore_isPGroup.comap_subtype
  let a := (subgroupOfEquivOfLe hXL).symm
  exact ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (MonoidHom.quotientPCoreEquivOfSurjective (f.subgroupMap (X.subgroupOf L))
      (f.subgroupMap_surjective _) hk)⟩

/-- The image of Y₊(S ∩ L) is solvable, using its actual normalized product. -/
theorem baseImage_solvable [Finite G] {d : LocalData G} {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d c) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective n) :
    Group.IsSolvable (modelImage (by omega : 0 < n) e (d.Yplus ⊔ (d.S ⊓ c.L))) := by
  obtain ⟨eY⟩ := (source_quotients h hn e).1
  have h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9 := by
    rw [Nat.card_congr eY.toEquiv]
    change Nat.card (Fin 2 → ZMod 3) = 9
    simp
  let : Group.IsSolvable (d.Yplus ⊔ (d.S ⊓ c.L) : Subgroup G) :=
    BinaryLinear.CubicPairGeometry.normalized_join_solvable _ _
      (d.T.isPGroup'.to_le (inf_le_left.trans inf_le_left))
      (inf_le_left.trans h.sylow_normalizes_yplus) 2 h9
  let a : ((d.Yplus ⊔ (d.S ⊓ c.L)).subgroupOf c.L) ≃*
      (d.Yplus ⊔ (d.S ⊓ c.L) : Subgroup G) :=
    subgroupOfEquivOfLe (sup_le h.yplus_le inf_le_right)
  let : Group.IsSolvable ((d.Yplus ⊔ (d.S ⊓ c.L)).subgroupOf c.L) :=
    Group.isSolvable_of_isSolvable_injective (f := a.toMonoidHom) a.injective
  exact Group.isSolvable_of_surjective
    ((linearAction (by omega : 0 < n) e).subgroupMap_surjective _)

/-- The quotient of the actual Y₊ image by its own two-core is E₉. -/
theorem yplusImage_quotient [Finite G] {d : LocalData G} {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d c) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective n) :
    Nonempty ((modelImage (by omega : 0 < n) e d.Yplus ⧸ pCore 2 (modelImage (by omega : 0 < n) e d.Yplus)) ≃*
      Multiplicative (Fin 2 → ZMod 3)) := by
  obtain ⟨a⟩ := modelImage_quotient (by omega : 0 < n) e h.yplus_le
  obtain ⟨b⟩ := (source_quotients h hn e).1
  exact ⟨a.symm.trans b⟩

private theorem core_quotient_three_part (H : Type*) [Group H] [Finite H] :
    (Nat.card (H ⧸ pCore 2 H)).factorization 3 = (Nat.card H).factorization 3 := by
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  conv_rhs => rw [← (pCore 2 H).card_mul_index, index_eq_card, hk,
    Nat.factorization_mul (pow_ne_zero _ (by decide)) Nat.card_pos.ne',
    Finsupp.add_apply, Nat.factorization_pow]
  simp only [Finsupp.smul_apply,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2), smul_zero, zero_add]

/-- The solvable base image has three-part nine, since its kernel is a two-group. -/
theorem baseImage_three_part [Finite G] {d : LocalData G} {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d c) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective n) :
    (Nat.card (modelImage (by omega : 0 < n) e (d.Yplus ⊔ (d.S ⊓ c.L)))).factorization 3 = 2 := by
  let : Finite (LinearGroup n) :=
    Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  obtain ⟨eY⟩ := (source_quotients h hn e).1
  have h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9 := by
    rw [Nat.card_congr eY.toEquiv]
    change Nat.card (Fin 2 → ZMod 3) = 9
    simp
  obtain ⟨a⟩ := modelImage_quotient (by omega : 0 < n) e (sup_le h.yplus_le inf_le_right)
  rw [← core_quotient_three_part, ← Nat.card_congr a.toEquiv, core_quotient_three_part,
    BinaryLinear.CubicPairGeometry.normalized_join_three_part d.Yplus (d.S ⊓ c.L)
      (d.T.isPGroup'.to_le (inf_le_left.trans inf_le_left))
      (inf_le_left.trans h.sylow_normalizes_yplus)]
  exact BinaryLinear.CubicPairGeometry.three_part_of_core_quotient_nine _ h9

/-- Lifting order-three elements through the two-group kernel identifies cubic-generated images. -/
theorem modelImage_theta [Finite G] {L X : Subgroup G} {n : ℕ} (hn : 0 < n)
    (e : (L ⧸ pCore 2 L) ≃* Projective n) (hXL : X ≤ L) :
    modelImage hn e (theta X) = theta (modelImage hn e X) := by
  have ht : (theta X).subgroupOf L = theta (X.subgroupOf L) := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((theta_le X).trans hXL),
      theta_map_of_injective L.subtype L.subtype_injective,
      map_subgroupOf_eq_of_le hXL]
  unfold modelImage
  rw [ht]
  apply FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.theta_map_of_twoGroup_ker
  rw [linearAction_ker]
  exact pCore_isPGroup

/-- Since Y₊ lies in L, the earlier local theta identity restricts to M ∩ L. -/
theorem yplus_eq_theta_intersection {d : LocalData G} {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d c) :
    d.Yplus = theta (d.M ⊓ c.L) := by
  have hYI : d.Yplus ≤ d.M ⊓ c.L :=
    le_inf ((h.theta_local ▸ theta_le (d.MI I)).trans inf_le_left) h.yplus_le
  apply le_antisymm
  · calc
      d.Yplus = theta d.Yplus := by rw [← h.theta_local, theta_idempotent]
      _ ≤ theta (d.M ⊓ c.L) := theta_mono hYI
  · exact (theta_mono (inf_le_inf_left d.M (component_le c))).trans_eq h.theta_local

/-- The marked Y₊ image is the cubic-generated subgroup of the marked intersection. -/
theorem yplusImage_eq_theta [Finite G] {d : LocalData G} {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d c) {n : ℕ} (hn : 0 < n)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective n) :
    modelImage hn e d.Yplus = theta (modelImage hn e (d.M ⊓ c.L)) := by
  rw [yplus_eq_theta_intersection h, modelImage_theta hn e inf_le_right]

/-- A preimage marking identifies the actual image with the whole plane stabilizer. -/
theorem planeParabolic_image {d : LocalData G} {L : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* Projective 4} (p : PlaneParabolic d L e) :
    modelImage (by decide) e (d.M ⊓ L) = BinaryLinear.parabolic p.plane := by
  unfold modelImage
  rw [p.intersection, map_comap_eq_self_of_surjective (linearAction_surjective _ e)]

/-- A plane marking determines the actual Y₊ image, including its two-core. -/
theorem yplusImage_eq_planeTheta [Finite G] {d : LocalData G} {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d c)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Projective 4} (p : PlaneParabolic d c.L e) :
    modelImage (by decide) e d.Yplus = theta (BinaryLinear.parabolic p.plane) := by
  rw [yplusImage_eq_theta h, planeParabolic_image p]

/-- The source geometric output, with a supplied quotient marking and the actual unipotent radical section. Existence remains to be proved. -/
structure ParabolicData (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Projective 4) where
  marking : PlaneParabolic d L e
  intersection_join : d.M ⊓ L = d.Yplus ⊔ (d.S ⊓ L)
  radical_image : modelImage (by decide : 0 < 4) e (d.R ⊓ L) =
    BinaryLinear.radical marking.plane
  radical_coordinates : CoreSection L (d.R ⊓ L) ≃* Multiplicative (Fin 4 → ZMod 2)

/-- The actual S-action on L/O₂(L), induced by ambient conjugation and relative normalization. -/
noncomputable def sylowCoreAction (d : LocalData G) (L : Subgroup G)
    (hn : d.S ≤ normalizer (L : Set G)) : d.S →* MulAut (L ⧸ pCore 2 L) :=
  (pCoreJoinAction 2 hn).comp (inclusion (show d.S ≤ L ⊔ d.S from le_sup_right))

/-- Trivial diagram action expressed by the actual Sylow automorphisms being inner. -/
def IsInnerOnComponent (d : LocalData G) (L : Subgroup G)
    (hn : d.S ≤ normalizer (L : Set G)) : Prop :=
  ∀ s : d.S, sylowCoreAction d L hn s ∈ MulAut.innerSubgroup (L ⧸ pCore 2 L)

/-- The induced Sylow action retains the original conjugation formula on quotient representatives. -/
theorem sylowCoreAction_apply (d : LocalData G) (L : Subgroup G)
    (hn : d.S ≤ normalizer (L : Set G)) (s : d.S) (l : L) :
    sylowCoreAction d L hn s (QuotientGroup.mk' (pCore 2 L) l) =
      QuotientGroup.mk' (pCore 2 L)
        (L.normalizerMonoidHom ⟨s, hn s.property⟩ l) :=
  pCoreJoinAction_mk 2 hn (inclusion le_sup_right s) l

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation

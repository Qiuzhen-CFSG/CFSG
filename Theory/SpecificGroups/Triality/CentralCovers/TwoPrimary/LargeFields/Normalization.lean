module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.RootRelations
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.TorusMotion
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# Canonical torus normalization of triality root sections

Assume each individual folded root has abelian full preimage in a central
extension of the genuine binary triality carrier. For q ≥ 4, nontrivial
motion by the actual Levi tori constructs additive sections by commutators.
Centrality makes these commutators independent of lift choices. Commutation
of the two folded tori proves equivariance under every scalar action of their
actual actors. A nonidentity scalar then proves uniqueness of the resulting
six sections.

The root-preimage hypothesis is exactly the remaining individual lifting
problem: any additive sections imply it. Neither it nor torus normalization
asserts the inter-root exchange relations. Those remain a separate obligation
in `RootSections.HigherCommutators`. In particular q = 4 is retained; the
nontrivial norm actor used here comes from the cubic field, not just its fixed
field units.

Sources: GLS3 §2.4, especially 2.4.7(f), and §6.1; Aschbacher–Smith A.2.4
and I.1.3 (PDF pp.44 and 418). The commutator construction follows the same
general argument as G2/MultiplierOrdinary/RootLifts and TorusEquivariance,
using the triality actors and both of its actual coefficient fields.
-/

@[expose] public section

open scoped commutatorElement

namespace Triality.Standard.CentralCovers.TwoPrimary
open Parabolics ConcreteBruhat RadicalCoordinates.LeviCommutators
noncomputable section

private theorem normalized_root_exists {F E G A : Type*} [Field F] [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (u : Multiplicative F →* G) (actor : A → G)
    (ha : ∀ a b, Commute (actor a) (actor b))
    (hcomm : ∀ v w : E, f v ∈ u.range → f w ∈ u.range → Commute v w)
    (a : A) (c : F) (hc : c ≠ 1)
    (hscale : ∀ x : F, actor a * u (.ofAdd x) * (actor a)⁻¹ = u (.ofAdd (c*x))) :
    ∃ s : Multiplicative F →* E, f.comp s = u ∧
      ∀ (b : A) (d : F),
        (∀ x : F, actor b * u (.ofAdd x) * (actor b)⁻¹ = u (.ofAdd (d*x))) →
        ∀ z : E, f z = actor b → ∀ x : F,
          z * s (.ofAdd x) * z⁻¹ = s (.ofAdd (d*x)) := by
  classical
  obtain ⟨v, hv⟩ := hf (actor a)
  choose w hw using fun x : F => hf (u (.ofAdd x))
  let s : F → E := fun x => ⁅v, w ((c-1)⁻¹*x)⁆
  have hd : c-1 ≠ 0 := sub_ne_zero.mpr hc
  have hs (x : F) : f (s x) = u (.ofAdd x) := by
    dsimp [s]
    rw [map_commutatorElement, commutatorElement_def, hv, hw, hscale,
      ← map_inv, ← map_mul]
    change u (.ofAdd (c*((c-1)⁻¹*x) + -((c-1)⁻¹*x))) = u (.ofAdd x)
    congr 1
    change c*((c-1)⁻¹*x) + -((c-1)⁻¹*x) = x
    calc
      _ = (c-1)*((c-1)⁻¹*x) := by ring
      _ = x := mul_inv_cancel_left₀ hd x
  have hs0 : s 0 = 1 := by
    dsimp [s]
    rw [mul_zero]
    have h0 : f (w 0) = f 1 := by rw [hw]; exact u.map_one.trans f.map_one.symm
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl h0]
    simp
  have hsadd (x y : F) : s (x+y) = s x * s y := by
    have hsum : f (w ((c-1)⁻¹*(x+y))) = f (w ((c-1)⁻¹*x) * w ((c-1)⁻¹*y)) := by
      rw [map_mul, hw, hw, hw, ← map_mul, mul_add]
      rfl
    have hcw : Commute (w ((c-1)⁻¹*x)) (s y) := hcomm _ _
      (by rw [hw]; exact ⟨.ofAdd _, rfl⟩) (by rw [hs]; exact ⟨.ofAdd _, rfl⟩)
    change ⁅v, w ((c-1)⁻¹*(x+y))⁆ = _
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl hsum,
      commutatorElement_mul_right_eq_mul_conj]
    change s x * w ((c-1)⁻¹*x) * s y * (w ((c-1)⁻¹*x))⁻¹ = _
    rw [mul_assoc (s x), hcw.eq, ← mul_assoc, mul_assoc (s x * s y),
      mul_inv_cancel, mul_one]
  refine ⟨{
    toFun := fun x => s x.toAdd
    map_one' := hs0
    map_mul' := fun x y => hsadd x.toAdd y.toAdd }, MonoidHom.ext (fun x => hs x.toAdd), ?_⟩
  intro b d hb z hz x
  change z * ⁅v, w ((c-1)⁻¹*x)⁆ * z⁻¹ = ⁅v, w ((c-1)⁻¹*(d*x))⁆
  rw [conjugate_commutatorElement]
  apply CentralExtension.commutator_eq_of_image_eq f hk
  · rw [map_mul, map_mul, map_inv, hz, hv, (ha b a).eq]
    simp only [mul_inv_cancel_right]
  · rw [map_mul, map_mul, map_inv, hz, hw, hw, hb]
    congr 1
    change d*((c-1)⁻¹*x) = (c-1)⁻¹*(d*x)
    ring

/-- The actual arms and central torus words commute after the genuine quotient. -/
theorem torusActor_commute (P : Parameters) (hp : P.prime = 2)
    (a b : Node) (t : (RootField P a)ˣ) (u : (RootField P b)ˣ) :
    Commute (torusActor P hp a t) (torusActor P hp b u) := by
  have h : Commute (torusElementary P hp a t) (torusElementary P hp b u) := by
    apply Commute.of_map (elementaryInclusion_injective P)
    have h3 (s : (ExtensionField P)ˣ) (i : Fin 4) (v : (ExtensionField P)ˣ) :
        Commute (torusWord P 0 s * torusWord P 2 (TorusCoordinates.frobenius P s) *
          torusWord P 3 (TorusCoordinates.frobenius P (TorusCoordinates.frobenius P s)))
          (torusWord P i v) :=
      ((TorusCoordinates.torusWord_commute P hp 0 i s v).mul_left
        (TorusCoordinates.torusWord_commute P hp 2 i _ v)).mul_left
          (TorusCoordinates.torusWord_commute P hp 3 i _ v)
    cases a <;> cases b <;>
      simp only [torusElementary_arms_val, torusElementary_central_val]
    · exact ((h3 t 0 u).mul_right (h3 t 2 _)).mul_right (h3 t 3 _)
    · exact h3 t 1 _
    · exact (h3 u 1 _).symm
    · exact TorusCoordinates.torusWord_commute P hp _ _ _ _
  exact h.map (toCarrier P)

variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

/-- The additive homomorphism of a published cubic-field folded root. -/
def baseShortHom (i : Fin 3) : Multiplicative (ExtensionField P) →* BinaryCarrier n hn where
  toFun x := short P rfl i x.toAdd
  map_one' := short_zero P rfl i
  map_mul' x y := short_add P rfl i x.toAdd y.toAdd

/-- The additive homomorphism of a published fixed-field folded root. -/
def baseLongHom (i : Fin 3) : Multiplicative (fixedField P) →* BinaryCarrier n hn where
  toFun x := long P rfl i x.toAdd
  map_one' := long_zero P rfl i
  map_mul' x y := long_add P rfl i x.toAdd y.toAdd

variable {E : Type*} [Group E] (f : E →* BinaryCarrier n hn)

/-- Only individual root preimages are constrained; no inter-root relation is assumed. -/
def RootPreimagesAbelian : Prop :=
  (∀ (i : Fin 3) (v w : E), f v ∈ (baseShortHom n hn i).range →
    f w ∈ (baseShortHom n hn i).range → Commute v w) ∧
  (∀ (i : Fin 3) (v w : E), f v ∈ (baseLongHom n hn i).range →
    f w ∈ (baseLongHom n hn i).range → Commute v w)

/-- Equivariance for every scalar action of an actual folded torus actor. -/
def ScalarEquivariant {F : Type*} [Field F]
    (u : Multiplicative F →* BinaryCarrier n hn) (s : Multiplicative F →* E) : Prop :=
  ∀ (a : Node) (t : (RootField P a)ˣ) (c : F),
    (∀ x : F, torusActor P rfl a t * u (.ofAdd x) * (torusActor P rfl a t)⁻¹ =
      u (.ofAdd (c*x))) →
    ∀ z : E, f z = torusActor P rfl a t → ∀ x : F,
      z * s (.ofAdd x) * z⁻¹ = s (.ofAdd (c*x))

/-- All six additive sections use the actual torus actions. -/
def RootSections.TorusNormalized (L : RootSections n hn f) : Prop :=
  (∀ i, ScalarEquivariant n hn f (baseShortHom n hn i) (L.shortRoot i)) ∧
  (∀ i, ScalarEquivariant n hn f (baseLongHom n hn i) (L.longRoot i))

private theorem short_scale (Q : Parameters) (hp : Q.prime = 2)
    (i : Fin 3) (a : Node) (t : (RootField Q a)ˣ) (c : ExtensionField Q)
    (h : ∀ x, elementaryInclusion Q (torusElementary Q hp a t) * shortSplit Q i x *
      (elementaryInclusion Q (torusElementary Q hp a t))⁻¹ = shortSplit Q i (c*x))
    (x : ExtensionField Q) :
    torusActor Q hp a t * short Q hp i x * (torusActor Q hp a t)⁻¹ =
      short Q hp i (c*x) := by
  simp only [torusActor, short, ← map_mul, ← map_inv]
  apply congrArg (toCarrier Q)
  apply elementaryInclusion_injective Q
  simp only [map_mul, map_inv, shortElementary_val]
  exact h x

private theorem long_scale (Q : Parameters) (hp : Q.prime = 2)
    (i : Fin 3) (a : Node) (t : (RootField Q a)ˣ) (c : fixedField Q)
    (h : ∀ x, elementaryInclusion Q (torusElementary Q hp a t) * longSplit Q i x *
      (elementaryInclusion Q (torusElementary Q hp a t))⁻¹ = longSplit Q i (c*x))
    (x : fixedField Q) :
    torusActor Q hp a t * long Q hp i x * (torusActor Q hp a t)⁻¹ =
      long Q hp i (c*x) := by
  simp only [torusActor, long, ← map_mul, ← map_inv]
  apply congrArg (toCarrier Q)
  apply elementaryInclusion_injective Q
  simp only [map_mul, map_inv, longElementary_val]
  exact h x

private theorem short_motion (hlarge : 2 ≤ n) (i : Fin 3) :
    ∃ (a : Node) (t : (RootField P a)ˣ) (c : ExtensionField P), c ≠ 1 ∧
      ∀ x, torusActor P rfl a t * baseShortHom n hn i (.ofAdd x) *
        (torusActor P rfl a t)⁻¹ = baseShortHom n hn i (.ofAdd (c*x)) := by
  have hq : 2 < (binaryParameters n hn).q := by
    change 2 < 2^n
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < n)
  have hm : ∃ a, ShortTorusMotion P rfl a i := by
    by_cases hi : i = 2
    · exact ⟨.arms, shortTorusMotion_arms P rfl hq i (by omega)⟩
    · exact ⟨.central, shortTorusMotion_central P rfl hq i hi⟩
  obtain ⟨a, t, c, hc, ht⟩ := hm
  exact ⟨a, t, c, hc, short_scale P rfl i a t c ht⟩

private theorem long_motion (hlarge : 2 ≤ n) (i : Fin 3) :
    ∃ (a : Node) (t : (RootField P a)ˣ) (c : fixedField P), c ≠ 1 ∧
      ∀ x, torusActor P rfl a t * baseLongHom n hn i (.ofAdd x) *
        (torusActor P rfl a t)⁻¹ = baseLongHom n hn i (.ofAdd (c*x)) := by
  have hq : 2 < (binaryParameters n hn).q := by
    change 2 < 2^n
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < n)
  have hm : ∃ a, LongTorusMotion P rfl a i := by
    by_cases hi : i = 0
    · exact ⟨.arms, longTorusMotion_arms P rfl hq i (by omega)⟩
    · exact ⟨.central, longTorusMotion_central P rfl hq i hi⟩
  obtain ⟨a, t, c, hc, ht⟩ := hm
  exact ⟨a, t, c, hc, long_scale P rfl i a t c ht⟩

/-- Construct one family normalized simultaneously by every folded torus actor. -/
theorem exists_torusNormalized_of_rootPreimagesAbelian (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hab : RootPreimagesAbelian n hn f) :
    ∃ L : RootSections n hn f, L.TorusNormalized := by
  let actor : (Σ a : Node, (RootField P a)ˣ) → BinaryCarrier n hn :=
    fun a => torusActor P rfl a.1 a.2
  have hshort (i : Fin 3) : ∃ s : Multiplicative (ExtensionField P) →* E,
      f.comp s = baseShortHom n hn i ∧
      ScalarEquivariant n hn f (baseShortHom n hn i) s := by
    obtain ⟨a, t, c, hc, hact⟩ := short_motion n hn hlarge i
    obtain ⟨s, hs, he⟩ := normalized_root_exists f hf hk (baseShortHom n hn i)
      actor (fun a b => torusActor_commute P rfl a.1 b.1 a.2 b.2)
      (hab.1 i) ⟨a, t⟩ c hc hact
    exact ⟨s, hs, fun a t => he ⟨a, t⟩⟩
  have hlong (i : Fin 3) : ∃ s : Multiplicative (fixedField P) →* E,
      f.comp s = baseLongHom n hn i ∧
      ScalarEquivariant n hn f (baseLongHom n hn i) s := by
    obtain ⟨a, t, c, hc, hact⟩ := long_motion n hn hlarge i
    obtain ⟨s, hs, he⟩ := normalized_root_exists f hf hk (baseLongHom n hn i)
      actor (fun a b => torusActor_commute P rfl a.1 b.1 a.2 b.2)
      (hab.2 i) ⟨a, t⟩ c hc hact
    exact ⟨s, hs, fun a t => he ⟨a, t⟩⟩
  choose s hs hse using hshort
  choose l hl hle using hlong
  exact ⟨{
    shortRoot := s
    longRoot := l
    project_short := fun i x => DFunLike.congr_fun (hs i) (.ofAdd x),
    project_long := fun i x => DFunLike.congr_fun (hl i) (.ofAdd x) }, hse, hle⟩

/-- Equal projections and one nonidentity scalar identify additive homomorphisms. -/
theorem hom_ext_of_scalar_equivariant {F : Type*} [Field F]
    (hk : f.ker ≤ Subgroup.center E) (u v : Multiplicative F →* E)
    (hproj : f.comp u = f.comp v) (z : E) (c : F) (hc : c ≠ 1)
    (hu : ∀ x : F, z * u (.ofAdd x) * z⁻¹ = u (.ofAdd (c*x)))
    (hv : ∀ x : F, z * v (.ofAdd x) * z⁻¹ = v (.ofAdd (c*x))) : u = v := by
  have hd : c-1 ≠ 0 := sub_ne_zero.mpr hc
  have he (w : Multiplicative F →* E)
      (hw : ∀ x : F, z * w (.ofAdd x) * z⁻¹ = w (.ofAdd (c*x))) (x : F) :
      ⁅z, w (.ofAdd ((c-1)⁻¹*x))⁆ = w (.ofAdd x) := by
    rw [commutatorElement_def, hw, ← map_inv, ← map_mul]
    change w (.ofAdd (c*((c-1)⁻¹*x) + -((c-1)⁻¹*x))) = w (.ofAdd x)
    apply congrArg (fun y : F => w (.ofAdd y))
    calc
      _ = (c-1)*((c-1)⁻¹*x) := by ring
      _ = x := mul_inv_cancel_left₀ hd x
  apply MonoidHom.ext
  intro x
  change u (.ofAdd x.toAdd) = v (.ofAdd x.toAdd)
  rw [← he u hu x.toAdd, ← he v hv x.toAdd]
  exact CentralExtension.commutator_eq_of_image_eq f hk rfl (DFunLike.congr_fun hproj _)

/-- Scalar normalization removes the independent choices of root sections. -/
theorem torusNormalized_unique (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (L M : RootSections n hn f) (hL : L.TorusNormalized) (hM : M.TorusNormalized) : L = M := by
  have hs (i : Fin 3) : L.shortRoot i = M.shortRoot i := by
    obtain ⟨a, t, c, hc, hact⟩ := short_motion n hn hlarge i
    obtain ⟨z, hz⟩ := hf (torusActor P rfl a t)
    exact hom_ext_of_scalar_equivariant n hn f hk _ _
      (MonoidHom.ext fun x => (L.project_short i x.toAdd).trans (M.project_short i x.toAdd).symm)
      z c hc (hL.1 i a t c hact z hz) (hM.1 i a t c hact z hz)
  have hl (i : Fin 3) : L.longRoot i = M.longRoot i := by
    obtain ⟨a, t, c, hc, hact⟩ := long_motion n hn hlarge i
    obtain ⟨z, hz⟩ := hf (torusActor P rfl a t)
    exact hom_ext_of_scalar_equivariant n hn f hk _ _
      (MonoidHom.ext fun x => (L.project_long i x.toAdd).trans (M.project_long i x.toAdd).symm)
      z c hc (hL.2 i a t c hact z hz) (hM.2 i a t c hact z hz)
  have hs' := funext hs
  have hl' := funext hl
  cases L
  cases M
  cases hs'
  cases hl'
  rfl

/-- The normalized six-root system is uniquely determined in the given extension. -/
theorem existsUnique_torusNormalized_of_rootPreimagesAbelian (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hab : RootPreimagesAbelian n hn f) :
    ∃! L : RootSections n hn f, L.TorusNormalized := by
  obtain ⟨L, hL⟩ := exists_torusNormalized_of_rootPreimagesAbelian n hn f hlarge hf hk hab
  exact ⟨L, hL, fun M hM => torusNormalized_unique n hn f hlarge hf hk M L hM hL⟩

/-- The preimage premise is necessary even for unnormalized additive sections. -/
theorem RootSections.rootPreimagesAbelian (L : RootSections n hn f)
    (hk : f.ker ≤ Subgroup.center E) : RootPreimagesAbelian n hn f := by
  constructor
  · intro i v w ⟨x, hx⟩ ⟨y, hy⟩
    apply commutatorElement_eq_one_iff_commute.mp
    rw [CentralExtension.commutator_eq_of_image_eq f hk
      (hx.symm.trans (L.project_short i x.toAdd).symm)
      (hy.symm.trans (L.project_short i y.toAdd).symm)]
    exact ((Commute.all x y).map (L.shortRoot i)).commutator_eq
  · intro i v w ⟨x, hx⟩ ⟨y, hy⟩
    apply commutatorElement_eq_one_iff_commute.mp
    rw [CentralExtension.commutator_eq_of_image_eq f hk
      (hx.symm.trans (L.project_long i x.toAdd).symm)
      (hy.symm.trans (L.project_long i y.toAdd).symm)]
    exact ((Commute.all x y).map (L.longRoot i)).commutator_eq

end
end Triality.Standard.CentralCovers.TwoPrimary

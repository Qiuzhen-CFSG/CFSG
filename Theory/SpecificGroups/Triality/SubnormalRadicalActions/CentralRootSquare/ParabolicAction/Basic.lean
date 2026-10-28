module

public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.Coordinates
public import Theory.SpecificGroups.Triality.FullParabolicActions.Definitions

/-!
# Full-parabolic actors on the first central triality layer

The actual pinned central SL₂ embeds through fixed points, elementary
restriction, and the central quotient. Every element of the full parabolic
factors as a radical element, a central SL₂ element, and an element of the
original two-parameter torus. Additivity of the first layer makes arbitrary
radical factors act trivially. A split-coordinate comparison retains the
faithful elementary quotient for the remaining root computations.

Source: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`), for the
central local group of Aschbacher–Smith F.1.12(I)(4), printed pp.263–264
(`refs/quasithin.pdf`). No perfectness assumption is used.
-/

@[expose] public section
noncomputable section
open Subgroup
open Triality.Standard.ConcreteBruhat
open scoped MatrixGroups Pointwise
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.LeviCommutators
namespace Triality.Standard.Parabolics.CentralRootSquare

/-- The first layer as an additive homomorphism, with its root-additivity input explicit. -/
def firstLayerHom (P : Parameters) (hp : P.prime = 2)
    (hadd : ∀ r s, firstLayer P hp (r * s) = firstLayer P hp r + firstLayer P hp s) :
    radical P .central →* Multiplicative (ExtensionField P × ExtensionField P) where
  toFun r := Multiplicative.ofAdd (firstLayer P hp r)
  map_one' := firstLayer_one P hp
  map_mul' := hadd

theorem firstLayer_inv (P : Parameters) (hp : P.prime = 2)
    (hadd : ∀ r s, firstLayer P hp (r * s) = firstLayer P hp r + firstLayer P hp s)
    (r : radical P .central) : firstLayer P hp r⁻¹ = -firstLayer P hp r :=
  (firstLayerHom P hp hadd).map_inv r

/-- Every radical factor acts trivially on this layer. -/
theorem firstLayer_conjugation_radical (P : Parameters) (hp : P.prime = 2)
    (hadd : ∀ r s, firstLayer P hp (r * s) = firstLayer P hp r + firstLayer P hp s)
    (x r : radical P .central) :
    firstLayer P hp (conjugation P ⟨x.val, radical_le_parabolic P .central x.property⟩ r) =
      firstLayer P hp r := by
  have he : conjugation P ⟨x.val, radical_le_parabolic P .central x.property⟩ r =
      x * r * x⁻¹ := rfl
  rw [he, hadd, hadd, firstLayer_inv P hp hadd]
  abel

private theorem lift_conjugation {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (k : G →* K) (hf : Function.Injective f) (x y z : G)
    (he : f z = f x * f y * (f x)⁻¹) : k z = k x * k y * (k x)⁻¹ := by
  have he' : z = x * y * x⁻¹ := hf (he.trans (by simp only [map_mul, map_inv]))
  simpa only [map_mul, map_inv] using congrArg k he'

/-- Compare conjugation with the split root normal form before the faithful
central quotient. This keeps the actual elementary lift visible. -/
theorem conjugation_coordinates_split (P : Parameters) (hp : P.prime = 2)
    (x : ElementaryGroup P) (hx : toCarrier P x ∈ parabolic P .central)
    (r : radical P .central) :
    PositiveCoordinates.orderedProduct P
        (PositiveCoordinates.expand P (extendOrbit P .central
          ((coordinates P hp).symm (conjugation P ⟨toCarrier P x, hx⟩ r)))) =
      elementaryInclusion P x *
        PositiveCoordinates.orderedProduct P
          (PositiveCoordinates.expand P (extendOrbit P .central ((coordinates P hp).symm r))) *
        (elementaryInclusion P x)⁻¹ := by
  have hr : toCarrier P (rootElement P hp .central ((coordinates P hp).symm r)) = r.val :=
    congrArg Subtype.val ((coordinates P hp).apply_symm_apply r)
  have hc : toCarrier P (rootElement P hp .central
      ((coordinates P hp).symm (conjugation P ⟨toCarrier P x, hx⟩ r))) =
      toCarrier P x * r.val * (toCarrier P x)⁻¹ :=
    congrArg Subtype.val ((coordinates P hp).apply_symm_apply _)
  exact lift_conjugation (toCarrier P) (elementaryInclusion P)
    (ElementaryCentralKernel.toCarrier_injective P hp) x
    (rootElement P hp .central ((coordinates P hp).symm r))
    (rootElement P hp .central
      ((coordinates P hp).symm (conjugation P ⟨toCarrier P x, hx⟩ r)))
    (hc.trans (congrArg (fun z => toCarrier P x * z * (toCarrier P x)⁻¹) hr.symm))

/-- The central pinned embedding, restricted to the genuine fixed group. -/
def centralFixed (P : Parameters) (hp : P.prime = 2) :
    SL(2, GaloisField P.prime P.exponent) →* fixedSubgroup P :=
  ((pinnedRankOneMaps P hp).centralFixedEmbedding).codRestrict (fixedSubgroup P)
    (fun A => ((pinnedRankOneMaps P hp).range_centralFixedEmbedding.le ⟨A, rfl⟩).2)

/-- Elementary descent of the central pinned SL₂; no perfectness is used. -/
def centralElementary (P : Parameters) (hp : P.prime = 2) :
    SL(2, GaloisField P.prime P.exponent) →* ElementaryGroup P := by
  let : CharP (GaloisField P.prime P.exponent) 2 :=
    hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
  exact sl2ElementaryLift P hp (centralFixed P hp)

theorem centralElementary_val (P : Parameters) (hp : P.prime = 2)
    (A : SL(2, GaloisField P.prime P.exponent)) :
    elementaryInclusion P (centralElementary P hp A) =
      (pinnedRankOneMaps P hp).hom 1 (sl2BaseEmbedding P A) := rfl

/-- The actual central rank-one actor in the full parabolic. -/
def centralActor (P : Parameters) (hp : P.prime = 2) :
    SL(2, GaloisField P.prime P.exponent) →* parabolic P .central :=
  ((toCarrier P).comp (centralElementary P hp)).codRestrict (parabolic P .central)
    (fun A => levi_le_parabolic P .central
      ⟨centralElementary P hp A,
        ((pinnedRankOneMaps P hp).range_centralFixedEmbedding.le ⟨A, rfl⟩).1, rfl⟩)

theorem centralActor_val (P : Parameters) (hp : P.prime = 2)
    (A : SL(2, GaloisField P.prime P.exponent)) :
    (centralActor P hp A).val = toCarrier P (centralElementary P hp A) := rfl

theorem range_centralActor (P : Parameters) (hp : P.prime = 2) :
    (centralActor P hp).range = (levi P .central).subgroupOf (parabolic P .central) := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    exact ⟨centralElementary P hp A,
      ((pinnedRankOneMaps P hp).range_centralFixedEmbedding.le ⟨A, rfl⟩).1, rfl⟩
  · rintro g ⟨x, hx, hxg⟩
    obtain ⟨A, hA⟩ := (pinnedRankOneMaps P hp).range_centralFixedEmbedding.ge
      ⟨hx, x.val.property⟩
    refine ⟨A, Subtype.ext ?_⟩
    rw [centralActor_val]
    have he : centralElementary P hp A = x :=
      elementaryInclusion_injective P hA
    exact (congrArg (toCarrier P) he).trans hxg

/-- The full two-parameter torus, retained in the parabolic. -/
def torusActor (P : Parameters) (hp : P.prime = 2)
    (a : ConcreteBruhat.TorusCoordinates.OrbitParameters P) : parabolic P .central :=
  ⟨(ConcreteBruhat.TorusCoordinates.torusMulEquiv P hp a).val,
    (fullLevi_le_parabolic P .central)
      (by
        rw [fullLevi_eq P hp .central]
        exact mem_sup_right (ConcreteBruhat.TorusCoordinates.torusMulEquiv P hp a).property)⟩

theorem torusActor_val (P : Parameters) (hp : P.prime = 2)
    (a : ConcreteBruhat.TorusCoordinates.OrbitParameters P) :
    (torusActor P hp a).val =
      toCarrier P (ConcreteBruhat.TorusCoordinates.orbitElementary P hp a) := rfl

/-- A full parabolic element has a radical factor, an actual central SL₂
factor, and both original torus parameters. -/
theorem parabolic_factorization (P : Parameters) (hp : P.prime = 2)
    (g : parabolic P .central) :
    ∃ r : radical P .central, ∃ A : SL(2, GaloisField P.prime P.exponent),
      ∃ a : ConcreteBruhat.TorusCoordinates.OrbitParameters P,
      g = ⟨r.val, radical_le_parabolic P .central r.property⟩ *
        centralActor P hp A * torusActor P hp a := by
  have hR : fullLevi P .central ≤ normalizer (radical P .central) :=
    fullLevi_le_normalizer_radical P .central
  have hmul : (parabolic P .central : Set (Carrier P)) =
      (radical P .central : Set (Carrier P)) * fullLevi P .central := by
    rw [parabolic_eq_radical_sup_fullLevi P hp .central]
    exact coe_mul_of_right_le_normalizer_left _ _ hR
  obtain ⟨r, hr, l, hl, hrl⟩ := (Set.ext_iff.mp hmul g.val).mp g.property
  have hmulL : (fullLevi P .central : Set (Carrier P)) =
      (levi P .central : Set (Carrier P)) * torus P := by
    rw [fullLevi_eq P hp .central]
    exact coe_mul_of_right_le_normalizer_left _ _ (torus_le_normalizer_levi P hp .central)
  obtain ⟨k, hk, t, ht, hkt⟩ := (Set.ext_iff.mp hmulL l).mp hl
  obtain ⟨A, hA⟩ := (range_centralActor P hp).ge
    (show (⟨k, levi_le_parabolic P .central hk⟩ : parabolic P .central) ∈
      (levi P .central).subgroupOf (parabolic P .central) from hk)
  obtain ⟨a, ha⟩ := (ConcreteBruhat.TorusCoordinates.torusMulEquiv P hp).surjective ⟨t, ht⟩
  refine ⟨⟨r, hr⟩, A, a, Subtype.ext ?_⟩
  change g.val = r * (centralActor P hp A).val * (torusActor P hp a).val
  rw [congrArg Subtype.val hA]
  change g.val = r * k * (ConcreteBruhat.TorusCoordinates.torusMulEquiv P hp a).val
  rw [ha]
  exact (hrl.symm.trans (congrArg (r * ·) hkt.symm)).trans (mul_assoc r k t).symm

end Triality.Standard.Parabolics.CentralRootSquare
end

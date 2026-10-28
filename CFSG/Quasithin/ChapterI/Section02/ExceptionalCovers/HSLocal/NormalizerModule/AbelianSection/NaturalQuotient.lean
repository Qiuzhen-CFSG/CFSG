module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.ModelInput
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.CentralLine
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Action

/-!
# The natural quotient of the abelian HS Frattini module

Squaring in the actual model core `C₄³` maps onto its marked omega subgroup,
`baseElementary`. Pull this map back through the original cover map, and
factor it through `coreMap`. The explicit image-of-E premise identifies the
kernel with the literal image of the covering center. Consequently the
quotient by `centralLine` is linearly isomorphic to the actual elementary
eight, equivariantly for normalizer conjugation.

Choose one basis of that elementary eight and use the same basis to construct
both vector coordinates and the actor equivalence with SL₃(2). Two elementary
matrices show that the natural quotient has no nonzero fixed vectors; hence
the central line is exactly the invariant space. Disjointness of E and the
central factor gives dimension one. `natural_central_quotient` assembles these
results with the existing faithfulness and four-dimensionality theorems.

The abelianness and Frattini premises remain explicit for the HS source
assembly to discharge. No nonsplitting or indecomposability premise is used.
All original central, Frattini, and actor maps are preserved.

Source: Aschbacher–Smith, I.2.2(5), final HS paragraph, printed p.412 / PDF
p.423; the natural-central-quotient hypothesis of B.4.8(2), p.91 / PDF p.102.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open Sporadic.LeechRelated.HS.BlockNormalizer
open Sporadic.LeechRelated.HS.EvenLocalCandidates
namespace NaturalQuotient

local instance base_elementary : IsElementaryAbelian 2 baseElementary :=
  elementary_isElementaryAbelian 2

variable (d : AbelianSection.ModelInput)

include d in
private theorem model_commutative : IsMulCommutative (pCore 2 baseNormalizer) :=
  ⟨⟨fun a b => d.coordinates.injective (by simp only [map_mul, mul_comm])⟩⟩

include d in
private theorem model_fourth (q : pCore 2 baseNormalizer) : q ^ 4 = 1 := by
  apply d.coordinates.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  ext i
  change 4 • (d.coordinates q).toAdd i = 0
  exact (by decide : ∀ a : ZMod 4, 4 • a = 0) _

include d in
/-- In the model abelian core, omega is exactly the square-one subgroup. -/
theorem model_omega_iff (q : pCore 2 baseNormalizer) :
    q ∈ omega (pCore 2 baseNormalizer) (p := 2) 1 ↔ q ^ 2 = 1 := by
  let := model_commutative d
  let := IsElementaryAbelian.omega₁_of_isMulCommutative (p := 2) (pCore 2 baseNormalizer)
  constructor
  · intro hq
    exact elemPow_eq_one_of_isElementaryAbelian q hq
  · intro hq
    exact subset_closure (by simpa using hq)

include d in
/-- Every model square lies in the original marked elementary subgroup. -/
theorem model_square_mem (q : pCore 2 baseNormalizer) :
    ((q : baseNormalizer) : Sporadic.LeechRelated.HS.Carrier) ^ 2 ∈ baseElementary := by
  rw [← d.omega_image]
  have hx : q ^ 2 ∈ omega (pCore 2 baseNormalizer) (p := 2) 1 :=
    (model_omega_iff d _).mpr (by rw [← pow_mul]; exact model_fourth d q)
  exact mem_map_of_mem _ (mem_map_of_mem _ hx)

include d in
/-- Every element of the marked elementary eight is an actual model square. -/
theorem model_square_surjective (a : baseElementary) :
    ∃ q : pCore 2 baseNormalizer,
      ((q : baseNormalizer) : Sporadic.LeechRelated.HS.Carrier) ^ 2 = a := by
  have ha := (le_of_eq d.omega_image.symm) a.property
  obtain ⟨b, ⟨x, hx, rfl⟩, hxa⟩ := ha
  have hx2 := (model_omega_iff d x).mp hx
  have hcoord : ∀ i, 2 • (d.coordinates x).toAdd i = 0 := by
    intro i
    have h := congrArg (fun y => (d.coordinates y).toAdd i) hx2
    simpa using h
  have hs : ∀ a : ZMod 4, 2 • a = 0 → ∃ b : ZMod 4, 2 • b = a := by decide
  choose v hv using fun i => hs _ (hcoord i)
  refine ⟨d.coordinates.symm (Multiplicative.ofAdd v), ?_⟩
  have hp : (d.coordinates.symm (Multiplicative.ofAdd v)) ^ 2 = x := by
    apply d.coordinates.injective
    rw [map_pow, d.coordinates.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    ext i
    exact hv i
  have he := congrArg (fun y : pCore 2 baseNormalizer =>
    ((y : baseNormalizer) : Sporadic.LeechRelated.HS.Carrier)) hp
  exact he.trans hxa

variable {K : Type*} [Group K] [Finite K]
variable (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
variable (hZ : Nat.card (center K) = 2)

/-- Restriction of the original local covering map to the two-cores. -/
def coreModelMap : Q e →* pCore 2 baseNormalizer :=
  ((localMap e).comp (Q e).subtype).codRestrict _ (fun q => by
    rw [← Q_map_localMap e hZ]
    exact mem_map_of_mem _ q.property)

theorem coreModelMap_surjective : Function.Surjective (coreModelMap e hZ) := by
  intro a
  have ha : (a : baseNormalizer) ∈ (Q e).map (localMap e) := by
    rw [Q_map_localMap e hZ]; exact a.property
  obtain ⟨q, hq, he⟩ := ha
  exact ⟨⟨q, hq⟩, Subtype.ext he⟩

variable [IsMulCommutative (Q e)]

/-- The literal square of the image under the original map to HS. -/
def squareMap : Q e →* baseElementary where
  toFun q := ⟨modelMap e (q : K) ^ 2, model_square_mem d (coreModelMap e hZ q)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change modelMap e ((a * b : Q e) : K) ^ 2 = _
    have he := congrArg (fun q : Q e => modelMap e (q : K)) (mul_pow a b 2)
    simpa only [map_mul, map_pow, coe_mul, coe_pow] using he

theorem squareMap_val (q : Q e) :
    (squareMap d e hZ q : Sporadic.LeechRelated.HS.Carrier) = modelMap e (q : K) ^ 2 := rfl

theorem squareMap_surjective : Function.Surjective (squareMap d e hZ) := by
  intro a
  obtain ⟨q, hq⟩ := model_square_surjective d a
  obtain ⟨x, rfl⟩ := coreModelMap_surjective e hZ q
  exact ⟨x, Subtype.ext hq⟩

variable (himage : ((E e).map (localMap e)).map baseNormalizer.subtype = baseElementary)

include himage in
/-- The given E-image premise makes the square map descend through coreMap. -/
theorem coreMap_ker_le_squareMap_ker : (coreMap e).ker ≤ (squareMap d e hZ).ker := by
  intro q hq
  have hE : (q : M e) ∈ E e :=
    (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hq)
  have he : modelMap e (q : K) ∈ baseElementary := by
    rw [← himage]
    exact mem_map_of_mem _ (mem_map_of_mem _ hE)
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian _ he

/-- The square map on the embedded Frattini quotient, induced by coreMap. -/
noncomputable def squareDescent : Qbar e →* baseElementary :=
  (coreMap e).liftOfSurjective (coreMap_surjective e)
    ⟨squareMap d e hZ, coreMap_ker_le_squareMap_ker d e hZ himage⟩

theorem squareDescent_coreMap (q : Q e) :
    squareDescent d e hZ himage (coreMap e q) = squareMap d e hZ q :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem squareDescent_surjective : Function.Surjective (squareDescent d e hZ himage) := by
  intro a
  obtain ⟨q, hq⟩ := squareMap_surjective d e hZ a
  exact ⟨coreMap e q, (squareDescent_coreMap d e hZ himage q).trans hq⟩

/-- The descended square map kills exactly the literal central image. -/
theorem squareDescent_eq_one_iff (v : Qbar e) :
    squareDescent d e hZ himage v = 1 ↔ v ∈ (centralFrattiniMap e hZ).range := by
  obtain ⟨q, rfl⟩ := coreMap_surjective e v
  rw [squareDescent_coreMap]
  constructor
  · intro hq
    have hq2 : (coreModelMap e hZ q) ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a : baseElementary => (a : Sporadic.LeechRelated.HS.Carrier)) hq
    have hqomega := (model_omega_iff d _).mpr hq2
    have hqelem : modelMap e (q : K) ∈ baseElementary := by
      rw [← d.omega_image]
      exact mem_map_of_mem _ (mem_map_of_mem _ hqomega)
    rw [← himage] at hqelem
    obtain ⟨b, ⟨t, ht, rfl⟩, htq⟩ := hqelem
    have hlocal : localMap e t = localMap e (q : M e) := Subtype.ext htq
    let z : M e := (q : M e) * t⁻¹
    have hz : z ∈ centralFactor e := by
      change z ∈ (center K).subgroupOf (M e)
      rw [← localMap_ker]
      change localMap e z = 1
      simp only [z, map_mul, map_inv, hlocal, mul_inv_cancel]
    refine ⟨⟨(z : K), hz⟩, ?_⟩
    apply Subtype.ext
    rw [centralFrattiniMap_val, coreMap_val]
    change QuotientGroup.mk' (E e) z = QuotientGroup.mk' (E e) (q : M e)
    have ht1 : QuotientGroup.mk' (E e) t = 1 := (QuotientGroup.eq_one_iff t).mpr ht
    simp only [z, map_mul, map_inv, ht1, inv_one, mul_one]
  · rintro ⟨z, hz⟩
    have hsz : squareDescent d e hZ himage (centralFrattiniMap e hZ z) = 1 := by
      change squareDescent d e hZ himage (coreMap e
        ⟨⟨z, center_le_M e z.property⟩, center_le_Q e hZ z.property⟩) = 1
      rw [squareDescent_coreMap]
      apply Subtype.ext
      have hzker : modelMap e (z : K) = 1 := by
        change (z : K) ∈ (modelMap e).ker
        rw [modelMap_ker]
        exact z.property
      change modelMap e (z : K) ^ 2 = 1
      rw [hzker, one_pow]
    rw [hz, squareDescent_coreMap] at hsz
    exact hsz

/-- The descended square map with the canonical binary linear structures. -/
noncomputable def squareLinear : Additive (Qbar e) →ₗ[ZMod 2] Additive baseElementary :=
  (squareDescent d e hZ himage).toAdditive.toZModLinearMap 2

theorem squareLinear_ker : (squareLinear d e hZ himage).ker = centralLine e hZ := by
  ext v
  exact squareDescent_eq_one_iff d e hZ himage v.toMul

theorem squareLinear_surjective : Function.Surjective (squareLinear d e hZ himage) := by
  intro a
  obtain ⟨v, hv⟩ := squareDescent_surjective d e hZ himage a.toMul
  exact ⟨Additive.ofMul v, congrArg Additive.ofMul hv⟩

/-- Conjugation commutes with the descended square map for the actual quotient actors. -/
theorem squareLinear_equivariant (a : M e ⧸ Q e) (v : Additive (Qbar e)) :
    squareLinear d e hZ himage (frattiniRepresentation e a v) =
      Additive.ofMul ((QuotientGroup.lift (Q e) (normalizerAction e)
        (normalizerAction_ker e hZ ▸ le_refl _)) a
          (squareLinear d e hZ himage v).toMul) := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Q e) a
  obtain ⟨q, hq⟩ := coreMap_surjective e v.toMul
  have hv : v = Additive.ofMul (coreMap e q) := congrArg Additive.ofMul hq.symm
  rw [hv, frattiniRepresentation_coreMap]
  apply Additive.toMul.injective
  change squareDescent d e hZ himage (coreMap e (MulAut.conjNormal m q)) =
    normalizerAction e m (squareDescent d e hZ himage (coreMap e q))
  rw [squareDescent_coreMap, squareDescent_coreMap]
  apply Subtype.ext
  change modelMap e ((m : K) * (q : K) * (m : K)⁻¹) ^ 2 =
    modelMap e (m : K) * (modelMap e (q : K) ^ 2) * (modelMap e (m : K))⁻¹
  rw [map_mul, map_mul, map_inv, conj_pow]

/-- The induced action on the quotient by the literal central line, using its fixedness. -/
noncomputable def quotientRepresentation :
    Representation (ZMod 2) (M e ⧸ Q e) (Additive (Qbar e) ⧸ centralLine e hZ) :=
  (frattiniRepresentation e).quotient (centralLine e hZ) (fun a v hv => by
    change frattiniRepresentation e a v ∈ centralLine e hZ
    rw [(Representation.mem_invariants _ _).mp (centralLine_le_invariants e hZ hv) a]
    exact hv)

/-- The first isomorphism theorem applied to the descended square map. -/
noncomputable def quotientToElementary :
    (Additive (Qbar e) ⧸ centralLine e hZ) ≃ₗ[ZMod 2] Additive baseElementary :=
  (Submodule.quotEquivOfEq _ _ (squareLinear_ker d e hZ himage).symm).trans
    ((squareLinear d e hZ himage).quotKerEquivOfSurjective
      (squareLinear_surjective d e hZ himage))

theorem quotientToElementary_mk (v : Additive (Qbar e)) :
    quotientToElementary d e hZ himage (Submodule.Quotient.mk v) =
      squareLinear d e hZ himage v := rfl

omit [IsMulCommutative (Q e)] in
/-- Disjointness of E and the relative center makes the central Frattini map injective. -/
theorem centralFrattiniMap_injective (hdisj : Disjoint (E e) (centralFactor e)) :
    Function.Injective (centralFrattiniMap e hZ) := by
  apply (centralFrattiniMap e hZ).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro z hz
  have hE : (⟨z, center_le_M e z.property⟩ : M e) ∈ E e := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg (fun v : Qbar e => (v : M e ⧸ E e)) hz
  have he := disjoint_def.mp hdisj hE z.property
  apply Subtype.ext
  exact congrArg (fun m : M e => (m : K)) he

omit [IsMulCommutative (Q e)] in
/-- The literal central image is one-dimensional because the center has order two. -/
theorem centralLine_finrank (hdisj : Disjoint (E e) (centralFactor e)) :
    Module.finrank (ZMod 2) (centralLine e hZ) = 1 := by
  have hc : Nat.card (centralLine e hZ) = 2 := by
    have h := Nat.card_congr
      (MonoidHom.ofInjective (centralFrattiniMap_injective e hZ hdisj)).toEquiv
    change Nat.card (centralLine e hZ) = 2
    exact h.symm.trans hZ
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := centralLine e hZ)
  rw [hc, Nat.card_zmod] at hpow
  exact Nat.pow_right_injective (by decide : 1 < 2) hpow.symm

/-- The binary structure is the one on the actual marked elementary eight. -/
theorem base_finrank : Module.finrank (ZMod 2) (Additive baseElementary) = 3 := by
  have hp := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive baseElementary)
  change Nat.card baseElementary = _ at hp
  rw [baseElementary_card, Nat.card_zmod] at hp
  exact Nat.pow_right_injective (by decide : 1 < 2) hp.symm

/-- One chosen basis used simultaneously for vectors and actors. -/
noncomputable def baseBasis : Module.Basis (Fin 3) (ZMod 2) (Additive baseElementary) :=
  Module.finBasisOfFinrankEq (ZMod 2) (Additive baseElementary) base_finrank

/-- Coordinates on the actual elementary eight in the chosen basis. -/
noncomputable def baseCoordinates : Additive baseElementary ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  baseBasis.equivFun

/-- The canonical conversion from group automorphisms to binary linear automorphisms. -/
def baseAutLinear : MulAut baseElementary ≃* (Additive baseElementary ≃ₗ[ZMod 2] Additive baseElementary) where
  toFun aut := { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
  invFun aut := MulEquiv.toAdditive.symm aut.toAddEquiv
  left_inv := by intro aut; ext; rfl
  right_inv := by intro aut; ext; rfl
  map_mul' := by intro aut other; ext; rfl

/-- The actor coordinates determined by baseCoordinates; the original baseAutomorphismEquiv is unchanged. -/
noncomputable def compatibleBaseActor :
    MulAut baseElementary ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  baseAutLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive baseElementary)).symm.trans
      ((Matrix.GeneralLinearGroup.toLin' baseBasis).symm.trans Matrix.PSL3Two.equivGL.symm))

/-- The chosen vector and actor coordinates satisfy the natural matrix action equation. -/
theorem compatibleBaseActor_intertwines (a : MulAut baseElementary) (v : Additive baseElementary) :
    baseCoordinates (Additive.ofMul (a v.toMul)) =
      (compatibleBaseActor a : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ baseCoordinates v := by
  have he : (Matrix.GeneralLinearGroup.toLin' baseBasis
      (Matrix.PSL3Two.equivGL (compatibleBaseActor a))).toLinearEquiv = baseAutLinear a := by
    simp only [compatibleBaseActor, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have hh := Matrix.GeneralLinearGroup.toLin'_apply baseBasis
    (Matrix.PSL3Two.equivGL (compatibleBaseActor a)) v
  rw [he] at hh
  have hc := congrArg baseCoordinates hh
  simp only [baseCoordinates, Matrix.PSL3Two.equivGL_apply,
    ← Module.Basis.equivFun_apply, Fintype.linearCombination_apply,
    ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply] at hc
  exact hc

/-- The compatible actor equivalence, induced by the actual normalizer action. -/
noncomputable def actorEquiv : (M e ⧸ Q e) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq (normalizerAction_ker e hZ).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (normalizerAction e)
      (normalizerAction_surjective e)).trans compatibleBaseActor)

omit [IsMulCommutative (Q e)] in
theorem actorEquiv_mk (m : M e) :
    actorEquiv e hZ (QuotientGroup.mk' (Q e) m) = compatibleBaseActor (normalizerAction e m) := rfl

/-- Actual coordinates on the quotient of Qbar by the literal central line. -/
noncomputable def quotientCoordinates :
    (Additive (Qbar e) ⧸ centralLine e hZ) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  (quotientToElementary d e hZ himage).trans baseCoordinates

theorem quotientCoordinates_coreMap (q : Q e) :
    quotientCoordinates d e hZ himage (Submodule.Quotient.mk (Additive.ofMul (coreMap e q))) =
      baseCoordinates (Additive.ofMul (squareMap d e hZ q)) := by
  change baseCoordinates (Additive.ofMul (squareDescent d e hZ himage (coreMap e q))) = _
  rw [squareDescent_coreMap]

/-- Full equivariance of the quotient coordinates with the natural SL₃(2) action. -/
theorem quotientCoordinates_intertwines (a : M e ⧸ Q e)
    (v : Additive (Qbar e) ⧸ centralLine e hZ) :
    quotientCoordinates d e hZ himage (quotientRepresentation e hZ a v) =
      (actorEquiv e hZ a : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        quotientCoordinates d e hZ himage v := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Q e) a
  obtain ⟨w, rfl⟩ := (centralLine e hZ).mkQ_surjective v
  change baseCoordinates (squareLinear d e hZ himage
    (frattiniRepresentation e (QuotientGroup.mk' (Q e) m) w)) = _
  rw [squareLinear_equivariant]
  exact compatibleBaseActor_intertwines (normalizerAction e m) _

private theorem natural_fixed_eq_zero (v : Fin 3 → ZMod 2)
    (hv : ∀ a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      (a : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v) : v = 0 := by
  have h : ∀ w : Fin 3 → ZMod 2,
      (!![1, 1, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w = w →
      (!![1, 0, 0; 0, 1, 0; 1, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w = w → w = 0 := by
    decide
  exact h v (hv ⟨_, by decide⟩) (hv ⟨_, by decide⟩)

include d himage in
/-- The natural quotient has no nonzero fixed vector. -/
theorem quotient_invariants_eq_bot : (quotientRepresentation e hZ).invariants = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  apply (quotientCoordinates d e hZ himage).injective
  rw [map_zero]
  apply natural_fixed_eq_zero
  intro a
  obtain ⟨b, rfl⟩ := (actorEquiv e hZ).surjective a
  rw [← quotientCoordinates_intertwines]
  rw [(Representation.mem_invariants _ _).mp hv b]

include d himage in
/-- The original central image is the whole invariant subspace. -/
theorem centralLine_eq_invariants : centralLine e hZ = (frattiniRepresentation e).invariants := by
  apply le_antisymm (centralLine_le_invariants e hZ)
  intro v hv
  apply (Submodule.Quotient.mk_eq_zero _).mp
  have hmem : (Submodule.Quotient.mk v : Additive (Qbar e) ⧸ centralLine e hZ) ∈
      (quotientRepresentation e hZ).invariants := by
    apply (Representation.mem_invariants _ _).mpr
    intro a
    change Submodule.Quotient.mk (frattiniRepresentation e a v) = Submodule.Quotient.mk v
    rw [(Representation.mem_invariants _ _).mp hv a]
  rw [quotient_invariants_eq_bot d e hZ himage] at hmem
  exact hmem

/-- The representative formula in the original HS carrier, without auxiliary action tags. -/
theorem quotientCoordinates_coreMap_square (q : Q e) :
    ((baseCoordinates.symm (quotientCoordinates d e hZ himage
      (Submodule.Quotient.mk (Additive.ofMul (coreMap e q))))).toMul :
        Sporadic.LeechRelated.HS.Carrier) = modelMap e (q : K) ^ 2 := by
  rw [quotientCoordinates_coreMap, baseCoordinates.symm_apply_apply]
  rfl

/-- All inputs to the natural-central-quotient step of B.4.8(2), on the literal
cover section and its existing action. The source assembly supplies the
independent Frattini premises; nonsplitting is not assumed or asserted here. -/
theorem natural_central_quotient
    (hdisj : Disjoint (E e) (centralFactor e)) (hE : Nat.card (E e) = 8) :
    centralLine e hZ = (frattiniRepresentation e).invariants ∧
    Module.finrank (ZMod 2) (centralLine e hZ) = 1 ∧
    Module.finrank (ZMod 2) (Additive (Qbar e)) = 4 ∧
    Function.Injective (frattiniRepresentation e) ∧
    (∀ a v, quotientCoordinates d e hZ himage (quotientRepresentation e hZ a v) =
      (actorEquiv e hZ a : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        quotientCoordinates d e hZ himage v) ∧
    (∀ q : Q e,
      ((baseCoordinates.symm (quotientCoordinates d e hZ himage
        (Submodule.Quotient.mk (Additive.ofMul (coreMap e q))))).toMul :
          Sporadic.LeechRelated.HS.Carrier) = modelMap e (q : K) ^ 2) :=
  ⟨centralLine_eq_invariants d e hZ himage, centralLine_finrank e hZ hdisj,
    frattiniRepresentation_finrank e hZ hE, frattiniRepresentation_injective e hZ,
    quotientCoordinates_intertwines d e hZ himage,
    quotientCoordinates_coreMap_square d e hZ himage⟩

end NaturalQuotient
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal

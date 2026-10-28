module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.Inputs
public import Theory.AlgebraicGroup.Jordan.FiniteOrder

/-!
# Passage between the three D4 conjugacy relations

Odd-order elements of the finite graph-field group are semisimple in the
ambient algebraic group. Counting their ambient classes counts their finite
classes only after proving that ambient conjugacy descends to fixed points.
The elementary subgroup requires a further generation theorem.

This module proves the counting transfers and the group-theoretic part of
conjugacy descent: a Lang solution in the centralizer corrects an ambient
conjugator to a fixed conjugator. Generation, centralizer Lang surjectivity,
and the torus/Weyl count remain explicit geometric obligations.

Sources: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 12.4--12.5 and
14.8; GLS3, Theorem 2.8.2.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound

open Theory.AlgebraicGroup

private theorem card_classes_image {G H : Type*} [Group G] [Group H]
    (f : G →* H) (s : Set G)
    (hf : ∀ x ∈ s, ∀ y ∈ s, IsConj (f x) (f y) → IsConj x y) :
    Nat.card (ConjClasses.mk '' s) =
      Nat.card ((fun x => ConjClasses.mk (f x)) '' s) := by
  have hinj : Set.InjOn (ConjClasses.map f) (ConjClasses.mk '' s) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr
      (hf x hx y hy (ConjClasses.mk_eq_mk_iff_isConj.mp h))
  have himage : ConjClasses.map f '' (ConjClasses.mk '' s) =
      (fun x => ConjClasses.mk (f x)) '' s := by
    rw [Set.image_image]
    rfl
  rw [← himage]
  exact (Nat.card_image_of_injOn hinj).symm

private theorem card_oddClasses_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) :
    Nat.card (ConjClasses.mk '' {g : G | ¬ 2 ∣ orderOf g}) =
      Nat.card (ConjClasses.mk '' {h : H | ¬ 2 ∣ orderOf h}) := by
  rw [card_classes_image e.toMonoidHom _ (by
    intro x _ y _ h
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      e.symm.toMonoidHom.map_isConj h)]
  have himage : (fun x => ConjClasses.mk (e x)) '' {g : G | ¬ 2 ∣ orderOf g} =
      ConjClasses.mk '' {h : H | ¬ 2 ∣ orderOf h} := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e x, by simpa only [Set.mem_ofPred_eq, e.orderOf_eq] using hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨e.symm y, ?_, ?_⟩
      · simpa only [Set.mem_ofPred_eq, e.symm.orderOf_eq] using hy
      · simp
  exact congrArg (fun s : Set (ConjClasses H) => Nat.card s) himage

/-- The conjugator correction in Steinberg 12.5. If `z` conjugates fixed
points, `z⁻¹ σ(z)` centralizes the first point. A Lang solution there makes
`z c` a fixed conjugator. The existence of that solution is an explicit input. -/
theorem isConj_fixed_of_centralizer_lang {G : Type*} [Group G]
    (σ : G →* G) (x y : MonoidHom.eqLocus σ (MonoidHom.id G))
    (hLang : ∀ a : G, Commute a (x : G) →
      ∃ c : G, Commute c (x : G) ∧ c * (σ c)⁻¹ = a)
    (hxy : IsConj (x : G) (y : G)) : IsConj x y := by
  obtain ⟨z, hz⟩ := isConj_iff.mp hxy
  have hx : σ (x : G) = x := x.property
  have hy : σ (y : G) = y := y.property
  have hσz : σ z * (x : G) * (σ z)⁻¹ = z * (x : G) * z⁻¹ := by
    calc
      _ = (y : G) := by simpa only [map_mul, map_inv, hx, hy] using congrArg σ hz
      _ = _ := hz.symm
  have ha : Commute (z⁻¹ * σ z) (x : G) := by
    change (z⁻¹ * σ z) * (x : G) = (x : G) * (z⁻¹ * σ z)
    calc
      _ = z⁻¹ * (σ z * (x : G) * (σ z)⁻¹) * σ z := by group
      _ = z⁻¹ * (z * (x : G) * z⁻¹) * σ z := by rw [hσz]
      _ = _ := by group
  obtain ⟨c, hc, hcσ⟩ := hLang (z⁻¹ * σ z) ha
  have hfixed : σ (z * c) = z * c := by
    calc
      _ = σ z * σ c := map_mul σ z c
      _ = z * (z⁻¹ * σ z) * σ c := by group
      _ = z * (c * (σ c)⁻¹) * σ c := by rw [hcσ]
      _ = _ := by group
  apply isConj_iff.mpr
  refine ⟨⟨z * c, hfixed⟩, Subtype.ext ?_⟩
  change z * c * (x : G) * (z * c)⁻¹ = (y : G)
  calc
    _ = z * (c * (x : G)) * c⁻¹ * z⁻¹ := by group
    _ = z * ((x : G) * c) * c⁻¹ * z⁻¹ := by rw [hc.eq]
    _ = z * (x : G) * z⁻¹ := by group
    _ = _ := hz

universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The point endomorphism defining the fixed group, with graph applied first. -/
def graphFieldEnd (S : Geometry K) (n : ℕ) : Monoid.End (Variety.Point K) :=
  let φ : Monoid.End (Variety.Point K) := S.frobenius.onPoints
  (φ ^ n).comp S.diagram.toMulEquiv.toMonoidHom

/-- Ambient classes represented by odd-order fixed points. These are classes
in the algebraic point group, not in the fixed or elementary subgroup. -/
def fixedAmbientOddClasses (S : Geometry K) (n : ℕ) : Set (ConjClasses (Variety.Point K)) :=
  (fun g : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n =>
    ConjClasses.mk (g : Variety.Point K)) '' {g | ¬ 2 ∣ orderOf g}

/-- The part of Steinberg 14.8(a) needed for the upper bound. -/
def AmbientClassBound (S : Geometry K) (n : ℕ) : Prop :=
  Nat.card (fixedAmbientOddClasses S n) ≤ (2 ^ n) ^ 4

/-- Steinberg 12.5 for odd-order points of the actual graph-field group.
This implication must be proved before using ambient class counts. -/
def OddClassFusion (S : Geometry K) (n : ℕ) : Prop :=
  ∀ x y : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n,
    ¬ 2 ∣ orderOf x → ¬ 2 ∣ orderOf y →
      IsConj (x : Variety.Point K) (y : Variety.Point K) → IsConj x y

/-- Lang surjectivity on each odd-order fixed point's actual centralizer.
The endomorphism is graph followed by the `n`th ordinary Frobenius. -/
def OddCentralizerLang (S : Geometry K) (n : ℕ) : Prop :=
  ∀ x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n,
    ¬ 2 ∣ orderOf x → ∀ a : Variety.Point K, Commute a (x : Variety.Point K) →
      ∃ c : Variety.Point K, Commute c (x : Variety.Point K) ∧
        c * (graphFieldEnd S n c)⁻¹ = a

/-- The ambient image is finite for positive exponents, independently of any
conjugacy descent or numerical bound. -/
theorem fixedAmbientOddClasses_finite (S : Geometry K) (n : ℕ) (hn : 0 < n) :
    (fixedAmbientOddClasses S n).Finite := by
  let := S.fixed_finite n hn
  exact (Set.toFinite _).image _

/-- Odd-order fixed points are semisimple in the actual algebraic group. -/
theorem fixed_odd_isSemisimple (S : Geometry K) (n : ℕ) (hn : 0 < n)
    (x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n)
    (hx : ¬ 2 ∣ orderOf x) : IsSemisimpleElement K (x : Variety.Point K) := by
  let := S.fixed_finite n hn
  apply finiteOrder_coprimeChar_implies_semisimple (x : Variety.Point K)
    (orderOf x) (orderOf_pos x)
  · simpa only [ringChar.eq k 2] using hx
  · exact congrArg Subtype.val (pow_orderOf_eq_one x)

/-- Each counted ambient class has a semisimple representative and is fixed
by the graph-field map, as required by Steinberg 14.8(a). -/
theorem mem_fixedAmbientOddClasses_spec (S : Geometry K) (n : ℕ) (hn : 0 < n)
    {c : ConjClasses (Variety.Point K)} (hc : c ∈ fixedAmbientOddClasses S n) :
    (∃ x : Variety.Point K, IsSemisimpleElement K x ∧ ConjClasses.mk x = c) ∧
      ConjClasses.map (graphFieldEnd S n) c = c := by
  obtain ⟨x, hx, rfl⟩ := hc
  refine ⟨⟨x, fixed_odd_isSemisimple S n hn x hx, rfl⟩, ?_⟩
  change ConjClasses.mk (graphFieldEnd S n x) =
    ConjClasses.mk (x : Variety.Point K)
  exact congrArg ConjClasses.mk x.property

/-- Actual centralizer Lang solutions imply descent of odd-order conjugacy. -/
theorem oddClassFusion_of_centralizerLang (S : Geometry K) (n : ℕ)
    (hLang : OddCentralizerLang S n) : OddClassFusion S n := by
  intro x y hx _ hxy
  exact isConj_fixed_of_centralizer_lang (graphFieldEnd S n) x y
    (hLang x hx) hxy

/-- Once conjugacy descends, passing to ambient classes loses no odd-order
classes of the fixed-point group. -/
theorem fixedOddClasses_card_eq_ambient (S : Geometry K) (n : ℕ)
    (hfusion : OddClassFusion S n) :
    Nat.card (ConjClasses.mk '' {g : graphFieldFixedSubgroup
      S.diagram.toMulEquiv S.frobenius.onPoints n | ¬ 2 ∣ orderOf g}) =
        Nat.card (fixedAmbientOddClasses S n) := by
  apply card_classes_image
    (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype
  intro x hx y hy
  exact hfusion x y hx hy

/-- Generation supplies an actual group isomorphism, hence an equality of
odd-order class counts, between the elementary and full fixed-point groups. -/
theorem elementaryOddClasses_card_eq_fixed (S : Geometry K) (n : ℕ)
    (hgen : graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n = ⊤) :
    Nat.card (ConjClasses.mk '' {g : graphFieldElementarySubgroup
      S.diagram.toMulEquiv S.frobenius.onPoints n | ¬ 2 ∣ orderOf g}) =
    Nat.card (ConjClasses.mk '' {g : graphFieldFixedSubgroup
      S.diagram.toMulEquiv S.frobenius.onPoints n | ¬ 2 ∣ orderOf g}) :=
  card_oddClasses_mulEquiv ((MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound

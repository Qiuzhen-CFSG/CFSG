module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.MarkedParabolic.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Reducing the fixed-plane centralizer to a single natural vector

The two definite planes are disjoint. Their order-two intersections with
Z_S generate Z_S by the preliminary order-four calculation. Since I
centralizes the first line, C_I(Z_S) is the centralizer of the nonidentity
element on the second line. The given natural coordinates turn this into
the stabilizer of a nonzero Sylow-fixed vector in the six-dimensional module.

Source: Aschbacher–Smith, 15.3.8 and 15.3.32(2),(4), printed pp.1123,1132–1133.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.MarkedParabolic
variable {G : Type*} [Group G] [Finite G]

/-- The two fixed lines generate the order-four fixed plane. -/
theorem fixedPlane_eq_sup_lines (d : LocalData G)
    (hcard : Nat.card d.ZS = 4)
    (hfirst : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2)
    (hsecond : Nat.card (d.ZS ⊓ d.V₂ : Subgroup G) = 2) :
    d.ZS = (d.ZS ⊓ d.V₁) ⊔ (d.ZS ⊓ d.V₂) := by
  have hdis : Disjoint (d.ZS ⊓ d.V₁) (d.ZS ⊓ d.V₂) :=
    (RankTwo.natural_planes_disjoint d.action (by decide :
      (1 : OrthogonalPlaneIndex) ≠ Multiplicative.ofAdd (1 : ZMod 2))).mono
      inf_le_right inf_le_right
  have hS : d.ZS ≤ d.S := d.action.fixedPlane_le_stabilizer d.T d.sylow_le
    (localModule_le d.T d.sylow_le) 1
  have hn : d.ZS ⊓ d.V₂ ≤ normalizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G) :=
    (inf_le_left.trans hS).trans ((sylow_le_fixedPlane_centralizer d).trans
      ((centralizer_le inf_le_left).trans (centralizer_le_normalizer _)))
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hdis
  exact (eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) (by
    rw [hcard, hc, hfirst, hsecond])).symm

/-- Inside I the second line determines the entire fixed-plane centralizer. -/
theorem fixedPlane_centralizer_eq_secondLine (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hjoin : I = c.L ⊔ d.S)
    (hfixed : d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁)
    (hcard : Nat.card d.ZS = 4)
    (hfirst : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2)
    (hsecond : Nat.card (d.ZS ⊓ d.V₂ : Subgroup G) = 2) :
    I ⊓ centralizer (d.ZS : Set G) =
      I ⊓ centralizer ((d.ZS ⊓ d.V₂ : Subgroup G) : Set G) := by
  apply le_antisymm (inf_le_inf_left _ (centralizer_le inf_le_left))
  intro i hi
  refine ⟨hi.1, ?_⟩
  have hz₁ := overgroup_le_fixedLine_centralizer d c hjoin hfixed hi.1
  have hz : (d.ZS ⊓ d.V₁) ⊔ (d.ZS ⊓ d.V₂) ≤ centralizer ({i} : Set G) := by
    apply sup_le
    · intro z hz
      rw [mem_centralizer_singleton_iff]
      exact hz₁ z hz
    · intro z hz
      rw [mem_centralizer_singleton_iff]
      exact hi.2 z hz
  rw [← fixedPlane_eq_sup_lines d hcard hfirst hsecond] at hz
  intro z hz'
  exact mem_centralizer_singleton_iff.mp (hz hz')

omit [Finite G] in
/-- An order-two subgroup has the same centralizer as its nonidentity element. -/
private theorem centralizer_orderTwo_eq_singleton (Z : Subgroup G)
    (hc : Nat.card Z = 2) (z : Z) (hne : z ≠ 1) :
    centralizer (Z : Set G) = centralizer ({(z : G)} : Set G) := by
  apply le_antisymm (centralizer_le (Set.singleton_subset_iff.mpr z.property))
  intro g hg w hw
  have hall := (Nat.card_eq_two_iff' (1 : Z)).mp hc
  have he : (⟨w, hw⟩ : Z) = 1 ∨ (⟨w, hw⟩ : Z) = z := by
    obtain ⟨u, hu, hall⟩ := hall
    have hz : z = u := hall z hne
    by_cases hw1 : (⟨w, hw⟩ : Z) = 1
    · exact Or.inl hw1
    · exact Or.inr ((hall ⟨w, hw⟩ hw1).trans hz.symm)
  rcases he with he | he
  · have hw1 : w = 1 := congrArg Subtype.val he
    simp [hw1]
  · have hwz : w = (z : G) := congrArg Subtype.val he
    rw [hwz]
    exact (mem_centralizer_singleton_iff.mp hg).symm

/-- The fixed plane is controlled by a nonzero fixed vector in the natural module. -/
theorem exists_fixedVector_centralizer (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hjoin : I = c.L ⊔ d.S)
    (a : NaturalEightAction I (d.componentModule I c.L))
    (hfixed : d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁)
    (hcard : Nat.card d.ZS = 4)
    (hfirst : Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2)
    (hsecond : Nat.card (d.ZS ⊓ d.V₂ : Subgroup G) = 2)
    (hinter : d.ZS ⊓ d.componentModule I c.L = d.ZS ⊓ d.V₂) :
    ∃ v : BinaryPermutation.natural (Fin 8), v ≠ 0 ∧
      (∀ s : I, (s : G) ∈ d.S →
        BinaryPermutation.naturalRepresentation (Fin 8) (a.actor s) v = v) ∧
      (∀ i : I, (i : G) ∈ centralizer (d.ZS : Set G) ↔
        BinaryPermutation.naturalRepresentation (Fin 8) (a.actor i) v = v) := by
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : (d.ZS ⊓ d.V₂ : Subgroup G))).mp hsecond
  have hzU : (z : G) ∈ d.componentModule I c.L :=
    ((hinter.symm ▸ z.property) : (z : G) ∈ d.ZS ⊓ d.componentModule I c.L).2
  let u : d.componentModule I c.L := ⟨z, hzU⟩
  let v := Multiplicative.toAdd (a.coordinates u)
  have hv : v ≠ 0 := by
    intro he
    have he' : a.coordinates u = 1 := congrArg Multiplicative.ofAdd he
    have hu : u = 1 := a.coordinates.injective (he'.trans a.coordinates.map_one.symm)
    apply hz
    apply Subtype.ext
    exact congrArg (fun x : d.componentModule I c.L => (x : G)) hu
  have hpoint (i : I) : (i : G) ∈ centralizer ({(z : G)} : Set G) ↔
      BinaryPermutation.naturalRepresentation (Fin 8) (a.actor i) v = v := by
    have he := a.compatible i u
    constructor
    · intro hi
      have hfix : (d.componentModule I c.L).normalizerMonoidHom
          ⟨i, a.normalizes i.property⟩ u = u := by
        apply Subtype.ext
        change (i : G) * (z : G) * (i : G)⁻¹ = z
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hi)
      rw [hfix] at he
      exact (congrArg Multiplicative.toAdd he).symm
    · intro hi
      have hfix := a.coordinates.injective (he.trans (congrArg Multiplicative.ofAdd hi))
      have hg := congrArg Subtype.val hfix
      change (i : G) * (z : G) * (i : G)⁻¹ = z at hg
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hg)
  have heq : I ⊓ centralizer (d.ZS : Set G) =
      I ⊓ centralizer ({(z : G)} : Set G) := by
    rw [fixedPlane_centralizer_eq_secondLine d c hjoin hfixed hcard hfirst hsecond,
      centralizer_orderTwo_eq_singleton _ hsecond z hz]
  have hfull (i : I) : (i : G) ∈ centralizer (d.ZS : Set G) ↔
      BinaryPermutation.naturalRepresentation (Fin 8) (a.actor i) v = v := by
    rw [← hpoint]
    exact ⟨fun h => (heq.le ⟨i.property, h⟩).2, fun h => (heq.ge ⟨i.property, h⟩).2⟩
  exact ⟨v, hv, fun s hs => (hfull s).mp (sylow_le_fixedPlane_centralizer d hs), hfull⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.MarkedParabolic
end

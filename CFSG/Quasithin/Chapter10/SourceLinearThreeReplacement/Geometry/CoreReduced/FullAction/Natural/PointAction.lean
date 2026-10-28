module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Natural
public import Theory.Representation.SpecialLinearNatural.BinaryPointStabilizer

/-!
# The point centralizer on the original moved factor

Lift the binary natural point-stabilizer action through the specified quotient
L/O₂(L). The faithful original coordinates identify its lift with conjugation
by C_L(a), keeping both the original vector and the component embedding.

Source: Aschbacher--Smith 10.2.11(3), printed p.754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction.Natural
open Chapter3.Section02

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}

/-- The literal point centralizer is transitive on the first factor outside its fixed line. -/
theorem exists_pointCentralizer_conjugating (c : Configuration s a b)
    (x y : (⁅D.fullModule,L⁆ : Subgroup G))
    (hx : (x : G) ≠ 1) (hxa : (x : G) ≠ a)
    (hy : (y : G) ≠ 1) (hya : (y : G) ≠ a) :
    ∃ g : G, g ∈ L ∧ g ∈ centralizer ({a} : Set G) ∧ (MulAut.conj g) (x : G) = y := by
  let f := s.natural.coordinates
  have hi : Function.Injective f := (Seed.natural_coordinates_bijective c).1
  have hn (v : (⁅D.fullModule,L⁆ : Subgroup G)) (hv : (v : G) ≠ 1) :
      (f v).toAdd ≠ 0 := by
    intro he
    exact hv (congrArg Subtype.val (hi (he.trans (map_one f).symm)))
  have hne (v : (⁅D.fullModule,L⁆ : Subgroup G)) (hv : (v : G) ≠ a) :
      (f v).toAdd ≠ (f ⟨a,c.first_mem⟩).toAdd :=
    fun he => hv (congrArg Subtype.val (hi he))
  obtain ⟨m, hma, hmx⟩ := Representation.BinaryPointStabilizer.exists_point_fixer
    (f ⟨a,c.first_mem⟩).toAdd (f x).toAdd (f y).toAdd
    (hn _ c.first_ne) (hn x hx) (hn y hy) (hne x hxa) (hne y hya)
  obtain ⟨q,hq⟩ := s.quotient.surjective m
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  have heq : s.quotient (QuotientGroup.mk' (pCore 2 L) g) = m := by rw [hg,hq]
  have he (v : (⁅D.fullModule,L⁆ : Subgroup G)) :
      (f ⟨g * v * (g : G)⁻¹,
        (mem_normalizer_iff.mp (s.natural.normalized g.property) v).mp v.property⟩).toAdd =
      Representation.specialLinearNatural 3 m (f v).toAdd := by
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, heq]
      using s.natural.equivariant g v
  have ha : (g : G) * a * (g : G)⁻¹ = a :=
    congrArg Subtype.val (hi ((he ⟨a,c.first_mem⟩).trans hma))
  refine ⟨g,g.property,?_,?_⟩
  · exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp ha)
  · exact congrArg Subtype.val (hi ((he x).trans hmx))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.FullAction.Natural

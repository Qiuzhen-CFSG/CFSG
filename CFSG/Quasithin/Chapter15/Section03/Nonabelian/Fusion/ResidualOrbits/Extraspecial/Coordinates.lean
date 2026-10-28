module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Inputs
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.QuotientFusion
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.Coordinate

/-!
# Natural and dual quotient orbits for the extraspecial branch

The actual recognition of 15.3.58 identifies U/Z with the binary natural
three-space and its linear dual. Every linear automorphism lifts to H.
Transitivity on vector/covector pairs of fixed pairing gives the mixed
singular class, and the supplied summand interchange joins the pure classes.
The extraspecial inner correction lifts both calculations to conjugacy by H.

These results do not identify the square map or the marked ambient classes
z and v. Those source-geometric identifications remain separate obligations.
In particular, the dimensions-four/five orbit theorem is not used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.58 and the first paragraph proving 15.3.61(2), pp.1148–1150.
-/

@[expose] public section

open Subgroup BinaryNaturalDual BinaryNaturalDual.ModelOrbits
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion
open CFSG.Quasithin.Chapter15.Section03.FusionCore
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial

private theorem linear_action_surjective : Function.Surjective
    (Matrix.SpecialLinearGroup.toLin' : BinaryLinearThree.Group →*
      BinaryLinear.GL BinaryLinearThree.Vector) := by
  let e := Matrix.PSL3Two.equivGL.trans (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryLinearThree.Vector))
  intro g
  obtain ⟨s, hs⟩ := e.surjective g
  refine ⟨s, ?_⟩
  rw [← hs]
  apply LinearEquiv.ext
  intro v
  simp only [e, MulEquiv.trans_apply, Matrix.PSL3Two.equivGL_apply,
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Matrix.GeneralLinearGroup.toLin_apply, Matrix.SpecialLinearGroup.toLin'_apply,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

private theorem model_action_eq (g : BinaryLinearThree.Group) (w : NaturalDualSpace) :
    (BinaryLinearThree.W g w.1, BinaryLinearThree.W.dual g w.2) =
      naturalDualRepresentation (Matrix.SpecialLinearGroup.toLin' g) w := by
  rw [naturalDualRepresentation_apply]
  apply Prod.ext rfl
  apply LinearMap.ext
  intro v
  change w.2 (Matrix.SpecialLinearGroup.toLin' g⁻¹ v) =
    w.2 ((Matrix.SpecialLinearGroup.toLin' g).symm v)
  rw [map_inv]
  rfl

variable {G : Type*} [Group G] {T Z ZS V : Subgroup G} {t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]
variable (d : RecognizedAction T Z ZS V t)

/-- Every binary linear transformation is realized by an actual element of H. -/
theorem exists_quotient_action_linear (g : BinaryLinear.GL BinaryLinearThree.Vector) :
    ∃ h : centralizerH Z, ∀ w : VectorQuotient Z ZS,
      (d.coordinates (quotientAction Z ZS h w)).toAdd =
        naturalDualRepresentation g (d.coordinates w).toAdd := by
  obtain ⟨s, rfl⟩ := linear_action_surjective g
  obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective (pCore 2 (centralizerH Z))
    (d.actorEquiv.symm (MulAut.conj s))
  refine ⟨h, fun w => (d.equivariant h s ?_ w).trans (model_action_eq s _)⟩
  rw [hh, d.actorEquiv.apply_symm_apply]

/-- The mixed singular vectors form one orbit on the literal quotient U/Z. -/
theorem quotient_orbit_of_singularDiagonal {x y : VectorQuotient Z ZS}
    (hx : IsSingularDiagonal (d.coordinates x).toAdd)
    (hy : IsSingularDiagonal (d.coordinates y).toAdd) :
    ∃ h : centralizerH Z, quotientAction Z ZS h x = y := by
  obtain ⟨g, hg⟩ := exists_naturalDual_eq hx.1 hy.1 hx.2.1 hy.2.1
    (hx.2.2.trans hy.2.2.symm)
  obtain ⟨h, hh⟩ := exists_quotient_action_linear d g
  refine ⟨h, d.coordinates.injective (Multiplicative.toAdd.injective ?_)⟩
  exact (hh x).trans hg

private theorem coordinates_ne_zero {x : VectorQuotient Z ZS} (hx : x ≠ 1) :
    (d.coordinates x).toAdd ≠ 0 := by
  intro he
  exact hx (d.coordinates.injective (he.trans (map_one d.coordinates).symm))

private theorem exists_pure_to_natural {x : VectorQuotient Z ZS}
    (hx : IsPure (d.coordinates x).toAdd) {w : BinaryLinearThree.Vector} (hw : w ≠ 0) :
    ∃ h : centralizerH Z,
      (d.coordinates (quotientAction Z ZS h x)).toAdd = (w, 0) := by
  have hn : x ≠ 1 := by
    intro h
    simp only [h, map_one, toAdd_one] at hx
    rcases hx with hx | hx
    · exact hx.1 rfl
    · exact hx.2 rfl
  rcases hx with ⟨hx₁, hx₂⟩ | ⟨hx₁, hx₂⟩
  · obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq hx₁ hw
    obtain ⟨h, hh⟩ := exists_quotient_action_linear d g
    exact ⟨h, by rw [hh, naturalDualRepresentation_apply, hg, hx₂, map_zero]⟩
  · let tt : centralizerH Z := ⟨t, d.t_mem_H⟩
    let y := quotientAction Z ZS tt x
    have hx' : x = d.coordinates.symm
        (Multiplicative.ofAdd (0, (d.coordinates x).toAdd.2)) := by
      apply d.coordinates.injective
      rw [d.coordinates.apply_symm_apply]
      exact Prod.ext hx₁ rfl
    have hy₂ : (d.coordinates y).toAdd.2 = 0 := by
      dsimp only [y, tt]
      rw [hx']
      exact d.swaps_dual _
    have hyn : y ≠ 1 := by
      intro h
      exact hn ((quotientAction Z ZS tt).injective (h.trans (map_one _).symm))
    have hy₁ : (d.coordinates y).toAdd.1 ≠ 0 := by
      intro h
      exact coordinates_ne_zero d hyn (Prod.ext h hy₂)
    obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq hy₁ hw
    obtain ⟨h, hh⟩ := exists_quotient_action_linear d g
    refine ⟨h * tt, ?_⟩
    rw [map_mul]
    change (d.coordinates (quotientAction Z ZS h y)).toAdd = (w, 0)
    rw [hh, naturalDualRepresentation_apply, hg, hy₂, map_zero]

/-- The two punctured summands form one orbit under the actual H-action. -/
theorem quotient_orbit_of_isPure {x y : VectorQuotient Z ZS}
    (hx : IsPure (d.coordinates x).toAdd) (hy : IsPure (d.coordinates y).toAdd) :
    ∃ h : centralizerH Z, quotientAction Z ZS h x = y := by
  let w : BinaryLinearThree.Vector := fun _ => 1
  have hw : w ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h 0)
  obtain ⟨a, ha⟩ := exists_pure_to_natural d hx hw
  obtain ⟨b, hb⟩ := exists_pure_to_natural d hy hw
  have he : quotientAction Z ZS a x = quotientAction Z ZS b y :=
    d.coordinates.injective (Multiplicative.toAdd.injective (ha.trans hb.symm))
  refine ⟨b⁻¹ * a, ?_⟩
  rw [map_mul]
  change quotientAction Z ZS b⁻¹ (quotientAction Z ZS a x) = y
  rw [he]
  change (quotientAction Z ZS b⁻¹ * quotientAction Z ZS b) y = y
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

/-- Pure noncentral lifts are conjugate by H, including the central correction. -/
theorem conjugateBy_of_isPure [IsExtraspecial 2 (closureU Z ZS)]
    (hZS : ZS ≤ centralizerH Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (x y : closureU Z ZS)
    (hx : IsPure (d.coordinates (QuotientGroup.mk' _ x)).toAdd)
    (hy : IsPure (d.coordinates (QuotientGroup.mk' _ y)).toAdd) :
    ConjugateBy (centralizerH Z) (x : G) (y : G) := by
  have hyn : (y : G) ∉ Z := by
    intro h
    have he : QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) y = 1 :=
      (QuotientGroup.eq_one_iff y).mpr h
    rw [he, map_one] at hy
    rcases hy with hy | hy
    · exact hy.1 rfl
    · exact hy.2 rfl
  exact (conjugateBy_iff_quotient_orbit Z ZS hZS hcenter x y hyn).mpr
    (quotient_orbit_of_isPure d hx hy)

/-- Mixed singular lifts are conjugate by H, including the central correction. -/
theorem conjugateBy_of_singularDiagonal [IsExtraspecial 2 (closureU Z ZS)]
    (hZS : ZS ≤ centralizerH Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (x y : closureU Z ZS)
    (hx : IsSingularDiagonal (d.coordinates (QuotientGroup.mk' _ x)).toAdd)
    (hy : IsSingularDiagonal (d.coordinates (QuotientGroup.mk' _ y)).toAdd) :
    ConjugateBy (centralizerH Z) (x : G) (y : G) := by
  have hyn : (y : G) ∉ Z := by
    intro h
    have he : QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) y = 1 :=
      (QuotientGroup.eq_one_iff y).mpr h
    rw [he, map_one] at hy
    exact hy.1 rfl
  exact (conjugateBy_iff_quotient_orbit Z ZS hZS hcenter x y hyn).mpr
    (quotient_orbit_of_singularDiagonal d hx hy)

/-- The actual preimage U₁ of the natural summand, embedded in G. -/
def naturalPreimage : Subgroup G :=
  ((AddMonoidHom.snd BinaryLinearThree.Vector (Module.Dual (ZMod 2) BinaryLinearThree.Vector)).toMultiplicative.comp
    (d.coordinates.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS))))).ker.map
      (closureU Z ZS).subtype

/-- The actual preimage of the dual summand, embedded in G. -/
def dualPreimage : Subgroup G :=
  ((AddMonoidHom.fst BinaryLinearThree.Vector (Module.Dual (ZMod 2) BinaryLinearThree.Vector)).toMultiplicative.comp
    (d.coordinates.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS))))).ker.map
      (closureU Z ZS).subtype

/-- Membership in U₁ is the vanishing of the dual coordinate. -/
theorem mem_naturalPreimage (x : closureU Z ZS) :
    (x : G) ∈ naturalPreimage d ↔ (d.coordinates (QuotientGroup.mk' _ x)).toAdd.2 = 0 := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hxy : y = x := Subtype.ext he
    exact hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Membership in the dual preimage is the vanishing of the natural coordinate. -/
theorem mem_dualPreimage (x : closureU Z ZS) :
    (x : G) ∈ dualPreimage d ↔ (d.coordinates (QuotientGroup.mk' _ x)).toAdd.1 = 0 := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hxy : y = x := Subtype.ext he
    exact hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Outside Z, the pure class is exactly the union of the two summand preimages. -/
theorem isPure_iff_mem_preimages (x : closureU Z ZS) (hxZ : (x : G) ∉ Z) :
    IsPure (d.coordinates (QuotientGroup.mk' _ x)).toAdd ↔
      (x : G) ∈ naturalPreimage d ∨ (x : G) ∈ dualPreimage d := by
  rw [mem_naturalPreimage, mem_dualPreimage]
  have hn : (d.coordinates (QuotientGroup.mk' _ x)).toAdd ≠ 0 := by
    intro he
    have hh : QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) x = 1 :=
      d.coordinates.injective (he.trans (map_one d.coordinates).symm)
    exact hxZ ((QuotientGroup.eq_one_iff x).mp hh)
  constructor
  · rintro (⟨_, hx⟩ | ⟨hx, _⟩)
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (h₂ | h₁)
    · exact Or.inl ⟨fun h₁ => hn (Prod.ext h₁ h₂), h₂⟩
    · exact Or.inr ⟨h₁, fun h₂ => hn (Prod.ext h₁ h₂)⟩

/-- The natural summand preimage is an actual subgroup of U. -/
theorem naturalPreimage_le : naturalPreimage d ≤ closureU Z ZS := map_subtype_le _

/-- The dual summand preimage is an actual subgroup of U. -/
theorem dualPreimage_le : dualPreimage d ≤ closureU Z ZS := map_subtype_le _

/-- The remaining square-map and marked-geometry output contract.
This is not a source hypothesis: its construction is required before the
conditional inside-U assembly below proves the source assertion. -/
structure MarkedGeometry (d : RecognizedAction T Z ZS V t) (z v : G) where
  square_zero : ∀ x : closureU Z ZS, (x : G) ^ 2 = 1 ↔
    quadratic (d.coordinates (QuotientGroup.mk' _ x)).toAdd = 0
  pureSeed : closureU Z ZS
  pureSeed_pure : IsPure (d.coordinates (QuotientGroup.mk' _ pureSeed)).toAdd
  pureSeed_fusion : IsConj (pureSeed : G) z
  v_mem : v ∈ closureU Z ZS
  v_mixed : IsSingularDiagonal
    (d.coordinates (QuotientGroup.mk' _ ⟨v, v_mem⟩)).toAdd

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial

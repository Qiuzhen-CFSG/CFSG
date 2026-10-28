module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Pairing
public import Theory.Representation.BinaryOffender.Defs
public import Theory.Representation.DualCommutator

/-!
# The hexad code commutator under coordinate duality

The existing equivariant coordinate pairing sends the actual code
commutator [V,K] onto the annihilator of the cocode fixed space C_V(K).
This is proved on commutator generators and then by double annihilation.
Consequently a five-dimensional cocode fixed space gives both a
five-dimensional code commutator and a five-dimensional code quotient.
The definition is the actual commutator span, not an assumed flag term.

Source: Aschbacher--Smith, the duality step in H.16.4(1)--(3), printed p.403,
combined manuscript of 1 March 2004. The remaining chief and action assertions
require more than this dimension calculation.
-/

@[expose] public section

noncomputable section
open Representation Representation.BinaryOffender
namespace MathieuCode.Hexad

private theorem commutator_map_equivariant {G V W : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (E : V ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (ρ g v) = σ g (E v)) :
    (Coinvariants.ker ρ).map E.toLinearMap = Coinvariants.ker σ := by
  rw [Coinvariants.ker, Coinvariants.ker, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨⟨g,v⟩, rfl⟩, rfl⟩
    exact ⟨(g, E v), by simp only [map_sub, hE, LinearEquiv.coe_coe]⟩
  · rintro ⟨⟨g,w⟩, rfl⟩
    obtain ⟨v, rfl⟩ := E.surjective w
    exact ⟨ρ g v - v, ⟨(g,v), rfl⟩, by simp only [map_sub, hE, LinearEquiv.coe_coe]⟩

/-- The literal code commutator space, the term V5 of the hexad flag. -/
def codeCommutator (K : Subgroup m22PairStabilizer) : Submodule (ZMod 2) M22Code :=
  Coinvariants.ker (m22OuterCodeRepresentation.comp K.subtype)

/-- Coordinate duality identifies the commutator with the annihilator of the
cocode fixed space. -/
theorem codeCommutator_map_duality (K : Subgroup m22PairStabilizer) :
    (codeCommutator K).map m22CodeCocodeDuality.toLinearMap =
      (fixedSpace m22OuterCocodeRepresentation K).dualAnnihilator := by
  have he := commutator_map_equivariant
    (m22OuterCodeRepresentation.comp K.subtype)
    (Representation.dual (m22OuterCocodeRepresentation.comp K.subtype))
    m22CodeCocodeDuality (fun g v => m22CodeCocodeDuality_equivariant g.val v)
  change (codeCommutator K).map m22CodeCocodeDuality.toLinearMap = _ at he
  rw [he]
  change Coinvariants.ker (Representation.dual (m22OuterCocodeRepresentation.comp K.subtype)) =
    (invariants (m22OuterCocodeRepresentation.comp K.subtype)).dualAnnihilator
  rw [Representation.invariants_eq_dual_commutator_coannihilator,
    Subspace.dualCoannihilator_dualAnnihilator_eq]

theorem codeCommutator_eq_annihilator (K : Subgroup m22PairStabilizer) :
    codeCommutator K = ((fixedSpace m22OuterCocodeRepresentation K).dualAnnihilator).comap
      m22CodeCocodeDuality.toLinearMap := by
  rw [← codeCommutator_map_duality,
    Submodule.comap_map_eq_of_injective m22CodeCocodeDuality.injective]

theorem codeCommutator_finrank (K : Subgroup m22PairStabilizer)
    (h5 : Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation K) = 5) :
    Module.finrank (ZMod 2) (codeCommutator K) = 5 := by
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (fixedSpace m22OuterCocodeRepresentation K)
  rw [h5, finrank_m22Cocode, ← codeCommutator_map_duality,
    LinearEquiv.finrank_map_eq] at hd
  exact Nat.add_left_cancel hd

theorem codeCommutator_quotient_finrank (K : Subgroup m22PairStabilizer)
    (h5 : Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation K) = 5) :
    Module.finrank (ZMod 2) (M22Code ⧸ codeCommutator K) = 5 := by
  have hd := (codeCommutator K).finrank_quotient_add_finrank
  rw [codeCommutator_finrank K h5, finrank_m22Code] at hd
  exact Nat.add_right_cancel hd

end MathieuCode.Hexad

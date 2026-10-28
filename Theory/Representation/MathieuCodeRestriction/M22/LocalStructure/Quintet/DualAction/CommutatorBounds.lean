module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Inputs

/-!
# Bounds on the cocode commutator space

The marked natural quotient is trivial on K, so every displacement belongs to
V6. An earlier inner involution of displacement four forces the commutator
to have dimension at least four. These bounds start the nonsplitting argument
that must prove equality with V6; equality is not assumed here.

Source: Aschbacher--Smith, H.14.4(2--3), H.15.4(1), and the duality
step in H.16.3(1), printed pp.397--400,403 (1 March 2004 manuscript).
-/

@[expose] public section
noncomputable section
namespace MathieuCode.M22Quintet.DualAction

abbrev cocodeCommutator : Submodule (ZMod 2) M22Cocode :=
  Representation.Coinvariants.ker (m22OuterCocodeRepresentation.comp K.subtype)

variable {F : CocodeFlag} {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

theorem cocode_displacement_mem_six (D : CocodeActionData F E) (g : K)
    (v : M22Cocode) : m22OuterCocodeRepresentation g.val v - v ∈ V6 := by
  have hq : D.quotientMap (kernelInclusion g) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [D.quotientMap_ker]
    exact g.property
  have he := D.naturalQuotient_equivariant (kernelInclusion g) (V6.mkQ v)
  rw [hq, map_one, Module.End.one_apply] at he
  have h := D.naturalQuotient.injective he
  apply (Submodule.Quotient.mk_eq_zero V6).mp
  change V6.mkQ (m22OuterCocodeRepresentation g.val v - v) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr h

theorem cocode_commutator_le_six (D : CocodeActionData F E) : cocodeCommutator ≤ V6 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, v⟩, rfl⟩
  exact cocode_displacement_mem_six D g v

theorem cocode_commutator_finrank_ge_four (D : CocodeActionData F E)
    (H : EarlierInputs D) : 4 ≤ Module.finrank (ZMod 2) cocodeCommutator := by
  obtain ⟨i, _, _, _, hi⟩ := H.involution_displacement
  have hle : LinearMap.range (m22OuterCocodeRepresentation i.val - LinearMap.id) ≤
      cocodeCommutator := by
    rintro _ ⟨v, rfl⟩
    exact Representation.Coinvariants.sub_mem_ker i v
  simpa only [hi] using Submodule.finrank_mono hle

/-- In particular the commutator is not confined to the two-dimensional term. -/
theorem cocode_commutator_not_le_two (D : CocodeActionData F E)
    (H : EarlierInputs D) : ¬cocodeCommutator ≤ V2 := by
  intro h
  have hle := Submodule.finrank_mono h
  have hge := cocode_commutator_finrank_ge_four D H
  rw [F.dim2] at hle
  omega

end MathieuCode.M22Quintet.DualAction

module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Local
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.Definitions
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.Coordinates
public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.InvolutiveWeights
public import Theory.SpecificGroups.Janko1.Model.Basic

/-!
# The Sylow character decomposition over GF(11)

The actual matrix representation restricts to the source Sylow eight. Its
operators square to one, so their simultaneous character spaces span already
over GF(11). Faithfulness supplies a nontrivial occurring character, and
independence bounds the number of occurring characters by seven.

These statements discharge the splitting-field input to the normalizer basis
construction in Gorenstein, *Finite Groups*, §16.6, pp.482–483. They require
neither irreducibility nor an identification of the ambient group with J₁.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation

/-- The coefficient field used by the source representation. -/
public instance normalizerBasisPrimeEleven : Fact (Nat.Prime 11) := ⟨by decide⟩

variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- The supplied representation acting on column vectors. -/
@[expose] public noncomputable def vectorRepresentation (ρ : G →* Janko1.Ambient) :
    Representation (ZMod 11) G (Fin 7 → ZMod 11) :=
  (Representation.generalLinearNatural 7).comp ρ

/-- Its restriction to the literal Sylow subgroup in the source data. -/
@[expose] public noncomputable def sylowRepresentation (ρ : G →* Janko1.Ambient) :
    Representation (ZMod 11) h.sylow (Fin 7 → ZMod 11) :=
  (vectorRepresentation ρ).comp (h.sylow : Subgroup G).subtype

omit [Finite G] in
/-- The action agrees with the original matrices acting on column vectors. -/
public theorem vectorRepresentation_apply (ρ : G →* Janko1.Ambient) (g : G)
    (v : Fin 7 → ZMod 11) :
    vectorRepresentation ρ g v = Matrix.mulVec (ρ g : Matrix (Fin 7) (Fin 7) (ZMod 11)) v :=
  LinearMap.congr_fun (Matrix.GeneralLinearGroup.coe_toLin (ρ g)) v

omit [Finite G] in
public theorem vectorRepresentation_injective (ρ : G →* Janko1.Ambient)
    (hρ : Function.Injective ρ) : Function.Injective (vectorRepresentation ρ) :=
  (Representation.generalLinearNatural_injective 7).comp hρ

public theorem sylowRepresentation_injective (ρ : G →* Janko1.Ambient)
    (hρ : Function.Injective ρ) : Function.Injective (sylowRepresentation h ρ) :=
  (vectorRepresentation_injective ρ hρ).comp Subtype.val_injective

/-- The simultaneous Sylow eigenspaces span over the prime field itself. -/
public theorem sylow_characterWeightSpace_span (ρ : G →* Janko1.Ambient) :
    (⨆ χ : (sylowRepresentation h ρ).CharacterWeight,
      (sylowRepresentation h ρ).characterWeightSpace χ.val) = ⊤ := by
  let := h.sylow_elementaryAbelian
  exact Representation.iSup_characterWeightSpace_eq_top_of_involutive _ h.sylow_square
    (by decide)

/-- A faithful representation has a nontrivial Sylow character over GF(11). -/
public theorem exists_nontrivial_sylow_weight (ρ : G →* Janko1.Ambient)
    (hρ : Function.Injective ρ) :
    ∃ χ : (sylowRepresentation h ρ).CharacterWeight, χ.val ≠ 1 := by
  let := h.sylow_elementaryAbelian
  have : Nontrivial h.sylow := ⟨⟨⟨h.z, h.z_mem⟩, 1,
    fun he => h.z_ne_one (congrArg Subtype.val he)⟩⟩
  exact Representation.exists_nontrivial_characterWeight_of_involutive _
    (sylowRepresentation_injective h ρ hρ) h.sylow_square (by decide)

/-- Independence gives the sharp seven-weight upper bound. -/
public theorem sylow_weight_card_le_seven (ρ : G →* Janko1.Ambient) :
    Finite (sylowRepresentation h ρ).CharacterWeight ∧
      Nat.card (sylowRepresentation h ρ).CharacterWeight ≤ 7 := by
  let := h.sylow_elementaryAbelian
  simpa using (sylowRepresentation h ρ).characterWeight_card_le
    (by rw [h.sylow_card]; decide)

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation

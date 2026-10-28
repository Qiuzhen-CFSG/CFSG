module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.FieldReduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.LargeFamily
public import Theory.SpecificGroups.SymmetricSix.SolvableGeneration
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360

/-!
# Binary derived symplectic E-generation

The genuine polar equivalence identifies Sp₄(F)′ with A₆ for every field
of order two. The duad and syntheme parabolics generate A₆ and S₆ and are
solvable. Solvable E-generation and E.1.8 therefore give rank-one generation
for these carriers. Faithful conjugation extends this argument to every
source group whose action on the marked A₆ lies in the natural S₆ image.
The full Sp₄(2) parabolics are never identified with the derived parabolics.

For the other outer actions, the actual ten-point-action comparison
A₆ ≃ PSL₂(9) connects the source input to the existing prime-square local
escape calculation. The final theorem below is conditional on that
calculation. It discharges the field model and all simple-socle structural
premises and uses the whole-group E2 theorem for rank-one actors. No
splitting, Sylow-fixing or natural-action premise is imposed on this
conditional assembly. The escaping E-members for larger actors remain an
explicit premise; thus this module does not yet prove the full binary
branch of E.1.14(1).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, E.1.1–E.1.14, printed pp.209–214,
particularly E.1.14(1),(6). The imported PSL₂(9) comparison retains the
ATLAS attribution and license in `Theory/AtlasPort/ExceptionalIsomorphisms`.
-/

public section

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour

private theorem generated_of_solvable_pair {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (P Q : Subgroup H)
    (hTP : (T : Subgroup H) ≤ P) (hTQ : (T : Subgroup H) ≤ Q)
    [Group.IsSolvable P] [Group.IsSolvable Q] (hPQ : P ⊔ Q = ⊤) :
    IsEGeneratedAt 1 T := by
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget 1 T Ω
  rw [← hPQ]
  exact sup_le
    (ChiefOrbit.solvable_overgroup_le_generationTarget (by decide) T P hTP hΩ)
    (ChiefOrbit.solvable_overgroup_le_generationTarget (by decide) T Q hTQ hΩ)

/-- The two actual solvable A₆ parabolics give rank-one E-generation. -/
theorem isEGenerated_alternatingSix : IsEGenerated 1 (alternatingGroup (Fin 6)) := by
  intro T
  obtain ⟨P, Q, hTP, hTQ, hP, hQ, hPQ⟩ :=
    Theory.SpecificGroups.SymmetricSix.a6_solvable_pair T
  let := hP
  let := hQ
  exact generated_of_solvable_pair T P Q hTP hTQ hPQ

/-- The full six-letter symmetric group is rank-one E-generated. -/
theorem isEGenerated_symmetricSix : IsEGenerated 1 (Equiv.Perm (Fin 6)) := by
  intro T
  obtain ⟨P, Q, hTP, hTQ, hP, hQ, hPQ⟩ :=
    Theory.SpecificGroups.SymmetricSix.s6_solvable_pair T
  let := hP
  let := hQ
  exact generated_of_solvable_pair T P Q hTP hTQ hPQ

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- The intrinsic derived binary model, transported through the actual polar equivalence. -/
theorem isEGenerated_of_binary_model (hF : Nat.card F = 2)
    (e : G ≃* commutator (Sp F)) : IsEGenerated 1 G :=
  isEGenerated_alternatingSix.map_equiv
    (e.trans (Binary.derivedEquivAlternatingSix hF)).symm

/-- The source binary case with F*(G) = G, with no extra generation premise. -/
theorem isEGenerated_binary_of_generalizedFitting_eq_top (hF : Nat.card F = 2)
    (e : generalizedFitting G ≃* commutator (Sp F))
    (hL : generalizedFitting G = ⊤) : IsEGenerated 1 G :=
  isEGenerated_of_binary_model hF
    ((topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)).trans e)

omit [Finite G] in
/-- The derived binary symplectic carrier is an actual PSL₂(9) matrix model.
The field is the concrete Galois field and the comparison is multiplicative. -/
theorem isPSL_nine_of_binary_model (hF : Nat.card F = 2)
    (e : G ≃* commutator (Sp F)) : ClassicalGroup.IsPSL G 2 (3 ^ 2) := by
  refine ⟨GaloisField 3 2, inferInstance, inferInstance, ?_, ?_⟩
  · exact GaloisField.card 3 2 (by decide)
  · exact ⟨(e.trans (Binary.derivedEquivAlternatingSix hF)).trans
      Atlas.Comparisons.Exceptional.psl2NineEquivAlt6.symm⟩

omit [Finite G] in
private theorem nonabelian_binary_socle (hF : Nat.card F = 2)
    (e : generalizedFitting G ≃* commutator (Sp F)) :
    ¬ IsMulCommutative (generalizedFitting G) :=
  ValuesOdd.PSLTwoGeneration.nonabelian_of_model _ (by decide)
    (isPSL_nine_of_binary_model hF e)

open AlternatingSix.ShadowLocal in
/-- Every extension whose faithful action lies in the natural S₆ image is
E₁-generated. The marked action is the literal conjugation action on F*(G). -/
theorem isEGenerated_binary_of_natural_action
    [IsSimpleGroup (generalizedFitting G)] (hF : Nat.card F = 2)
    (e : generalizedFitting G ≃* commutator (Sp F))
    (hnatural : (conjugationAction (generalizedFitting G)
      (e.trans (Binary.derivedEquivAlternatingSix hF))).range ≤ natural) :
    IsEGenerated 1 G := by
  let c := e.trans (Binary.derivedEquivAlternatingSix hF)
  let a := conjugationAction (generalizedFitting G) c
  have ha : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    rw [conjugationAction_ker]
    exact SimpleSocle.centralizer_eq_bot (nonabelian_binary_socle hF e)
  let b : G →* natural := a.codRestrict natural (fun g => hnatural ⟨g, rfl⟩)
  let n : Equiv.Perm (Fin 6) ≃* natural :=
    MonoidHom.ofInjective permutationAction_injective
  let f : G →* Equiv.Perm (Fin 6) := n.symm.toMonoidHom.comp b
  have hf : Function.Injective f := by
    intro x y h
    apply ha
    have hb : b x = b y := n.symm.injective h
    exact congrArg Subtype.val hb
  have hA : alternatingGroup (Fin 6) ≤ f.range := by
    intro x hx
    let k := c.symm ⟨x, hx⟩
    refine ⟨k, ?_⟩
    change n.symm (b k) = x
    apply n.injective
    rw [n.apply_symm_apply]
    apply Subtype.ext
    change conjugationAction (generalizedFitting G) c k = permutationAction x
    have hi := conjugationAction_on_inner (generalizedFitting G) c k
    have hc : c k = ⟨x, hx⟩ := c.apply_symm_apply _
    rw [hc] at hi
    exact hi.trans (permutationAction_coe ⟨x, hx⟩).symm
  have hk : f.ker = ⊥ := (MonoidHom.ker_eq_bot_iff f).mpr hf
  let : Group.IsSolvable f.ker := by rw [hk]; infer_instance
  intro T
  obtain ⟨P, Q, hTP, hTQ, hP, hQ, hPQ⟩ :=
    Theory.SpecificGroups.SymmetricSix.solvable_pair_of_six_action f hA T
  let := hP
  let := hQ
  exact generated_of_solvable_pair T P Q hTP hTQ hPQ

/-- Conditional assembly for all source outer actions. The sole remaining
input is the PSL₂(9) large-family escape calculation, after partial application
to the ambient SQTK and Sylow-supplement hypotheses. The concrete model,
centralizer, radical, two-core and whole-group E2 premises are proved here. -/
theorem isEGenerated_binary_of_square_calculation
    [IsSimpleGroup (generalizedFitting G)] (hF : Nat.card F = 2)
    (e : generalizedFitting G ≃* commutator (Sp F))
    (T₀ : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T₀ : Subgroup G) = ⊤)
    (hsquare : ClassicalGroup.IsPSL (generalizedFitting G) 2 (3 ^ 2) →
      centralizer (generalizedFitting G : Set G) = ⊥ →
      solvableRadical G = ⊥ → pCore 2 G = ⊥ →
      ∀ T : Sylow 2 G, ValuesOdd.PSLTwoGeneration.LargeFamilyEscapeAt T) :
    IsEGenerated 1 G := by
  have ha := nonabelian_binary_socle hF e
  obtain ⟨hC, hR, hO, _⟩ := SimpleSocle.structure_of_sylow_supplement ha T₀ hgen
  apply ValuesOdd.PSLTwoGeneration.isEGenerated_of_component_and_large_escape
  · intro T A _ _ hne
    exact RankOneUpper.eCaseComponent_top ha T₀ hgen (T : Subgroup G) A hne
  · exact hsquare (isPSL_nine_of_binary_model hF e) hC hR hO

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour

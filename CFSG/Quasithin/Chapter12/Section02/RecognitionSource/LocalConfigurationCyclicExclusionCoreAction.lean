module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionNumericalAction
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.Representation.BinaryCoprimeDegree
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.MinimalDegree
public import Theory.Representation.NormalInvariants

/-!
# Faithfulness and the binary-three core action

Use the literal conjugation homomorphism P → Aut(W), with its binary
representation on Additive W. Frattini fixed-point freeness gives zero
central invariants; extraspeciality then makes this representation faithful.
The exact binary degree divides dim W. When p=3 and |W|=64, the module is
irreducible. The normal two-core of H has a nonzero fixed vector on W;
P-invariance and irreducibility make that fixed space all of W.

Thus the source implication W ≤ Z(O₂(H)) is proved from its actual
numerical premises. Their discharge and the rest of the terminal source
contradiction remain with qt-d-12213-cyclic-block. The literal assembly is
in LocalConfigurationCyclicExclusionCoreAssembly.
Source: Aschbacher–Smith, 12.2.23, printed pp.803–804; G.7.1 for the binary degree.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}
namespace InvariantOddLocalAnalysis
variable (S : InvariantOddLocalAnalysis T L V d p H P U W g v)
include S

/-- The odd group's literal conjugation action on the original W. -/
@[expose] def oddModuleAction : P →* MulAut W :=
  W.normalizerMonoidHom.comp (inclusion
    ((S.overgroup ▸ le_sup_left).trans S.normalizes))

/-- The associated binary representation, using the original W as its carrier. -/
@[expose] def oddModuleRepresentation :
    let := S.elementary
    Representation (ZMod 2) P (Additive W) := by
  let := S.elementary
  exact Representation.elementaryRepresentation (p := 2) S.oddModuleAction

omit [Finite G] in
/-- The representation acts by the original ambient conjugation. -/
theorem oddModuleRepresentation_apply (a : P) (w : W) :
    (S.oddModuleRepresentation a (Additive.ofMul w)).toMul.val =
      (a : G) * (w : G) * (a : G)⁻¹ := rfl

/-- The central fixed space is zero under the source Frattini fixed-point hypothesis. -/
theorem oddModuleRepresentation_center_invariants
    (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥) :
    letI := S.elementary
    Representation.invariants (S.oddModuleRepresentation.comp (center P).subtype) = ⊥ := by
  let := S.elementary
  let : Fact p.Prime := ⟨S.prime⟩
  let := he
  apply bot_unique
  intro w hw
  change w = 0
  apply Additive.toMul.injective
  apply Subtype.ext
  have hm : (w.toMul : G) ∈ W ⊓ centralizer
      (((frattini P).map P.subtype : Subgroup G) : Set G) := by
    refine ⟨w.toMul.property, ?_⟩
    rintro z ⟨a, ha, rfl⟩
    rw [IsExtraspecial.frattini_eq_center (p := p)] at ha
    have hh := congrArg (fun x : Additive W => x.toMul.val) (hw (⟨a, ha⟩ : center P))
    change (a : G) * (w.toMul : G) * (a : G)⁻¹ = w.toMul at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  exact mem_bot.mp (hf ▸ hm)

/-- The original P-action on W is faithful in the extraspecial branch. -/
theorem oddModuleRepresentation_faithful
    (A : NaturalLocalAnalysis T L V d) (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥) :
    Function.Injective S.oddModuleRepresentation := by
  let := S.elementary
  let : Fact p.Prime := ⟨S.prime⟩
  let := he
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply Representation.ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := p)
  intro hk
  apply S.module_ne_bot A
  apply eq_bot_iff.mpr
  intro w hw
  have hi : Additive.ofMul (⟨w, hw⟩ : W) ∈
      Representation.invariants (S.oddModuleRepresentation.comp (center P).subtype) := by
    intro z
    have hz := hk z.property
    exact congrArg (fun f : Module.End (ZMod 2) (Additive W) =>
      f (Additive.ofMul (⟨w, hw⟩ : W))) hz
  rw [S.oddModuleRepresentation_center_invariants he hf] at hi
  exact congrArg (fun x : Additive W => x.toMul.val) hi

/-- The exact extraspecial binary degree bounds and divides the dimension of W. -/
theorem extraspecial_module_degree
    (A : NaturalLocalAnalysis T L V d) (he : IsExtraspecial p P)
    (hcard : Nat.card P = p ^ 3)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥) :
    let := S.elementary
    p * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) (Additive W) ∧
      p * orderOf (2 : ZMod p) ∣ Module.finrank (ZMod 2) (Additive W) := by
  let := S.elementary
  let : Fact p.Prime := ⟨S.prime⟩
  let := he
  have hp2 : p ≠ 2 := fun he => S.odd_prime.not_two_dvd_nat (by rw [he])
  exact ⟨Representation.BinaryCoprimeDegree.extraspecial_finrank_le hp2
      S.oddModuleRepresentation (S.oddModuleRepresentation_faithful A he hf) hcard,
    Representation.BinaryCoprimeDegree.extraspecial_degree_dvd_finrank hp2
      S.oddModuleRepresentation hcard (S.oddModuleRepresentation_center_invariants he hf)⟩

/-- In the numerical binary-three branch the actual P-module W is irreducible. -/
theorem extraspecial_binary_three_irreducible
    (A : NaturalLocalAnalysis T L V d) (he : IsExtraspecial p P)
    (hcard : Nat.card P = p ^ 3)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hp : p = 3) (hW : Nat.card W = 64) :
    letI := S.elementary
    S.oddModuleRepresentation.IsIrreducible := by
  let := S.elementary
  subst p
  let := he
  have hdim : Module.finrank (ZMod 2) (Additive W) = 6 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    have heq : (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive W) = 2 ^ 6 := by
      simpa only [Nat.card_zmod, show Nat.card (Additive W) = 64 from hW, Nat.reducePow] using hc.symm
    exact Nat.pow_right_injective (by decide : 1 < 2) heq
  exact Representation.RankTwo.ExtraspecialModel.irreducible_of_faithful_six
    S.oddModuleRepresentation (S.oddModuleRepresentation_faithful A he hf) hcard hdim

/-- Irreducibility forces the normal two-core of H to centralize W. -/
theorem extraspecial_binary_three_module_centralizes_core
    (A : NaturalLocalAnalysis T L V d) (he : IsExtraspecial p P)
    (hcard : Nat.card P = p ^ 3)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hp : p = 3) (hW : Nat.card W = 64) :
    W ≤ centralizer (H.pCoreIn 2 : Set G) := by
  let := S.elementary
  let hPH : P ≤ H := S.overgroup ▸ le_sup_left
  let a : H →* MulAut W := W.normalizerMonoidHom.comp (inclusion S.normalizes)
  let ρ := Representation.elementaryRepresentation (p := 2) a
  let Q := pCore 2 H
  let : Nontrivial (Additive W) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    change 1 < Nat.card W
    rw [hW]
    decide
  let : S.oddModuleRepresentation.IsIrreducible :=
    S.extraspecial_binary_three_irreducible A he hcard hf hp hW
  let Z : Subrepresentation S.oddModuleRepresentation := {
    toSubmodule := Representation.invariants (ρ.comp Q.subtype)
    apply_mem_toSubmodule := fun b w hw =>
      Representation.le_comap_invariants ρ Q (⟨b, hPH b.property⟩ : H) hw }
  have hchar : ringChar (ZMod 2) ≠ 0 := by rw [ZMod.ringChar_zmod_n]; decide
  have hQ : IsPGroup (ringChar (ZMod 2)) Q := by
    simpa only [ZMod.ringChar_zmod_n] using (pCore_isPGroup (p := 2) (G := H))
  obtain ⟨x, hx, hfix⟩ := Representation.pGroup_fix_nonzero_vector hchar hQ (ρ.comp Q.subtype)
  have hZ : Z ≠ ⊥ := by
    intro hbot
    have hh : x ∈ Z := hfix
    rw [hbot] at hh
    exact hx hh
  have htop : Z = ⊤ := (eq_bot_or_eq_top Z).resolve_left hZ
  intro w hw q hq
  obtain ⟨q, hq, rfl⟩ := hq
  have hh : Additive.ofMul (⟨w, hw⟩ : W) ∈ Z := by rw [htop]; trivial
  have hfixed := congrArg (fun y : Additive W => y.toMul.val)
    (hh (⟨q, hq⟩ : Q))
  change (q : G) * w * (q : G)⁻¹ = w at hfixed
  exact mul_inv_eq_iff_eq_mul.mp hfixed

end InvariantOddLocalAnalysis
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

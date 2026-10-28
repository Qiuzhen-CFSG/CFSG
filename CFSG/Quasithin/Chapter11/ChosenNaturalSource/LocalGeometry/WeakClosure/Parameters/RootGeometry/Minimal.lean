module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.Source
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Incidence.Transport
public import Theory.Representation.SpecialLinearThreeFrameGeometry.Transitivity

open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.Section06
open CFSG.Quasithin.ChapterB.QuasisimpleSource
/-!
# Minimal fixed spaces in the linear and symplectic natural modules

At corank m, a nontrivial local residual action supplies an involution whose
entire fixed space is the original subgroup U. A field involution would move
half the natural quotient, strictly more than n. Thus in the SL₃ and Sp₄ rows
the quotient fixed space is a field hyperplane. Equality of coranks identifies
U with its full original preimage, retaining nonsplit central attachments.
Actual special linear flag transitivity and symplectic duality then identify
U with an L-conjugate of V₂ or V₃ respectively.

The G₂ extension uses the same minimal-involution reduction; the Source
endpoint assembles these results with the A₂ calculation and applies them to
the global parameters. Source: Aschbacher--Smith, 11.2.2(3), printed p.768.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.MinimalFixed

section Semilinear
variable {H F W : Type*} [Group H] [Field F] [Finite F] [CharP F 2]
  [Algebra (ZMod 2) F] [AddCommGroup W] [Module F W] [Module (ZMod 2) W]
  [IsScalarTower (ZMod 2) F W] [FiniteDimensional F W]

theorem semilinear_minimal_fixed_hyperplane
    (ρ : Representation (ZMod 2) H W) (hρ : Function.Injective ρ)
    (hdim : 2 < Module.finrank F W) (a : H) (ha : orderOf a = 2)
    (hsmall : fixedCodim ρ (zpowers a) ≤ Module.finrank (ZMod 2) F)
    (σ : F ≃+* F) (hσ : ∀ r v, ρ a (r • v) = σ r • ρ a v) :
    ∃ Q : Submodule F W, Module.finrank F Q + 1 = Module.finrank F W ∧
      fixedSpace ρ (zpowers a) = Q.restrictScalars (ZMod 2) := by
  let : FiniteDimensional (ZMod 2) W := Module.Finite.trans F W
  have hn := Module.finrank_pos (R := ZMod 2) (M := F)
  have ha2 : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  have haa (v : W) : ρ a (ρ a v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ha2, map_one,
      Module.End.one_apply]
  have hσ1 : σ = RingEquiv.refl F := by
    by_contra hne
    let : Nontrivial W := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank F W)
    obtain ⟨v,hv⟩ := exists_ne (0 : W)
    have hσσ : Function.Involutive σ := by
      intro r
      apply smul_left_injective F hv
      have hh := haa (r • v)
      rw [hσ, hσ, haa] at hh
      exact hh
    have he := SymplecticConjugatePair.Ambient.semilinear_involution_twice_codim
      ρ a ha2 σ hσσ hne hσ
    have hd := Module.finrank_mul_finrank (ZMod 2) F W
    nlinarith
  let Q : Submodule F W := {
    carrier := {v | ρ a v = v}
    zero_mem' := map_zero _
    add_mem' := fun hv hw => (ρ a).map_add _ _ |>.trans (congrArg₂ (· + ·) hv hw)
    smul_mem' := fun r v hv => by
      change ρ a (r • v) = r • v
      rw [hσ, hσ1, RingEquiv.refl_apply, show ρ a v = v from hv] }
  have hfix : fixedSpace ρ (zpowers a) = Q.restrictScalars (ZMod 2) := by
    ext v
    exact mem_fixedSpace_zpowers_iff ρ a v
  have hcod : fixedCodim ρ (zpowers a) =
      Module.finrank (ZMod 2) F * Module.finrank F (W ⧸ Q) := by
    unfold fixedCodim
    rw [hfix, (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) Q).finrank_eq,
      Module.finrank_mul_finrank]
  have hpos := fixedCodim_pos_of_faithful ρ hρ
    (show zpowers a ≠ ⊥ by
      intro h
      have ha1 : a = 1 := mem_bot.mp (h ▸ (mem_zpowers a))
      simp [ha1] at ha)
  have hq : Module.finrank F (W ⧸ Q) = 1 := by
    rw [hcod] at hsmall hpos
    nlinarith
  have hd := Q.finrank_quotient_add_finrank
  exact ⟨Q, by omega, hfix⟩
end Semilinear

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

@[expose] def subspace (U : Subgroup G) [IsElementaryAbelian 2 V] : Submodule (ZMod 2) (Additive V) :=
  AddSubgroup.toZModSubmodule 2 (U.subgroupOf V).toAddSubgroup

theorem subspace_finrank_add_corank (U : Subgroup G) [IsElementaryAbelian 2 V] :
    Module.finrank (ZMod 2) (subspace (V := V) U) + subgroupCorank V U =
      Module.finrank (ZMod 2) (Additive V) := by
  have hcardS : Nat.card (subspace (V := V) U) =
      2 ^ Module.finrank (ZMod 2) (subspace (V := V) U) := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := subspace (V := V) U))
  have hcardV : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    change Nat.card V = _ at h
    simpa only [Nat.card_zmod] using h
  have hi : (U.subgroupOf V).index = 2 ^ subgroupCorank V U := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact V.relIndex_eq_two_pow_quotient_finrank U
  have hc := (U.subgroupOf V).card_mul_index
  have hcardB : Nat.card (U.subgroupOf V) = Nat.card (subspace (V := V) U) := rfl
  rw [hcardB, hcardS, hi, hcardV, ← pow_add] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) hc

theorem eq_of_le_of_corank_eq [IsElementaryAbelian 2 V]
    {U W : Subgroup G} (hUW : U ≤ W) (hWV : W ≤ V)
    (hc : subgroupCorank V U = subgroupCorank V W) : U = W := by
  have hi : U.relIndex V = W.relIndex V := by
    rw [V.relIndex_eq_two_pow_quotient_finrank U,
      V.relIndex_eq_two_pow_quotient_finrank W, ← subgroupCorank_eq_quotient_finrank,
      ← subgroupCorank_eq_quotient_finrank, hc]
  have hm := relIndex_mul_relIndex U W V hUW hWV
  rw [hi] at hm
  have h1 : U.relIndex W = 1 := by
    have hz : W.relIndex V ≠ 0 := by
      intro hz
      have hh := W.relIndex_dvd_card V
      rw [hz,zero_dvd_iff] at hh
      exact Nat.card_pos.ne' hh
    exact (Nat.mul_right_cancel (Nat.pos_of_ne_zero hz)) (hm.trans (one_mul _).symm)
  exact le_antisymm hUW (Subgroup.relIndex_eq_one.mp h1)

theorem exists_minimal_involution {c : Coordinates D S.field}
    (hmodel : FixedCodimensions D S c)
    {U : Subgroup G} (hUV : U ≤ V)
    (hcor : subgroupCorank V U = naturalParameter D S c)
    (hCN : normalizer (L : Set G) ⊓ centralizer (U : Set G) ≤ normalizer (V : Set G))
    (hres : ¬ oddCentralizerCondition (normalizer (L : Set G)) V U) :
    letI := D.elementary
    ∃ a : Automizer V, orderOf a = 2 ∧
      fixedCodim (automizerRepresentation V) (zpowers a) = naturalParameter D S c ∧
      fixedSpace (automizerRepresentation V) (zpowers a) = subspace U := by
  let := D.elementary
  let C := normalizer (L : Set G) ⊓ centralizer (U : Set G)
  let I := inducedAutomizer V C
  have hI : I ≠ ⊥ := by
    intro hi
    have hC := (inducedAutomizer_eq_bot_iff hCN).mp hi
    apply hres
    apply oddCentralizerCondition_of_eq
    exact le_antisymm (le_inf inf_le_left hC)
      (inf_le_inf_left _ (Subgroup.centralizer_le hUV))
  have hdim : fixedCodim (automizerRepresentation V) I ≤ naturalParameter D S c := by
    rw [fixedCodim_inducedAutomizer V C hCN, ← hcor]
    exact subgroupCorank_antitone (le_inf hUV (le_centralizer_iff.mpr inf_le_right))
  have hc : Nat.card I ≠ 1 := (I.one_lt_card_iff_ne_bot.mpr hI).ne'
  let p := (Nat.card I).minFac
  have hp : p.Prime := Nat.minFac_prime hc
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := I) p (Nat.minFac_dvd _)
  have ha' : orderOf (a : Automizer V) = p := (Subgroup.orderOf_coe a).trans ha
  have hsmall := (fixedCodim_mono (automizerRepresentation V)
    (zpowers_le.mpr a.property)).trans hdim
  have hp2 : p = 2 := by
    rcases hp.eq_two_or_odd' with he | ho
    · exact he
    · have hh := hmodel.odd_prime_lower p hp ho a ha'
      have hm := naturalParameter_gt_one D S c
      omega
  have ha2 : orderOf (a : Automizer V) = 2 := ha'.trans hp2
  have heq := le_antisymm hsmall (hmodel.involution_lower a ha2)
  refine ⟨a,ha2,heq,?_⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro v hv
    have hfix : v ∈ fixedSpace (automizerRepresentation V) I := by
      apply (mem_fixedSpace_inducedAutomizer V C hCN v).mpr
      exact le_centralizer_iff.mpr (show C ≤ centralizer (U : Set G) from inf_le_right) hv
    intro b
    exact hfix ⟨b,(zpowers_le.mpr a.property) b.property⟩
  · have hs := subspace_finrank_add_corank (V := V) U
    have hf := fixedCodim_add_finrank (automizerRepresentation V) (zpowers (a : Automizer V))
    rw [hcor] at hs
    omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.MinimalFixed

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.MinimalFixed
open FullAutomizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

theorem field_hyperplane_preimage {c : Coordinates D S.field}
    (hmodel : FixedCodimensions D S c) (hm : naturalParameter D S c = S.field.degree)
    (hd : 2 < Module.finrank S.field.Carrier c.Space)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = naturalParameter D S c)
    (hCN : normalizer (L : Set G) ⊓ centralizer (U : Set G) ≤ normalizer (V : Set G))
    (hres : ¬ oddCentralizerCondition (normalizer (L : Set G)) V U)
    (hsemi : ∀ ρ : Representation (ZMod 2) (Automizer V) c.Space,
      (∀ (a : inducedAutomizer V L) v,
        ρ (a : Automizer V) v = c.modelAction (layerEquiv D S c a) v) →
      ∀ a, ∃ σ : S.field.Carrier ≃+* S.field.Carrier,
        ∀ r v, ρ a (r • v) = σ r • ρ a v) :
    ∃ Q : Submodule S.field.Carrier c.Space,
      Module.finrank S.field.Carrier Q + 1 = Module.finrank S.field.Carrier c.Space ∧
      c.preimage Q = U := by
  let := D.elementary
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  obtain ⟨a,ha,hca,hfix⟩ := exists_minimal_involution D S hmodel hUV hcor hCN hres
  obtain ⟨ρ,hρ,he,hL⟩ := exists_faithful_quotient_action D S c
  obtain ⟨σ,hσ⟩ := hsemi ρ hL a
  have hsmall : fixedCodim ρ (zpowers a) ≤ Module.finrank (ZMod 2) S.field.Carrier := by
    rw [OneCohomology.coefficient_finrank_of_card 2 _ S.field.card_eq, ← hm, ← hca]
    exact fixedCodim_le_of_equivariant_surjection (automizerRepresentation V) ρ
      (projectionLinear D S c) (projectionLinear_surjective D S c) he (zpowers a)
  obtain ⟨Q,hQ,hQfix⟩ := semilinear_minimal_fixed_hyperplane ρ hρ hd a ha hsmall σ hσ
  refine ⟨Q,hQ,?_⟩
  have hUQ : U ≤ c.preimage Q := by
    intro x hx
    let v : Additive V := Additive.ofMul ⟨x,hUV hx⟩
    have hv : v ∈ fixedSpace (automizerRepresentation V) (zpowers a) := by
      rw [hfix]
      exact hx
    have hw : projectionLinear D S c v ∈ fixedSpace ρ (zpowers a) := by
      intro b
      exact (he b v).symm.trans (congrArg (projectionLinear D S c) (hv b))
    rw [hQfix] at hw
    exact (c.mem_preimage Q v.toMul).mpr hw
  have hcodQ : subgroupCorank V (c.preimage Q) = S.field.degree := by
    rw [NaturalDimensions.pullback_corank D S c]
    have hquot := Q.finrank_quotient_add_finrank
    rw [show Module.finrank S.field.Carrier (c.Space ⧸ Q) = 1 by omega,mul_one]
  exact (eq_of_le_of_corank_eq hUQ (D.centralQuotientPreimage_le _)
    (hcor.trans (hm.trans hcodQ.symm))).symm

theorem sl3_minimal_fixed
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m))
    (hmodel : FixedCodimensions D S (Coordinates.sl3 m))
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = S.field.degree)
    (hCN : normalizer (L : Set G) ⊓ centralizer (U : Set G) ≤ normalizer (V : Set G))
    (hres : ¬ oddCentralizerCondition (normalizer (L : Set G)) V U) :
    ∃ l : L, (f.Vi 1).map (MulAut.conj (l : G)).toMonoidHom = U := by
  let c := Coordinates.sl3 m
  have hd : Module.finrank S.field.Carrier c.Space = 3 := NaturalDimensions.field_dimension D S c
  dsimp only [c] at hd
  obtain ⟨Q,hQ,hpre⟩ := field_hyperplane_preimage D S hmodel rfl (by omega)
    hUV hcor hCN hres (by
      intro ρ hL a
      let := layer_normal D S
      exact SL3OddNaturalNormalizer.normalizer_semilinear
        (inducedAutomizer V L) (layerEquiv D S c) ρ hL a)
  have hdQ : Module.finrank S.field.Carrier Q = 2 := by omega
  have hQ0 : Q ≠ ⊥ := by intro hz; rw [hz,finrank_bot] at hdQ; contradiction
  obtain ⟨v,hvQ,hv0⟩ := (Submodule.ne_bot_iff Q).mp hQ0
  let P := Submodule.span S.field.Carrier {v}
  have hdP : Module.finrank S.field.Carrier P = 1 := finrank_span_singleton hv0
  obtain ⟨g,_,hg⟩ := Matrix.SpecialLinearGroup.FrameGeometry.exists_flag_map
    (f.space 0) (f.space 1) P Q (f.dimension 0) (f.dimension 1)
      (f.nested (by decide)) hdP hdQ
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvQ))
  obtain ⟨l,hl⟩ := c.quotientMap_surjective g
  refine ⟨l,?_⟩
  change (c.preimage (f.space 1)).map (MulAut.conj (l : G)).toMonoidHom = U
  rw [c.preimage_conjugate,hl]
  exact (congrArg c.preimage hg).trans hpre

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.MinimalFixed

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.MinimalFixed
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.TwoLocalCover
section SymplecticGeometry
variable {F : Type*} [Field F]

private theorem symplectic_hyperplane_ker (Q : Submodule F (Vector F))
    (hQ : Module.finrank F Q + 1 = Module.finrank F (Vector F)) :
    ∃ v : Vector F, v ≠ 0 ∧ Q = (form F v).ker := by
  have hdim : Module.finrank F ((form F).orthogonal Q) = 1 := by
    rw [(form F).finrank_orthogonal (form_nondegenerate (F := F))]
    omega
  let : Nontrivial ((form F).orthogonal Q) := Module.nontrivial_of_finrank_pos (R := F) (M := (form F).orthogonal Q) (by omega)
  obtain ⟨v,hv⟩ := exists_ne (0 : (form F).orthogonal Q)
  have hv0 : (v : Vector F) ≠ 0 := fun h => hv (Subtype.ext h)
  have hf : form F v ≠ 0 := by
    intro hf
    exact hv0 ((form_nondegenerate (F := F)).1 v (by intro w; exact LinearMap.congr_fun hf w))
  have hle : Q ≤ (form F v).ker := by
    intro w hw
    exact (form_alternating (F := F)).isRefl _ _ (v.property w hw)
  refine ⟨v,hv0,Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  omega

theorem symplectic_hyperplane_transitive (P Q : Submodule F (Vector F))
    (hP : Module.finrank F P + 1 = Module.finrank F (Vector F))
    (hQ : Module.finrank F Q + 1 = Module.finrank F (Vector F)) :
    ∃ g : Sp F, P.map (symplecticNatural 2 g) = Q := by
  obtain ⟨v,hv,rfl⟩ := symplectic_hyperplane_ker P hP
  obtain ⟨w,hw,rfl⟩ := symplectic_hyperplane_ker Q hQ
  obtain ⟨g,hg⟩ := nonzero_vector_transitive hv hw
  refine ⟨g,?_⟩
  ext z
  constructor
  · rintro ⟨y,hy,rfl⟩
    change form F w (g • y) = 0
    rw [← hg,preserves_form]
    exact hy
  · intro hz
    refine ⟨g⁻¹ • z,?_,?_⟩
    · change form F v (g⁻¹ • z) = 0
      have hh := preserves_form g v (g⁻¹ • z)
      rw [hg,smul_inv_smul] at hh
      exact hh.symm.trans hz
    · exact smul_inv_smul g z
end SymplecticGeometry

open FullAutomizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

theorem sp4_minimal_fixed
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = S.field.degree)
    (hCN : normalizer (L : Set G) ⊓ centralizer (U : Set G) ≤ normalizer (V : Set G))
    (hres : ¬ oddCentralizerCondition (normalizer (L : Set G)) V U) :
    ∃ l : L, (f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom = U := by
  let c := Coordinates.sp4 m
  have hd : Module.finrank S.field.Carrier c.Space = 4 := NaturalDimensions.field_dimension D S c
  dsimp only [c] at hd
  obtain ⟨Q,hQ,hpre⟩ := field_hyperplane_preimage D S (sp4_fixedCodimensions D S m) rfl
    (by omega) hUV hcor hCN hres (by
      intro ρ hL a
      let := layer_normal D S
      have hq : 2 < Nat.card S.field.Carrier := by
        rw [S.field.card_eq]
        simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary
      have hn := SymplecticNaturalNormalizer.operator_mem_naturalNormalizer
        (inducedAutomizer V L) hq (layerEquiv D S c) ρ hL a
      exact SymplecticNaturalNormalizer.exists_field_twist ⟨SymplecticConjugatePair.Ambient.linearAction ρ a,hn⟩)
  have hP : Module.finrank S.field.Carrier (f.space 2) + 1 =
      Module.finrank S.field.Carrier (Coordinates.sp4 m).Space := by
    rw [f.dimension,hd]
    rfl
  obtain ⟨g,hg⟩ := symplectic_hyperplane_transitive (f.space 2) Q hP hQ
  obtain ⟨l,hl⟩ := c.quotientMap_surjective g
  refine ⟨l,?_⟩
  change (c.preimage (f.space 2)).map (MulAut.conj (l : G)).toMonoidHom = U
  rw [c.preimage_conjugate,hl]
  exact (congrArg c.preimage hg).trans hpre

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.MinimalFixed

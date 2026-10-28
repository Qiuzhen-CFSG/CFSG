module
public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource
public import CFSG.Quasithin.ClassificationModels
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank.Geometry
public import Theory.LinearAlgebra.AlternatingFinrank
public import Theory.LinearAlgebra.AlternatingPlane
public import Theory.SpecificGroups.ProjectiveLinear.FourTwoPGroupBound

/-!
# The nonabelian L₃(2) source geometry and terminal order obstruction

For the actual selected Theorem D counterexample, the earlier natural-module,
structural and escape implications give the two-group closure U, its marked
Frattini subgroup V₁, and V ∩ Z(U) = V₁. The literal projection of the original
order-eight seed into U/Z(U) has kernel V₁ and image of dimension two.
Commutativity of V makes that plane isotropic for the nondegenerate commutator
form. Consequently the quotient has even dimension at least four.

When Z(U) = V₁, this proves that U is extraspecial and either |U| = 32 or
|U| > 64. The actual containment U ≤ T then contradicts any recognition of
an overgroup of T as L₄(2). The bound includes the d = 8 case |U| = 512;
it does not require the strict bound |U| > 512 printed in the final paragraph.
The action-kernel conclusion is separate, since it also uses earlier uniqueness.

The last two theorems assemble the independent nonextraspecial HS recognition,
the order-32 G₂(3) recognition, and the large-case local L₄(2) recognition.
Those three source implications remain explicit. Thus these are conditional
consumers for 14.4.14 and Theorem D, not proofs of either source theorem.
The naturality input is owned by qt-d-1434-source, and the structural and
escape inputs by qt-d-1222-source. Final 14.4.14 assembly remains with
qt-d-14414-source.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, 12.8.4 and
12.8.8, pp.850--852; 14.3.23 and 14.3.26, pp.999--1001; 14.4.3 and the
final paragraph before 14.4.14, pp.1007 and 1012.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneGeometry
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original nonabelian closure has the marked Frattini subgroup and
center intersection. Uniqueness is not needed for these conclusions. -/
theorem source_closure (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    let := chosen.elementary
    IsPGroup 2 F.U ∧ frattini F.U = (F.Vi 1).subgroupOf F.U ∧
      V ⊓ F.ZU = F.Vi 1 := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  have hnat : 3 ≤ 3 → Nonempty (AmbientNaturalMarking L chosen.normalizes 3) :=
    fun _ => ⟨h.naturalMarking⟩
  refine ⟨F.localKernel_UH_isPGroup d.qtke L (normalizer (L : Set G)) F.H
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes structural)
    h.residual hnat (h.point_mem_Hz F alternatives), ?_, ?_⟩
  · exact F.localKernel_frattini_eq_point d.qtke L (normalizer (L : Set G))
      (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes structural)
      h.residual hnat (h.flag_escape F alternatives) hne
  · let := F.localKernel_tilde_seed_elementary
    exact F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking (by decide) hne

/-- The original action kernel, with only the earlier universal uniqueness
input added to the structural and escape implications. -/
theorem source_action_kernel (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) :
    letI := chosen.elementary
    (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  exact F.localKernel_eq_pCore d.qtke L (normalizer (L : Set G)) F.H
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes previous.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique previous.structural previous.uniqueness).2
    (h.seed_centralizer_le previous.structural previous.uniqueness) h.centralizer_L
    (h.point_mem_Hz F previous.alternatives)

/-- The image of the original order-eight seed in U/Z(U) is a plane. -/
theorem seed_hat_dimension (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat] (hc : V ⊓ F.ZU = F.Vi 1) :
    Module.finrank (ZMod 2) (hatSpace F V) = 2 := by
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  let π : V →* F.Uhat := (QuotientGroup.mk' (center F.U)).comp (inclusion hVU)
  have hk : π.ker = (F.Vi 1).subgroupOf V := by
    ext v
    change QuotientGroup.mk' (center F.U) ⟨v, hVU v.property⟩ = 1 ↔
      (v : G) ∈ F.Vi 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hz
      rw [← hc]
      exact ⟨v.property, ⟨_, hz, rfl⟩⟩
    · intro hv
      have hz : (v : G) ∈ F.ZU := (show F.Vi 1 ≤ F.ZU from hc ▸ inf_le_right) hv
      obtain ⟨u, hu, he⟩ := hz
      exact (show u = ⟨v, hVU v.property⟩ from Subtype.ext he) ▸ hu
  have hr : π.range = hatImage F V := by
    ext q
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨⟨v, hVU v.property⟩, v.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  have hkcard : Nat.card π.ker = 2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv]
    simpa using F.card 1 (by decide)
  have hvcard : Nat.card V = 8 := by
    simpa [F.last] using F.card 3 (by decide)
  have hcard := π.ker.card_mul_index
  rw [index_ker, hkcard, hvcard, hr] at hcard
  have hhat : Nat.card (hatSpace F V) = 4 := by
    change Nat.card (hatImage F V) = 4
    omega
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := hatSpace F V)
  rw [Nat.card_zmod, hhat] at hd
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hd.symm

/-- Commutativity of the actual seed makes that plane isotropic. -/
theorem quotient_dimension (F : InvariantFlag T V 3) [IsElementaryAbelian 2 V]
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hc : V ⊓ F.ZU = F.Vi 1) :
    let := F.uhat_elementary_of_point (by decide) htwo hphi
    4 ≤ Module.finrank (ZMod 2) (Additive F.Uhat) ∧
      Even (Module.finrank (ZMod 2) (Additive F.Uhat)) := by
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  let B := F.uhatBilinearForm (by decide) htwo hphi
  have hi : ∀ x ∈ hatSpace F V, ∀ y ∈ hatSpace F V, B x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, hea⟩ := (show x.toMul ∈ hatImage F V from hx)
    obtain ⟨b, hb, heb⟩ := (show y.toMul ∈ hatImage F V from hy)
    have hab : Commute a b := by
      change a * b = b * a
      exact Subtype.ext (congrArg (fun v : V => (v : G))
        (mul_comm (⟨a, ha⟩ : V) ⟨b, hb⟩))
    have hz : F.uhatCommutator htwo (QuotientGroup.mk' (center F.U) a)
        (QuotientGroup.mk' (center F.U) b) = 1 := by
      apply Subtype.ext
      rw [F.uhatCommutator_apply_mk]
      change ⁅a, b⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr hab.eq
    change B (Additive.ofMul x.toMul) (Additive.ofMul y.toMul) = 0
    rw [← hea, ← heb, F.uhatBilinearForm_apply, hz]
    simp only [map_one]
    rfl
  have hb := B.twice_finrank_le_of_isotropic
    (F.uhatBilinearForm_nondegenerate (by decide) htwo hphi) (hatSpace F V) hi
  rw [seed_hat_dimension F hc] at hb
  exact ⟨hb, AlternatingForm.even_finrank B
    (F.uhatBilinearForm_isAlt (by decide) htwo hphi)
    (F.uhatBilinearForm_nondegenerate (by decide) htwo hphi)⟩

/-- The closure is contained in the original Sylow subgroup, not merely
isomorphic to a two-subgroup elsewhere. -/
theorem source_closure_le_sylow (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) : F.U ≤ (T : Subgroup G) := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  exact (F.localKernel_closure d.qtke L (normalizer (L : Set G)) F.H
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.point_mem_Hz F alternatives)).2.2.1.1

omit [Finite G] in
/-- Equality of the ambient center with the marked point is also the literal
intrinsic equality needed for the extraspecial quotient. -/
theorem center_point (F : InvariantFlag T V 3) (hZ : F.ZU = F.Vi 1) :
    center F.U = (F.Vi 1).subgroupOf F.U := by
  rw [← hZ]
  ext x
  exact ⟨fun hx => mem_map_of_mem _ hx, fun ⟨y, hy, he⟩ =>
    (show y = x from Subtype.ext he) ▸ hy⟩

/-- The original extraspecial case has order 32, or order strictly greater
than 64. This is the bound needed by the actual L₄(2) terminal obstruction. -/
theorem source_extraspecial_order (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) :
    IsExtraspecial 2 F.U ∧ (Nat.card F.U = 32 ∨ 64 < Nat.card F.U) := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, hc⟩ := source_closure d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  have hcenter : Nat.card (center F.U) = 2 := by
    rw [center_point F hZ]
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (show F.Vi 1 ≤ F.U from (F.le_seed 1).trans (le_conjugateSpanBy V F.H))).toEquiv).trans
      (by simpa using F.card 1 (by decide))
  refine ⟨⟨hcenter, inferInstance,
    QuotientGroup.nontrivial_iff.mpr (fun ht => hne (center_eq_top_iff.mp ht))⟩, ?_⟩
  obtain ⟨hd, heven⟩ := quotient_dimension F htwo hphi hc
  let r := Module.finrank (ZMod 2) (Additive F.Uhat)
  have hcard : Nat.card F.U = 2 ^ (r + 1) := by
    have hqcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    rw [Nat.card_zmod] at hqcard
    rw [card_eq_card_quotient_mul_card_subgroup (center F.U), hcenter]
    change Nat.card (Additive F.Uhat) * 2 = _
    rw [hqcard, pow_succ]
  by_cases hr : r = 4
  · exact Or.inl (by rw [hcard, hr]; decide)
  · right
    obtain ⟨k, hk⟩ := heven
    have hlarge : 6 < r + 1 := by dsimp [r]; omega
    rw [hcard]
    exact (by decide : 64 = 2 ^ 6) ▸ Nat.pow_lt_pow_right (by decide) hlarge

/-- Application to the actual recognized overgroup. The source geometry
supplies both U ≤ T and its order obstruction; only the independent local
recognition of a subgroup containing T remains explicit. -/
theorem source_large_overgroup_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : Nat.card F.U ≠ 32)
    (G₀ : Subgroup G) (hTG₀ : (T : Subgroup G) ≤ G₀)
    (e : G₀ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) : False := by
  have hcard := (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).2
  have hUT := source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hbound := Matrix.PSL4Two.card_twoGroup_le_sixtyFour T.isPGroup'
    (e.toMonoidHom.comp (inclusion hTG₀)) (e.injective.comp (inclusion_injective hTG₀))
  have hle := Nat.card_le_card_of_injective (inclusion hUT) (inclusion_injective hUT)
  omega

/-- Conditional final assembly of the three source branches. The first two
premises are the independent recognitions 14.3.26 and 14.4.3; the third is
14.4.13 on an actual subgroup containing T. This theorem discharges the
numerical and Sylow premises of the terminal contradiction, not those three
recognitions themselves. -/
theorem recognition_of_source_branches (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (nonextraspecial : F.ZU ≠ F.Vi 1 → Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier))
    (small : F.ZU = F.Vi 1 → Nat.card F.U = 32 →
      Nonempty (G ≃* Atlas.G2.Model (ZMod 3)))
    (large : F.ZU = F.Vi 1 → 64 < Nat.card F.U →
      ∃ G₀ : Subgroup G, (T : Subgroup G) ≤ G₀ ∧
        Nonempty (G₀ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) := by
  by_cases hZ : F.ZU = F.Vi 1
  · rcases (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).2
      with hs | hl
    · exact Or.inr (small hZ hs)
    · obtain ⟨G₀, hTG₀, e⟩ := large hZ hl
      obtain ⟨e⟩ := e
      exact False.elim (source_large_overgroup_exclusion d earlier hq chosen
        structural alternatives F hne hZ (by omega) G₀ hTG₀ e)
  · exact Or.inl (nonextraspecial hZ)

/-- The same assembled actual isomorphisms feed the complete Theorem D
catalogue. No order or simplicity certification of additional models is used. -/
theorem theoremD_of_source_branches (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (nonextraspecial : F.ZU ≠ F.Vi 1 → Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier))
    (small : F.ZU = F.Vi 1 → Nat.card F.U = 32 →
      Nonempty (G ≃* Atlas.G2.Model (ZMod 3)))
    (large : F.ZU = F.Vi 1 → 64 < Nat.card F.U →
      ∃ G₀ : Subgroup G, (T : Subgroup G) ≤ G₀ ∧
        Nonempty (G₀ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))) :
    ClassificationModels.IsTheoremDExceptionalModel G := by
  rcases recognition_of_source_branches d earlier hq chosen structural alternatives F hne
    nonextraspecial small large with hs | hg
  · exact .sporadic .hs (by simp) hs
  · exact .g2_three ⟨ZMod 3, inferInstance, inferInstance, Nat.card_zmod 3, hg⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneGeometry

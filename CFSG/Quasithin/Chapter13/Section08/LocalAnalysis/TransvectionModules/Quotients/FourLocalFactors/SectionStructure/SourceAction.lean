module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.SectionStructure
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Extensions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.NaturalSetup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import Theory.Representation.SixLetterRadicalDisplacement.RadicalGeometry
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.CComponent.Basic

/-!
# The marked source calculation on U_H/V₁

The original natural L-action makes C_L(V) a two-group, so the standing
C_T(V)=O₂(LT) identity places the actual bar kernel in T. This argument
retains the original natural V separately from U_H/V₁. Its irreducibility
also proves V=⟨V₃^L⟩ from the nonzero flag and C_V(L)=1.

For the latter section we retain an actual surjective homomorphism with
kernel V₁ and the source H/O₂(H) conjugation action. The exact F.9.2(3)
kernel statement proves faithfulness. The proved normalizer of the natural
A₆ image extends the prescribed K* action to a compatible six-letter action
of H*. An element centralizing V fixes the marked plane V₃/V₁ pointwise.
The concrete plane-fixer and radical-displacement calculations then give
[U_H,C_{LT}(V)]≤V₃, the local input needed by SectionStructure.

Finally, subnormal perfectness and the literal set product H=KT identify K
with O²(H). This proves relative normality without replacing the product by
a join or assuming a component-normality conclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.6(4), printed p.948 (PDF p.965), using the original natural action
13.5.2(3), F.9.2(3), and the weight-four plane marking in 13.7.6(3).
The intrinsic model results reused here are proved independently of §13.8.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.SectionStructure
open ComponentSieve.SixAndG2.NaturalSix
open ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Representation.SixLetterRadicalDisplacement
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]

/-- The genuine original natural L-action makes C_L(V) a two-group. -/
theorem original_centralizer_le_core (L T V V₁ : Subgroup G)
    (n : NaturalSetup L T V V₁) : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2 := by
  intro x hx
  let l : L := ⟨x, hx.1⟩
  let p : (L ⊔ T : Subgroup G) := inclusion le_sup_left l
  have hp : n.permutation p = 1 := by
    apply symmetricAction_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v, hv⟩ := n.naturalMap_surjective (Multiplicative.ofAdd w)
    have he := n.conjugation p v
    have hc : V.normalizerMonoidHom ⟨p.val, n.normalizes_V p.property⟩ v = v := by
      apply Subtype.ext
      change x * (v : G) * x⁻¹ = (v : G)
      rw [← mem_centralizer_iff.mp hx.2 v v.property, mul_inv_cancel_right]
    rw [hc, hv] at he
    change w = symmetricAction (n.permutation p) w at he
    simpa only [map_one, Module.End.one_apply] using he.symm
  have he : n.model (QuotientGroup.mk' (pCore 2 L) l) = 1 := by
    apply Subtype.ext
    exact (n.model_compatible l).symm.trans hp
  have hl : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
    (n.model.injective (he.trans n.model.map_one.symm))
  exact ⟨l, hl, rfl⟩

theorem original_sylow_isPGroup (L T V V₁ : Subgroup G)
    (n : NaturalSetup L T V V₁) : IsPGroup 2 T := by
  have hp := n.sylow.isPGroup'.map (L ⊔ T).subtype
  rwa [n.sylow_eq, map_subgroupOf_eq_of_le (show T ≤ L ⊔ T from le_sup_right)] at hp

theorem source_barKernel_le_T (L T V V₁ : Subgroup G)
    (n : NaturalSetup L T V V₁)
    (hCT : T ⊓ centralizer (V : Set G) = (L ⊔ T).pCoreIn 2) :
    (L ⊔ T) ⊓ centralizer (V : Set G) ≤ T := by
  have he := barKernel_map_eq_core L T V (original_sylow_isPGroup L T V V₁ n)
    n.normalizes_L n.normalizes_V
    ((isPGroup_pCoreIn 2 L).to_le (original_centralizer_le_core L T V V₁ n)) hCT
  rw [barKernel_map, ← hCT] at he
  exact he.le.trans inf_le_left

/-- Faithfulness of the original natural section when C_V(L)=1. -/
theorem original_naturalMap_injective (L T V V₁ : Subgroup G)
    (n : NaturalSetup L T V V₁) (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Function.Injective n.naturalMap := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [n.naturalMap_kernel]
  apply le_bot_iff.mp
  intro v hv
  apply Subtype.ext
  have hm : (v : G) ∈ V ⊓ centralizer (L : Set G) := ⟨v.property, hv⟩
  rwa [hfixed] at hm

/-- Irreducibility of the original natural L-module generates V from the
nonzero marked V₃. This uses the original module, not U_H/V₁. -/
theorem original_V_generated (L T V V₁ V₃ : Subgroup G)
    (n : NaturalSetup L T V V₁) (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hflag : V₃ ≤ V) (hne : V₃ ≠ ⊥) : V = conjugateSpanBy V₃ L := by
  let B := conjugateSpanBy V₃ L
  have hBV : B ≤ V := conjugateSpanBy_le hflag (le_sup_left.trans n.normalizes_V)
  let S : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)) :=
    AddSubgroup.toZModSubmodule 2 ((B.subgroupOf V).map n.naturalMap).toAddSubgroup'
  have hstable (k : alternatingGroup (Fin 6)) (v : BinaryPermutation.natural (Fin 6))
      (hv : v ∈ S) : alternatingAction k v ∈ S := by
    obtain ⟨a, ha⟩ := n.model.surjective k
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) a
    obtain ⟨b, hb, rfl⟩ := hv
    let p : (L ⊔ T : Subgroup G) := inclusion le_sup_left l
    have hp : n.permutation p = k.val := by rw [n.model_compatible, hl, ha]
    have hc := n.conjugation p b
    rw [hp] at hc
    refine ⟨V.normalizerMonoidHom ⟨p.val, n.normalizes_V p.property⟩ b, ?_, ?_⟩
    · exact (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ L l.property) b).mp hb
    · exact congrArg Multiplicative.ofAdd hc
  let W : Subrepresentation alternatingAction := ⟨S, fun k _ hv => hstable k _ hv⟩
  let _ : alternatingAction.IsIrreducible :=
    BinaryPermutation.alternatingNatural_isIrreducible (by decide)
  have hW : W = ⊤ := by
    rcases eq_bot_or_eq_top W with hbot | htop
    · exfalso
      apply hne
      apply le_bot_iff.mp
      intro v hv
      have hvV := hflag hv
      have hm : (n.naturalMap ⟨v, hvV⟩).toAdd ∈ W.toSubmodule :=
        ⟨⟨v, hvV⟩, le_conjugateSpanBy V₃ L hv, rfl⟩
      rw [hbot] at hm
      have hz : n.naturalMap ⟨v, hvV⟩ = n.naturalMap 1 := by
        change (n.naturalMap ⟨v, hvV⟩).toAdd = 0 at hm
        change n.naturalMap ⟨v, hvV⟩ = 1 at hm
        simpa only [map_one] using hm
      exact congrArg Subtype.val (original_naturalMap_injective L T V V₁ n hfixed hz)
    · exact htop
  apply le_antisymm _ hBV
  intro v hv
  have hm : (n.naturalMap ⟨v, hv⟩).toAdd ∈ S := by
    change (n.naturalMap ⟨v, hv⟩).toAdd ∈ W.toSubmodule
    rw [hW]
    trivial
  obtain ⟨b, hb, he⟩ := hm
  have heq : b = ⟨v, hv⟩ := original_naturalMap_injective L T V V₁ n hfixed he
  change (b : G) ∈ B at hb
  have heq' : (b : G) = v := congrArg Subtype.val heq
  simpa only [heq'] using hb

/-- F.9.2(3)'s exact kernel identity makes the literal section action faithful. -/
theorem section_action_faithful (H B Z : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) U) (s : ConjugationSection H B Z ρ)
    (hker : ∀ h : H, (∀ u : B, ⁅(h : G), (u : G)⁆ ∈ Z) → h ∈ pCore 2 H) :
    Function.Injective ρ := by
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  apply le_bot_iff.mp
  intro a ha
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) a
  apply (QuotientGroup.eq_one_iff h).mpr
  apply hker h
  intro u
  apply (s.quotient_eq_zero_iff ⟨⁅(h : G), (u : G)⁆, s.commutator_mem h u⟩).mp
  rw [← s.displacement]
  have he : ρ (QuotientGroup.mk' (pCore 2 H) h) = 1 := ha
  rw [he, Module.End.one_apply, sub_self]

/-- Fixing the canonical weight-four plane forces every natural displacement
back into that plane. -/
theorem natural_displacement_of_plane_fixer (g : Equiv.Perm (Fin 6))
    (hg : ∀ v ∈ canonicalPlane, symmetricAction g v = v) (v : BinaryPermutation.natural (Fin 6)) :
    symmetricAction g v - v ∈ canonicalPlane := by
  have hD := (natural_plane_fixer g).mp hg
  have hbound : naturalDisplacement Theory.SpecificGroups.SymmetricSix.BinaryFlags.D ≤
      canonicalPlane := by
    rw [← map_displacement, ← map_pairSpace]
    exact Submodule.map_mono (displacement_le_pairSpace _ le_rfl)
  exact hbound (Coinvariants.sub_mem_ker
    (ρ := symmetricAction.comp Theory.SpecificGroups.SymmetricSix.BinaryFlags.D.subtype)
    ⟨g, hD⟩ v)

/-- In the literal product H=KT, the subnormal perfect component K is O²(H).
Consequently its normality does not require an extra source premise. -/
theorem component_normal_of_product [Finite G] (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hT : IsPGroup 2 T)
    (hprod : ∀ h : H, ∃ k ∈ K, ∃ t ∈ T, k * t = (h : G)) :
    (K.subgroupOf H).Normal := by
  let _ := hK.perfect
  have hp : IsPPerfect 2 (K.subgroupOf H) := by
    intro N hN hq
    let _ := hN
    have hs : Subsingleton ((K.subgroupOf H) ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent ((K.subgroupOf H) ⧸ N) hq.isNilpotent
    apply eq_top_iff.mpr
    intro k _
    exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
  have he : pResidual 2 H = K.subgroupOf H :=
    pResidual_eq_of_subnormal_product (K.subgroupOf H) (T.subgroupOf H)
      hK.subnormal hp hT.comap_subtype (by
        intro h
        obtain ⟨k, hk, t, ht, he⟩ := hprod h
        exact ⟨⟨k, hKH hk⟩, hk, ⟨t, hTH ht⟩, ht, Subtype.ext he⟩)
  rw [← he]
  infer_instance

/-- The source kernel fixes V₃ pointwise. Its action on U_H/V₁ therefore
lies in the concrete plane fixer and moves U_H only into V₃. -/
theorem UH_barKernel_commutator (L H K T V V₁ V₃ : Subgroup G)
    (n : NaturalSetup L T V V₁)
    (hCT : T ⊓ centralizer (V : Set G) = (L ⊔ T).pCoreIn 2)
    (hTH : T ≤ H) (hflag : V₁ ≤ V₃) (hV₃ : V₃ ≤ V)
    [(Source.starImage H K).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) U)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hker : ∀ h : H, (∀ u : Source.UH H V₃, ⁅(h : G), (u : G)⁆ ∈ V₁) → h ∈ pCore 2 H)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (E : U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (he : ∀ k : Source.starImage H K, ∀ u, E (ρ k u) = alternatingAction (eK k) (E u))
    (hmark : (s.image V₃).map E.toLinearMap = canonicalPlane) :
    ⁅Source.UH H V₃, (L ⊔ T) ⊓ centralizer (V : Set G)⁆ ≤ V₃ := by
  obtain ⟨f, _hf, _hK, hf, _cases⟩ :=
    faithful_extension_of_normalizer normalizer_alternatingImage (Source.starImage H K) ρ
      (section_action_faithful H _ V₁ ρ s hker) eK E he
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha u hu
  let aH : H := ⟨a, hTH (source_barKernel_le_T L T V V₁ n hCT ha)⟩
  let uH : Source.UH H V₃ := ⟨u, hu⟩
  let g := f (QuotientGroup.mk' (pCore 2 H) aH)
  have hfix : ∀ v ∈ canonicalPlane, symmetricAction g v = v := by
    intro v hv
    rw [← hmark] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨b, hb, rfl⟩ := (s.mem_image V₃ w).mp hw
    change symmetricAction (f (QuotientGroup.mk' (pCore 2 H) aH))
      (E (s.quotient b).toAdd) = E (s.quotient b).toAdd
    rw [← hf]
    apply congrArg E
    rw [s.conjugates]
    apply congrArg (fun x : Source.UH H V₃ => (s.quotient x).toAdd)
    apply Subtype.ext
    change a * (b : G) * a⁻¹ = (b : G)
    rw [← mem_centralizer_iff.mp ha.2 b (hV₃ hb), mul_inv_cancel_right]
  have hd := natural_displacement_of_plane_fixer g hfix (E (s.quotient uH).toAdd)
  change symmetricAction (f (QuotientGroup.mk' (pCore 2 H) aH))
    (E (s.quotient uH).toAdd) - E (s.quotient uH).toAdd ∈ canonicalPlane at hd
  rw [← hf, ← map_sub, s.displacement, ← hmark] at hd
  have hc : (s.quotient ⟨⁅a, u⁆, s.commutator_mem aH uH⟩).toAdd ∈ s.image V₃ := by
    obtain ⟨w, hw, hew⟩ := hd
    exact E.injective hew ▸ hw
  exact (s.quotient_mem_image_iff V₃ hflag _).mp hc

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.SectionStructure

end

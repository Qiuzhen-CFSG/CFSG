module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.RudvalisNormalizer.Transport
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.RudvalisNormalizer.SourceMarking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.RudvalisNormalizer.Complement

/-!
# The original V-normalizer in the recognized Rudvalis cover

Restrict the recognition map to the original V. Its kernel is trivial because
V meets the covering line trivially. A marked image identifies V with the
literal Ru eight, compatibly with conjugation. The model's full normalizer
bound gives one inclusion for the original component normalizer. SourceMarking
derives V = [V,L₁] and aligns its image using the actual Sylow subgroup.
Complement constructs an invariant complement by averaging over an odd orbit;
uniqueness for the original L₁ identifies it with V and gives the reverse
inclusion. The intrinsic preimage results now give two-perfectness, the actual
two-core quotient isomorphism with Aut(V), and center order two.

The source assembly discharges every marking and normalization premise. Its
only recognition input is the specified surjection Lᵤ → Ru with kernel ⟨u⟩.
The final application supplies all three normalizer facts to Basic's Sylow
contradiction. Ru recognition and the earlier 12.2.2 structural theorem remain
with the parent quasisimple-exclusion assembly.

Source: Aschbacher–Smith 14.7.68(2), printed p.1071 (PDF p.1088).
-/

@[expose] public section
noncomputable section
open Subgroup Representation Theory.GroupTheory
open Rudvalis.SylowOvergroups Rudvalis.CoreQuotients
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable {d : Data T L V F W} {u : F.U} {Lu : Subgroup G}

/-- Conditional assembly on the literal source subgroups. The marked-eight
placement and complement-normalization premises must still be proved from the
source configuration; this theorem alone is not the Ru-normalizer calculation. -/
theorem fixedNormalizer_model_of_marked_preimage
    (earlier : d.ModuleSeparation) (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hne : (u : G) ≠ 1) (Lu : Subgroup G) (hLu : Lu ≤ d.fixedCentralizer u)
    (hout : ¬ Lu ≤ F.H) (hq : IsQuasisimple Lu) (r : d.FixedRudvalisCover u Lu)
    (hV : V ≤ Lu) (hmap : (V.subgroupOf Lu).map r.projection = elementary 2)
    (hnorm : r.max4Preimage ≤ (normalizer (V : Set G)).subgroupOf Lu) :
    IsPPerfect 2 (d.fixedComponentNormalizer Lu) ∧
      Nonempty (((d.fixedComponentNormalizer Lu) ⧸ pCore 2 (d.fixedComponentNormalizer Lu)) ≃* MulAut V) ∧
      Nat.card (center (d.fixedComponentNormalizer Lu)) = 2 := by
  have hdisj := d.fixed_line_inf_seed_eq_bot earlier u hu hne
    (fun hc => hout (hLu.trans hc))
  let eJ := r.normalizerEquiv hV hmap hnorm
  let eV := r.seedEquiv hV hdisj hmap
  refine ⟨(r.max4Preimage_twoPerfect hne hLu hq).of_surjective eJ.symm.toMonoidHom eJ.symm.surjective, ?_, ?_⟩
  · let qJ := QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
    exact ⟨qJ.trans ((r.max4PreimageQuotientEquiv hne).trans (MulAut.congr eV.symm))⟩
  · rw [Nat.card_congr (centerCongr eJ).toEquiv]
    exact r.max4Preimage_center_card hne hLu

/-- The intrinsic normalizer calculation in the recognized Ru branch of
14.7.68(2). Generation, containment, the marked eight, and preservation of the
original complement are all derived from the supplied source configuration. -/
theorem fixedNormalizer_model_of_rudvalisCover
    (earlier : d.ModuleSeparation) (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hne : (u : G) ≠ 1) (hfix : d.FixedModuloPoint u)
    (hNK : normalizer (K F : Set G) = F.H) (hmax : IsMaximalTwoLocal F.H)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    (Lu : Subgroup G) (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal)
    (hKLu : K F < Lu) (hout : ¬ Lu ≤ F.H) (hq : IsQuasisimple Lu)
    (r : d.FixedRudvalisCover u Lu) :
    IsPPerfect 2 (d.fixedComponentNormalizer Lu) ∧
      Nonempty (((d.fixedComponentNormalizer Lu) ⧸ pCore 2 (d.fixedComponentNormalizer Lu)) ≃* MulAut V) ∧
      Nat.card (center (d.fixedComponentNormalizer Lu)) = 2 := by
  obtain ⟨hgen, hV, g, hmap⟩ := d.fixedRudvalis_originalEight earlier u hu hne
    hfix hNK hmax hsyl Lu hLu hc hn hKLu hout hq r
  have hnorm := (r.align g).max4Preimage_le_seed_normalizer earlier hu hne
    hfix hNK hmax hsyl hLu hc hn hKLu hout hq hgen hV hmap
  exact d.fixedNormalizer_model_of_marked_preimage earlier u hu hne Lu hLu
    hout hq (r.align g) hV hmap hnorm

/-- Consumer application to the original fixed-centralizer configuration.
Only recognition of the covering group and the genuine earlier structural
theorem remain explicit; no intrinsic normalizer fact is assumed. -/
theorem false_of_fixedRudvalisCover
    (earlier : d.ModuleSeparation)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hNK : normalizer (K F : Set G) = F.H)
    (hmax : IsMaximalTwoLocal F.H)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    (Lu : Subgroup G) (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal)
    (hKLu : K F < Lu) (hout : ¬ Lu ≤ F.H) (hq : IsQuasisimple Lu)
    (r : d.FixedRudvalisCover u Lu) : False := by
  obtain ⟨hp, ⟨e⟩, hcenter⟩ := d.fixedNormalizer_model_of_rudvalisCover earlier
    u hu hne hfix hNK hmax hsyl Lu hLu hc hn hKLu hout hq r
  exact d.false_of_fixedNormalizer_model earlier structural u hu hne hfix hmax
    hsyl hLu hn hout r hp e hcenter

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

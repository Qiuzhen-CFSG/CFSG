module

public import BenderSuzuki.ZD.Recognition.Interfaces
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.NormalExclusion
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.SimpleNormal
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.Centralizers
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.SylowConfiguration
public import Theory.GroupTheory.OddCoreCentralizerContainment

/-!
# The final odd-core contradiction in the ZD simplicity reduction

This module proves the last coprime-action step of GLS Proposition 4.3.
Lemma 4.10(b) puts an odd core outside `M`, while 4.10(c) puts every central
involution centralizer inside `M`. The noncyclic first omega subgroup of the
Sylow center then forces that same odd core into `M`.

The final theorem constructs the simple normal subgroup of Lemma 4.9,
applies the centralizer conclusions of Lemma 4.10, and supplies the Sylow
configuration. It derives simplicity from the preliminary, radical and
local-embedding hypotheses; the minimal-reduction owner supplies those
independent earlier-source premises.

Source: GLS, Volume 4, Chapter 2, Proposition 4.3, final paragraph;
`refs/KGroup/GLS4/Chapter2.tex`, lines 711–719.
-/

namespace BenderSuzuki.ZD
open PFAppendixIII Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The final contradiction of GLS Proposition 4.3, once Lemma 4.10 and the
Sylow configuration of its last paragraph have been established. -/
public theorem false_of_centralizer_oddCore_configuration
    (z : G) (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzc : ∀ s : S, Commute z (s : G))
    (hncyc : ¬ IsCyclic (omega₁ (Subgroup.center S) (p := 2)))
    (u : G) (huS : u ∈ (S : Subgroup G)) (hu : PFAppendixIII.IsInvolution u)
    (huM : ¬ Subgroup.centralizer ({u} : Set G) ≤ M)
    (hlocal : ∀ v : G, PFAppendixIII.IsInvolution v → Commute v z →
      ¬ Subgroup.centralizer ({v} : Set G) ≤ M →
      (¬ (pPrimeCore 2 (Subgroup.centralizer ({v} : Set G))).map
          (Subgroup.centralizer ({v} : Set G)).subtype ≤ M) ∧
      ¬ ∃ T : Sylow 2 G, v ∈ (T : Subgroup G) ∧
        ∀ t : T, Commute v (t : G)) : False := by
  have hodd := (hlocal u hu (hzc ⟨u, huS⟩).symm huM).1
  apply hodd
  apply centralizer_oddCore_le_of_noncyclic_omega_center S u huS hncyc
  intro v hv hvS hvc
  by_contra hnot
  exact (hlocal v hv (hvc ⟨z, hzS⟩) hnot).2 ⟨S, hvS, hvc⟩

/-- GLS Proposition 4.3, with all Lemma 4.9, Lemma 4.10 and Sylow
configuration inputs discharged from the preceding source hypotheses. -/
public theorem isSimple_of_preliminary_and_local
    {Z : Set G} (h : MinimalCounterexample Z M)
    (hgen : Subgroup.closure Z = ⊤)
    (hclass : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z)
    (htwo : ∀ z ∈ Z, ∃ S : Sylow 2 G, z ∈ S ∧ ∀ s : S, Commute z (s : G))
    (hf : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M ∧ ControlsFusionIn M (S : Subgroup G))
    (hsol : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hlocal : ∀ H : Subgroup G, H ≠ ⊤ → ¬ H ≤ M →
      (∃ z ∈ Z, z ∈ H ∧ z ∈ M) →
      IsStronglyEmbedded ((M.comap H.subtype).comap
        (Subgroup.closure (H.subtype ⁻¹' Z)).subtype)) : IsSimpleGroup G := by
  by_contra hnot
  obtain ⟨z, hz, hzM⟩ := h.disconnected.nonempty
  obtain ⟨N, hN, hNs, hNeven, hNz, hzN⟩ :=
    simple_normal_subgroup_of_nonsimple h.disconnected hgen hclass htwo hf hsol hlocal hz hzM hnot
  let : N.Normal := hN
  let : IsSimpleGroup N := hNs
  obtain ⟨S, _, hzS, hzc, hcyc, u, huS, hu, huM⟩ :=
    exists_sylow_configuration_of_even_normal h.disconnected hclass htwo hf hz hzM N hNeven hzN
  exact false_of_centralizer_oddCore_configuration z S hzS hzc hcyc u huS hu huM
    (Centralizers.centralizer_oddCore_configuration h hsol hlocal N hNeven hz hzM hNz hzN)

end BenderSuzuki.ZD

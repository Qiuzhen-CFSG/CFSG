module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalDefs
public import Theory.GroupTheory.PGroup.Omega

/-!
# Relocating the escaping component to the omega centralizer

An overgroup of a Sylow subgroup with nontrivial two-core makes that Sylow
nontrivial. Its central omega subgroup is then nontrivial and lies in the
two-core of its own centralizer. If the residual of H centralizes omega,
the Sylow supplement places all of H in this same centralizer.

The cubic selected by the local sieve still escapes the residual normalizer
after this relocation. Applying the sieve again therefore supplies a
C-component relative to the whole omega centralizer, with its literal
two-core quotient model. We retain the full moved module from the first
centralization argument. The sieve and the centralization/module argument
remain explicit prerequisites; this module does not claim to prove them.

Source: Aschbacher--Smith, 5.1.13(4--6), printed pp.637--638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem omega_ne_bot {T : Sylow 2 G} (hT : (T : Subgroup G) ≠ ⊥) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ := by
  let : Nontrivial (T : Subgroup G) := (nontrivial_iff_ne_bot _).mpr hT
  let : Nontrivial (center (T : Subgroup G)) := T.isPGroup'.center_nontrivial
  have hc := T.isPGroup'.to_subgroup (center (T : Subgroup G))
  obtain ⟨n, hn, he⟩ := hc.nontrivial_iff_card.mp inferInstance
  have hd : 2 ∣ Nat.card (center (T : Subgroup G)) := by
    rw [he]
    exact dvd_pow_self 2 (Nat.ne_of_gt hn)
  have hne := omega₁_map_subtype_ne_bot (G := (T : Subgroup G))
    (center (T : Subgroup G)) 2 hd
  intro hbot
  apply hne
  apply Subgroup.map_injective (f := (T : Subgroup G).subtype) Subtype.val_injective
  simpa [Stellmacher.omegaOneCenterAmbient] using hbot

/-- The original central omega is a nontrivial normal two-subgroup of its
centralizer. This supplies the membership in H required for relocation. -/
theorem omegaCentralizer_mem_H {T : Sylow 2 G}
    (hT : (T : Subgroup G) ≠ ⊥) : omegaCentralizer T ∈ Chapter1.H G := by
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  have hZT : Z ≤ (T : Subgroup G) := fun z hz =>
    ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hZC : Z ≤ omegaCentralizer T := hZT.trans sylow_le_omegaCentralizer
  have hc : Z ≤ (omegaCentralizer T).pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      (Stellmacher.omegaOneCenterAmbient_elementaryAbelian _).isPGroup hZC
      (Subgroup.centralizer_le_normalizer _)
  exact fun hb => omega_ne_bot hT (bot_unique (hc.trans_eq hb))

/-- Once its residual centralizes omega, an actual member H of H(T) lies
in the omega centralizer, which itself belongs to H(H). -/
theorem omegaCentralizer_mem_HOver_of_residual {T : Sylow 2 G} {H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hR : residual H ≤ omegaCentralizer T) :
    omegaCentralizer T ∈ Chapter1.HOver G (H : Set G) := by
  have hc : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hH.2)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.2] at hh
  have hT : (T : Subgroup G) ≠ ⊥ := fun hb =>
    hH.1 (bot_unique (hc.trans_eq hb))
  exact ⟨omegaCentralizer_mem_H hT, (residual_le_omegaCentralizer_iff hH.2).mp hR⟩

omit [Finite G] in
/-- The actual escaping cubic remains in the intersected Cartan after
relocation. No normality of Y in the omega centralizer is required. -/
theorem LocalCartanWitness.escape_in_omegaCentralizer
    {T : Sylow 2 G} {H A Y X D : Subgroup G}
    (d : LocalCartanWitness T H A Y X D) (hXC : X ≤ omegaCentralizer T) :
    ¬ A ⊓ omegaCentralizer T ≤ normalizer (residual H : Set G) := by
  intro hN
  exact d.cubic_escape ((le_inf (d.cubic_le.trans inf_le_left)
    ((d.cubic_le.trans inf_le_right).trans hXC)).trans hN)

/-- The second application of the local sieve constructs the relative
C-component in the target centralizer. This discharges the relocation
step of 5.1.13, retaining its two substantial source arguments explicitly. -/
theorem sourceLocalCartanEscape_of_sieve_and_centralization
    {κ : GroupClass.{u}} (hsieve : LocalCartanSieve κ G)
    (hcentral : LocalCartanCentralization κ G) : SourceLocalCartanEscape κ G := by
  intro T L W n h H hH hgen A B c Y hY hescape
  obtain ⟨X, D, d⟩ := hsieve T L W n h H hH hgen A B c Y hY hescape
  obtain ⟨hXC, hmodule⟩ := hcentral T L W n h H hH hgen A B c Y hY X D d
  have hC := omegaCentralizer_mem_HOver_of_residual hH.1.1 (d.residual_le.trans hXC)
  obtain ⟨X', D', d'⟩ := hsieve T L W n h H hH hgen A B c
    (omegaCentralizer T) hC (d.escape_in_omegaCentralizer hXC)
  exact ⟨hmodule, d.residual_linear, X', d'.residual_le, d'.component_le,
    d'.component, d'.component_model⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.RawQuotient.ActionKernel
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.RawQuotient.Coverage
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.MixedLocal
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification

/-!
# Whole-quotient coverage in the selected A₆/S₆ case

The quotient map is exactly I → I/O_{3′}(I), and the selected subgroup is
the join of the images of the intrinsic component and central four-group.
Conjugation embeds this quotient into Aut(A₆). The source central four-group
is faithful and centralizes a Sylow two-subgroup, excluding the full
Aut(A₆) image by the proved identification of its actual Sylow model. The selected S₆
then exhausts the quotient by the index-two order calculation.

The mixed-configuration adapter constructs the intrinsic central four-group
and its Sylow containment from Ω₁(Z(T)) ≤ Ω₁(Z(J(T))) ≤ Baum(T) ≤ T_I.
It retains the source component, quotient map, and actual subgroup images.
The final coverage and whole-quotient results discharge `SylowModel` using
`Identification.sylowEquiv`. The conditional assembly APIs are retained.
Faithfulness is the applicable component conclusion of source 1.1.5(3).
The remaining fields of `QuotientCoordinates` belong to KernelCoordinates.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 15.4.18,
printed pp.1162–1163, and F.6.18, pp.309–310.
-/

@[expose] public section
open Subgroup
open AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.RawQuotient
variable {I : Type*} [Group I] [Finite I]

/-- The source star image, with the quotient by the three-prime core fixed. -/
abbrev starImage (U : Subgroup I) : Subgroup (I ⧸ pPrimeCore 3 I) :=
  U.map (QuotientGroup.mk' (pPrimeCore 3 I))

/-- The selected subgroup L*Z*, expressed as the join of its actual images. -/
abbrev selectedJoin (L Z : Subgroup I) : Subgroup (I ⧸ pPrimeCore 3 I) :=
  starImage L ⊔ starImage Z

/-- The missing coverage, conditional only on the independent actual Sylow
model. The selected S6 equivalence is used for its order, not as an equivalence
of the whole quotient. -/
theorem selectedJoin_eq_top_of_sylow_model (model : SylowModel)
    (hI : IsStronglyQuasithin I) (L Z : Subgroup I)
    (hL : Theory.GroupTheory.IsComponent I L) (eL : L ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 I) (hZS : Z ≤ (S : Subgroup I))
    (hSZ : (S : Subgroup I) ≤ centralizer (Z : Set I)) (hZ : Nat.card Z = 4)
    (hfaithful : Z ⊓ centralizer (L : Set I) = ⊥)
    (eSelected : selectedJoin L Z ≃* Equiv.Perm (Fin 6)) :
    selectedJoin L Z = ⊤ := by
  let : L.Normal := component_normal hI L hL eL
  let f := conjugationAction L eL
  have hk : f.ker = pPrimeCore 3 I :=
    (conjugationAction_ker L eL).trans (core_eq_centralizer hI L hL eL).symm
  have hZker : Disjoint Z f.ker := by
    rw [conjugationAction_ker L eL]
    exact disjoint_iff.mpr hfaithful
  exact coverage_of_proper_action f hk
    (not_surjective_of_central_four model S Z hZS hSZ hZ f hZker)
    (selectedJoin L Z) eSelected

/-- Extend the selected equivalence to the entire star quotient after proving
coverage, with no choices of a different quotient or kernel. -/
noncomputable def wholeQuotientEquivOfSylowModel (model : SylowModel)
    (hI : IsStronglyQuasithin I) (L Z : Subgroup I)
    (hL : Theory.GroupTheory.IsComponent I L) (eL : L ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 I) (hZS : Z ≤ (S : Subgroup I))
    (hSZ : (S : Subgroup I) ≤ centralizer (Z : Set I)) (hZ : Nat.card Z = 4)
    (hfaithful : Z ⊓ centralizer (L : Set I) = ⊥)
    (eSelected : selectedJoin L Z ≃* Equiv.Perm (Fin 6)) :
    (I ⧸ pPrimeCore 3 I) ≃* Equiv.Perm (Fin 6) :=
  Subgroup.topEquiv.symm.trans
    ((MulEquiv.subgroupCongr (selectedJoin_eq_top_of_sylow_model model hI L Z
      hL eL S hZS hSZ hZ hfaithful eSelected).symm).trans eSelected)

/-- The extension agrees with the supplied selected-subgroup equivalence. -/
theorem wholeQuotientEquivOfSylowModel_apply (model : SylowModel)
    (hI : IsStronglyQuasithin I) (L Z : Subgroup I)
    (hL : Theory.GroupTheory.IsComponent I L) (eL : L ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 I) (hZS : Z ≤ (S : Subgroup I))
    (hSZ : (S : Subgroup I) ≤ centralizer (Z : Set I)) (hZ : Nat.card Z = 4)
    (hfaithful : Z ⊓ centralizer (L : Set I) = ⊥)
    (eSelected : selectedJoin L Z ≃* Equiv.Perm (Fin 6)) (x : selectedJoin L Z) :
    wholeQuotientEquivOfSylowModel model hI L Z hL eL S hZS hSZ hZ hfaithful eSelected
      (x : I ⧸ pPrimeCore 3 I) = eSelected x := rfl

private theorem sylow_model : SylowModel :=
  fun P => ⟨Identification.sylowEquiv P⟩

/-- The selected S₆ subgroup exhausts the actual star quotient. The proved
Sylow identification discharges the model premise in the coverage argument. -/
theorem selectedJoin_eq_top
    (hI : IsStronglyQuasithin I) (L Z : Subgroup I)
    (hL : Theory.GroupTheory.IsComponent I L) (eL : L ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 I) (hZS : Z ≤ (S : Subgroup I))
    (hSZ : (S : Subgroup I) ≤ centralizer (Z : Set I)) (hZ : Nat.card Z = 4)
    (hfaithful : Z ⊓ centralizer (L : Set I) = ⊥)
    (eSelected : selectedJoin L Z ≃* Equiv.Perm (Fin 6)) :
    selectedJoin L Z = ⊤ :=
  selectedJoin_eq_top_of_sylow_model sylow_model hI L Z hL eL S hZS hSZ hZ
    hfaithful eSelected

/-- The whole star quotient is S₆, extending the supplied equivalence on L*Z*. -/
noncomputable def wholeQuotientEquiv
    (hI : IsStronglyQuasithin I) (L Z : Subgroup I)
    (hL : Theory.GroupTheory.IsComponent I L) (eL : L ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 I) (hZS : Z ≤ (S : Subgroup I))
    (hSZ : (S : Subgroup I) ≤ centralizer (Z : Set I)) (hZ : Nat.card Z = 4)
    (hfaithful : Z ⊓ centralizer (L : Set I) = ⊥)
    (eSelected : selectedJoin L Z ≃* Equiv.Perm (Fin 6)) :
    (I ⧸ pPrimeCore 3 I) ≃* Equiv.Perm (Fin 6) :=
  wholeQuotientEquivOfSylowModel (by exact sylow_model) hI L Z hL eL S hZS hSZ hZ
    hfaithful eSelected

/-- The whole-quotient equivalence preserves the selected subgroup's coordinates. -/
theorem wholeQuotientEquiv_apply
    (hI : IsStronglyQuasithin I) (L Z : Subgroup I)
    (hL : Theory.GroupTheory.IsComponent I L) (eL : L ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 I) (hZS : Z ≤ (S : Subgroup I))
    (hSZ : (S : Subgroup I) ≤ centralizer (Z : Set I)) (hZ : Nat.card Z = 4)
    (hfaithful : Z ⊓ centralizer (L : Set I) = ⊥)
    (eSelected : selectedJoin L Z ≃* Equiv.Perm (Fin 6)) (x : selectedJoin L Z) :
    wholeQuotientEquiv hI L Z hL eL S hZS hSZ hZ hfaithful eSelected
      (x : I ⧸ pPrimeCore 3 I) = eSelected x := rfl

section Mixed
variable {G : Type*} [Group G] [Finite G]

/-- The intrinsic source four-group in the constructed mixed local group. -/
noncomputable abbrev mixedZ (T : Sylow 2 G) (Y : Subgroup G) (F : Bool → Subgroup G) :
    Subgroup (MixedLocal.generated T Y F) :=
  (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)).subgroupOf (MixedLocal.generated T Y F)

/-- Assembly with the genuine realized mixed factors and constructed Goldschmidt
configuration. Faithfulness is precisely the applicable 1.1.5 component clause.
The independent Sylow-model input must still be discharged. -/
theorem whole_star_quotient_of_mixed_of_sylow_model (model : SylowModel)
    {K : GroupClass} (T : Sylow 2 G) {Y X M₁ M₂ : Subgroup G}
    {F : Bool → Subgroup G} (d : MixedLocal.RealizedFactors T Y X M₁ M₂ F)
    (c : MixedLocal.Configuration K T Y X M₂ F)
    (L : Subgroup (MixedLocal.generated T Y F))
    (hL : Theory.GroupTheory.IsComponent (MixedLocal.generated T Y F) L)
    (eL : L ≃* alternatingGroup (Fin 6))
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hfaithful : mixedZ T Y F ⊓ centralizer (L : Set (MixedLocal.generated T Y F)) = ⊥)
    (eSelected : selectedJoin L (mixedZ T Y F) ≃* Equiv.Perm (Fin 6)) :
    Nonempty (((MixedLocal.generated T Y F) ⧸
      pPrimeCore 3 (MixedLocal.generated T Y F)) ≃* Equiv.Perm (Fin 6)) := by
  let J := MixedLocal.generated T Y F
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  have hZU : Z ≤ MixedLocal.stabilizer T F :=
    ((centralOmega_le_thompsonAlpha _).trans (MixedLocal.alpha_le_baumann _)).trans
      (le_inf inf_le_left d.baumann_invariant)
  have hZJ : Z ≤ J := hZU.trans (le_sup_right.trans le_sup_left)
  obtain ⟨S, hS⟩ := c.generated_sylow
  have hZS : mixedZ T Y F ≤ (S : Subgroup J) := by
    intro z hz
    have hm : (z : G) ∈ (S : Subgroup J).map J.subtype := hS ▸ hZU hz
    obtain ⟨s, hs, he⟩ := hm
    exact (Subtype.ext he : s = z) ▸ hs
  have hSZ : (S : Subgroup J) ≤ centralizer (mixedZ T Y F : Set J) := by
    intro s hs z hz
    apply Subtype.ext
    have hsU : (s : G) ∈ MixedLocal.stabilizer T F :=
      hS ▸ Subgroup.mem_map_of_mem J.subtype hs
    exact (((Stellmacher.mem_omegaOneCenterAmbient_iff (T : Subgroup G) (z : G)).mp hz).2.2
      s hsU.1).symm
  have hZcard : Nat.card (mixedZ T Y F) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZJ).toEquiv).trans hZ
  exact ⟨wholeQuotientEquivOfSylowModel model c.sqtk.stronglyQuasithin L (mixedZ T Y F)
    hL eL S hZS hSZ hZcard hfaithful eSelected⟩

/-- Whole-quotient coverage in the genuine mixed setup, with the actual
Aut(A₆) Sylow model supplied by its proved identification. The faithfulness
input is source 1.1.5(3); the only model inputs are the selected A₆ component
and the given equivalence on its join with Z*. -/
theorem whole_star_quotient_of_mixed
    {K : GroupClass} (T : Sylow 2 G) {Y X M₁ M₂ : Subgroup G}
    {F : Bool → Subgroup G} (d : MixedLocal.RealizedFactors T Y X M₁ M₂ F)
    (c : MixedLocal.Configuration K T Y X M₂ F)
    (L : Subgroup (MixedLocal.generated T Y F))
    (hL : Theory.GroupTheory.IsComponent (MixedLocal.generated T Y F) L)
    (eL : L ≃* alternatingGroup (Fin 6))
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hfaithful : mixedZ T Y F ⊓ centralizer (L : Set (MixedLocal.generated T Y F)) = ⊥)
    (eSelected : selectedJoin L (mixedZ T Y F) ≃* Equiv.Perm (Fin 6)) :
    Nonempty (((MixedLocal.generated T Y F) ⧸
      pPrimeCore 3 (MixedLocal.generated T Y F)) ≃* Equiv.Perm (Fin 6)) :=
  whole_star_quotient_of_mixed_of_sylow_model sylow_model T d c L hL eL hZ
    hfaithful eSelected

end Mixed
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.RawQuotient

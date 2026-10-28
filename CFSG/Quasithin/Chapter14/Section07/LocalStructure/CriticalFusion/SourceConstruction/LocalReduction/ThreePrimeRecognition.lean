module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.ExchangedRecognition
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Action
public import Theory.Representation.BinaryOffender.PerfectMoved

/-!
# A commuting cubic excludes a faithful quadratic Suzuki orbit

Recognize the full moved central quotient using the proved normal or
exchanged Suzuki theorem. In the exchanged case, the actual index-two
normalizer supplies the pair geometry and faithfulness is required only
on the whole pair. Scalar centralization lifts through that same central
quotient, since the perfect orbit generates its own moved space. A
fixed-point-free cubic cannot fix this nonzero space.

Source: Aschbacher–Smith, 14.7.7, printed p.1045, with F.9.18 and the
Suzuki natural-module centralizer calculation, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter13.Section08.Components.Suzuki
open Chapter13.Section08.Components.Suzuki.NaturalSections
universe u
variable {D W : Type u} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

omit [Finite D] [Finite W] in
private theorem moved_not_bot_of_faithful (ρ : Representation (ZMod 2) D W)
    (hf : Function.Injective ρ) (K : Subgroup D) (hne : K ≠ ⊥) :
    subspaceCommutator ρ ⊤ K ≠ ⊥ := by
  intro he
  apply hne
  apply bot_unique
  intro k hk
  apply hf
  apply LinearMap.ext
  intro v
  have hv : ρ k v - v ∈ subspaceCommutator ρ ⊤ K :=
    Submodule.subset_span ⟨k,hk,v,Submodule.mem_top,rfl⟩
  rw [he,Submodule.mem_bot] at hv
  simpa only [map_one,Module.End.one_apply] using sub_eq_zero.mp hv

/-- A faithful quadratic Suzuki orbit cannot coexist with a commuting
fixed-point-free cubic. Recognition uses the entire moved central quotient
and, for an exchanged pair, faithfulness only on that whole pair. -/
theorem suzuki_orbit_impossible_of_fixedFree_cubic
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (K : Subgroup D) (hK : IsComponent D K) (S : Sylow 2 D)
    (hi : K.Normal ∨ (normalizer (K : Set D)).index = 2)
    {m : ℕ} (hm : 0 < m) (eK : K ≃* SuzukiMatrixGroup m)
    (Z A : Subgroup D) (hcZ : Nat.card Z = 3) (hfree : fixedSpace ρ Z = ⊥)
    (hcomm : componentOrbit K (S : Subgroup D) ≤ centralizer (Z : Set D))
    (hAS : A ≤ (S : Subgroup D)) (hA : IsElementaryTwo A)
    (hquad : IsQuadratic ρ A) (hcod : fixedCodim ρ A ≤ 2 * rank A)
    (hfaith : A ⊓ centralizer (componentOrbit K (S : Subgroup D) : Set D) = ⊥) : False := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hKne : K ≠ ⊥ := (nontrivial_iff_ne_bot K).mp inferInstance
  have finish (X : Subgroup D) (hXne : X ≠ ⊥)
      (hfix : subspaceCommutator ρ ⊤ X ≤ fixedSpace ρ Z) : False :=
    moved_not_bot_of_faithful ρ hf X hXne (bot_unique (hfree ▸ hfix))
  rcases hi with hn | hindex
  · let := hn
    have he : componentOrbit K (S : Subgroup D) = K :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer K _ K le_rfl
        le_normalizer_of_normal) (le_componentOrbit _ _)
    rw [he] at hcomm hfaith
    have hker : ¬ K ≤ ρ.ker := by
      rw [(MonoidHom.ker_eq_bot_iff ρ).mpr hf]
      exact fun hh => hKne (bot_unique hh)
    obtain ⟨e⟩ := SourceRecognition.natural_moved_of_quadratic_actor
      ρ K A hm eK hs hA hquad hcod hfaith hker
    have hc : Z ≤ centralizer (K : Set D) := le_centralizer_iff.mp hcomm
    apply finish K hKne
    exact central_extension_fixed_of_natural ρ K Z (subspaceCommutator ρ ⊤ K)
      (subspaceCommutator_invariant ρ ⊤ K)
      (subspaceCommutator_invariant_normalizer ρ
        (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
        (hc.trans (Subgroup.centralizer_le_normalizer _))) hc
      (subspaceCommutator_idempotent_of_perfect ρ K) m 0 1
      (by simpa using hcZ) e.groupEquiv.toMonoidHom e.groupEquiv.surjective
      e.linearEquiv e.intertwines
  · let X := componentOrbit K (S : Subgroup D)
    have hmove : ¬ (S : Subgroup D) ≤ normalizer (K : Set D) := by
      intro hh
      exact S.not_dvd_index (by simpa only [hindex] using index_dvd_of_le hh)
    have hz := SectionRecognition.center_eq_bot_of_equiv_suzuki eK
    have geo := Chapter13.Section08.Components.SourceModels.exchanged_geometry_of_index_two
      K (S : Subgroup D) hK hz hindex hmove
    have hSX : (S : Subgroup D) ≤ normalizer (X : Set D) := le_normalizer_componentOrbit _ _
    obtain ⟨e⟩ := ExchangedRecognition.exchanged_natural_pair ρ geo hindex hSX hf hK hs
      hm eK hAS hA hquad hfaith hcod
    have hXne : X ≠ ⊥ := fun he => hKne
      (bot_unique ((le_componentOrbit _ _).trans he.le))
    let : Group.IsPerfect X := hK.orbit_isPerfect (S : Subgroup D)
    have hc : Z ≤ centralizer (X : Set D) := le_centralizer_iff.mp hcomm
    apply finish X hXne
    exact central_extension_fixed_of_naturalPair ρ X Z (subspaceCommutator ρ ⊤ X)
      (subspaceCommutator_invariant ρ ⊤ X)
      (subspaceCommutator_invariant_normalizer ρ
        (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
        (hc.trans (Subgroup.centralizer_le_normalizer _))) hc
      (subspaceCommutator_idempotent_of_perfect ρ X) m 0 1
      (by simpa using hcZ) e.groupEquiv.toMonoidHom e.groupEquiv.surjective
      e.linearEquiv e.intertwines

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

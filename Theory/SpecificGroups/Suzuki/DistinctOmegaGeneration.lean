module
public import Theory.SpecificGroups.Suzuki.OmegaGeneration
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.SpecificGroups.Suzuki.SmallSylowIntersections

/-!
# Generation by distinct Suzuki Sylow omegas

For q > 2, a full Sylow omega and any element outside its normalizer
generate the Suzuki group. Align the Sylow with the concrete root and
apply root-omega generation. The TI property then places every nonidentity
element of a distinct Sylow omega outside that normalizer, so the two
full omegas generate.

The actual remote-center application in DGS (12.7) uses the two prescribed
centers on its path, rather than a freely chosen second conjugate.
Source: DGS85, Groups and Graphs, (12.7), printed p.184; the model input
is Huppert--Blackburn III, XI.3.12(e) and XI.11.15, as in OmegaGeneration.
The parameter zero is excluded: two involutions do not generate Sz(2).
-/

public noncomputable section
open Subgroup
namespace BenderSuzuki.MatrixGroups

/-- A full Sylow omega and any element outside its normalizer generate. -/
theorem suzukiSylow_omega_sup_zpowers_eq_top {n : ℕ} (hn : 0 < n)
    (P : Sylow 2 (SuzukiMatrixGroup n)) (t : SuzukiMatrixGroup n)
    (ht : t ∉ normalizer (P : Set (SuzukiMatrixGroup n))) :
    omegaOneAmbient (P : Subgroup (SuzukiMatrixGroup n)) ⊔ zpowers t = ⊤ := by
  obtain ⟨f,hP,hB⟩ := suzukiSylow_aligned_equiv hn (MulEquiv.refl _) P
  have ht' : f.symm t ∉ SuzukiBorelSubgroup n := by
    intro hh
    exact ht (hB ▸ mem_map.mpr ⟨f.symm t,hh,f.apply_symm_apply t⟩)
  have he := congrArg (Subgroup.map f.toMonoidHom)
    (suzukiRootSubgroup_omega_sup_zpowers_eq_top n hn (f.symm t) ht')
  rw [Subgroup.map_sup,map_omegaOneAmbient_injective _ f.injective,hP,
    MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom,f.apply_symm_apply,Subgroup.map_top_of_surjective _ f.surjective] at he
  exact he

/-- The full omegas of any two distinct Suzuki Sylows generate. -/
theorem suzukiSylow_distinct_omega_sup_eq_top {n : ℕ} (hn : 0 < n)
    (P R : Sylow 2 (SuzukiMatrixGroup n)) (hne : P ≠ R) :
    omegaOneAmbient (P : Subgroup (SuzukiMatrixGroup n)) ⊔
      omegaOneAmbient (R : Subgroup (SuzukiMatrixGroup n)) = ⊤ := by
  have hneR : omegaOneAmbient (R : Subgroup (SuzukiMatrixGroup n)) ≠ ⊥ := by
    intro he
    have hc := suzukiSylow_omega_card hn (MulEquiv.refl _) R
    rw [he,card_bot] at hc
    have hp : 1 < 2^(2*n+1) := Nat.one_lt_pow (by omega) (by decide)
    omega
  obtain ⟨t,ht,ht1⟩ := (omegaOneAmbient (R : Subgroup (SuzukiMatrixGroup n))).bot_or_exists_ne_one.resolve_left hneR
  have htR : t ∈ (R : Subgroup (SuzukiMatrixGroup n)) := omegaOneAmbient_le _ ht
  have htN : t ∉ normalizer (P : Set (SuzukiMatrixGroup n)) := by
    intro htN
    have htP : t ∈ (P : Subgroup (SuzukiMatrixGroup n)) := by
      have hh : t ∈ (R : Subgroup (SuzukiMatrixGroup n)) ⊓ normalizer (P : Set _) := ⟨htR,htN⟩
      rw [R.isPGroup'.inf_normalizer_sylow P] at hh
      exact hh.2
    exact hne (suzuki_sylow_eq_of_inf_ne_bot_all n P R (by
      intro he
      have hh : t ∈ (P : Subgroup (SuzukiMatrixGroup n)) ⊓ R := ⟨htP,htR⟩
      rw [he,mem_bot] at hh
      exact ht1 hh))
  apply top_unique
  rw [←suzukiSylow_omega_sup_zpowers_eq_top hn P t htN]
  exact sup_le le_sup_left ((zpowers_le.mpr ht).trans le_sup_right)
end BenderSuzuki.MatrixGroups

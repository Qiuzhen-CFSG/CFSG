module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Baumann.Basic
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.Basic
/-!
# The inner actors in the specified ambient two-subgroup

Restrict the literal normalizer action to `R`. Its kernel is the component
centralizer. The inverse image of its range under the faithful inner action
of `K` is a two-subgroup containing the specified Sylow, so Sylow maximality
identifies it with that Sylow. Thus every inner actor in `R` has a representative
in `R ∩ K`, and its remaining factor belongs to `R ∩ C_H(K)`.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927 (PDF p.944).
This is an unconditional action calculation for the supplied whole-group model.
-/

public section
open Subgroup Stellmacher
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel
variable {H F : Type*} [Group H] [Field F] [Finite F] [CharP F 2]
variable (K : Subgroup H) (e : K ≃* Sp F)

/-- Conjugation by the specified subgroup, transported through the actual model. -/
@[expose] noncomputable def restrictedModelAction (R : Subgroup H)
    (hR : R ≤ normalizer (K : Set H)) : R →* MulAut (Sp F) :=
  (modelAction K e).comp (inclusion hR)

omit [Finite F] [CharP F 2] in
/-- The restriction retains precisely the component-centralizer kernel. -/
theorem restrictedModelAction_eq_one_iff (R : Subgroup H)
    (hR : R ≤ normalizer (K : Set H)) (r : R) :
    restrictedModelAction K e R hR r = 1 ↔ (r : H) ∈ centralizer (K : Set H) := by
  change inclusion hR r ∈ (modelAction K e).ker ↔ _
  rw [modelAction_ker]
  rfl

omit [Finite F] [CharP F 2] in
private theorem modelAction_component (k : K) :
    modelAction K e (inclusion K.le_normalizer k) = MulAut.conj (e k) := by
  apply MulEquiv.ext
  intro g
  change e (k * e.symm g * k⁻¹) = e k * g * (e k)⁻¹
  simp only [map_mul, map_inv, e.apply_symm_apply]

/-- Inside `R`, the preimage of inner actors is the literal Sylow–centralizer product. -/
theorem restrictedModelAction_inner_preimage (R : Subgroup H)
    (hR : R ≤ normalizer (K : Set H)) (hp : IsPGroup 2 R)
    (S : Sylow 2 (Sp F))
    (hSyl : (localSylow K e S : Subgroup K).map K.subtype = R ⊓ K) :
    ((MulAut.innerSubgroup (Sp F)).comap (restrictedModelAction K e R hR)).map R.subtype =
      (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H)) := by
  let φ := restrictedModelAction K e R hR
  let i : K →* MulAut (Sp F) := MulAut.conj.comp e.toMonoidHom
  have hi : Function.Injective i := InvolutionNormalForms.inner_injective.comp e.injective
  have hφk (k : K) (hk : (k : H) ∈ R) : φ ⟨k, hk⟩ = i k := by
    exact modelAction_component K e k
  let Q : Subgroup K := φ.range.comap i
  have hQ : IsPGroup 2 Q :=
    (hp.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective).comap_of_injective i hi
  have hPQ : (localSylow K e S : Subgroup K) ≤ Q := by
    intro k hk
    have hkR : (k : H) ∈ R := (hSyl ▸ mem_map_of_mem K.subtype hk).1
    exact ⟨⟨k, hkR⟩, hφk k hkR⟩
  have hQP : Q = (localSylow K e S : Subgroup K) :=
    (localSylow K e S).is_maximal' hQ hPQ
  apply le_antisymm
  · rintro x ⟨r, hr, rfl⟩
    obtain ⟨g, hg⟩ := hr
    change MulAut.conj g = φ r at hg
    let k : K := e.symm g
    have hkQ : k ∈ Q := ⟨r, by simpa only [i, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, k, e.apply_symm_apply] using hg.symm⟩
    have hkP : k ∈ localSylow K e S := by
      change k ∈ (localSylow K e S : Subgroup K)
      rw [← hQP]
      exact hkQ
    have hkRK : (k : H) ∈ R ⊓ K := hSyl ▸ mem_map_of_mem K.subtype hkP
    let kr : R := ⟨k, hkRK.1⟩
    have hkr : φ kr = φ r := (hφk k hkRK.1).trans (by
      simpa only [i, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, k,
        e.apply_symm_apply] using hg)
    have hc : ((kr⁻¹ * r : R) : H) ∈ centralizer (K : Set H) := by
      apply (restrictedModelAction_eq_one_iff K e R hR _).mp
      change φ (kr⁻¹ * r) = 1
      rw [map_mul, map_inv, hkr, inv_mul_cancel]
    have hprod := (show (k : H) ∈ (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H)) from
      mem_sup_left hkRK)
    have hcprod : ((kr⁻¹ * r : R) : H) ∈ (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H)) :=
      mem_sup_right ⟨(kr⁻¹ * r).property, hc⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.subtype_apply, kr, mul_inv_cancel_left] using
      ((R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H))).mul_mem hprod hcprod
  · apply sup_le
    · intro k hk
      refine ⟨⟨k, hk.1⟩, ?_, rfl⟩
      change φ ⟨k, hk.1⟩ ∈ MulAut.innerSubgroup (Sp F)
      exact ⟨e ⟨k,hk.2⟩, (hφk ⟨k,hk.2⟩ hk.1).symm⟩
    · intro c hc
      refine ⟨⟨c, hc.1⟩, ?_, rfl⟩
      change restrictedModelAction K e R hR ⟨c,hc.1⟩ ∈ MulAut.innerSubgroup (Sp F)
      rw [(restrictedModelAction_eq_one_iff K e R hR _).mpr hc.2]
      exact one_mem _
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel

module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Transport
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Thompson
public import Stellmacher.OmegaOneCenterMap

/-!
# Specified Sylow and Borel facts for the Baumann argument

Transport the concrete symplectic Thompson theorem and elementary Sylow center
to the specified Sylow of the actual component. Its intersection with the
component centralizer is trivial because the whole matrix model has trivial
center. The ambient Borel is exactly the component-relative Sylow normalizer.

These are unconditional transport facts from a genuine whole-group equivalence;
they do not use simplicity of an unspecified central quotient.
Source: Aschbacher–Smith, proof of 13.6.6, printed p.927 (PDF p.944).
-/

public section
open Subgroup Stellmacher
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel
variable {H F : Type*} [Group H] [Field F] [Finite F] [CharP F 2]
variable (K : Subgroup H) (e : K ≃* Sp F)

theorem modelSylow_thompson {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : elementaryAbelianMaxJ (S : Subgroup (Sp F)) = S := by
  obtain ⟨g, hU, _⟩ := residualAt_conjugate hF hn S
  rw [← hU, elementaryAbelianMaxJ_map_injective _ (MulAut.conj g).injective,
    CentralRootGeometry.elementaryAbelianMaxJ_unipotent]

theorem localSylow_thompson {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) :
    elementaryAbelianMaxJ ((localSylow K e S : Subgroup K).map K.subtype) =
      (localSylow K e S : Subgroup K).map K.subtype := by
  change elementaryAbelianMaxJ (((S : Subgroup (Sp F)).map e.symm.toMonoidHom).map
    K.subtype) = _
  rw [elementaryAbelianMaxJ_map_injective _ K.subtype_injective,
    elementaryAbelianMaxJ_map_injective _ e.symm.injective, modelSylow_thompson hF hn]
  rfl

include e in
omit [Finite F] in
theorem component_inter_centralizer_disjoint (R : Subgroup H) :
    Disjoint (R ⊓ K) (R ⊓ centralizer (K : Set H)) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  have hz : (⟨x, hx.1.2⟩ : K) ∈ center K := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hx.2.2 y y.property)
  have hez : e ⟨x, hx.1.2⟩ ∈ center (Sp F) :=
    MulEquivClass.apply_mem_center e hz
  rw [EvenProjective.center_eq_bot] at hez
  have heq : (⟨x, hx.1.2⟩ : K) = 1 := e.injective (hez.trans (map_one e).symm)
  exact congrArg Subtype.val heq

omit [Finite F] [CharP F 2] in
theorem borelIn_le_component (S : Sylow 2 (Sp F)) : borelIn K e S ≤ K := by
  rintro x ⟨b, rfl⟩
  exact b.val.property

omit [CharP F 2] in
theorem borelIn_normalizes_localSylow (S : Sylow 2 (Sp F)) :
    borelIn K e S ≤ normalizer ((localSylow K e S : Subgroup K).map K.subtype : Set H) := by
  have hb : borelIn K e S = (localBorel K e S).map K.subtype := by
    rw [borelIn, borelMap, MonoidHom.range_comp, range_subtype]
  rw [hb, localBorel_eq_normalizer]
  exact le_normalizer_map K.subtype
omit [CharP F 2] in
theorem borelIn_eq_relative_normalizer (R : Subgroup H) (S : Sylow 2 (Sp F))
    (hSyl : (localSylow K e S : Subgroup K).map K.subtype = R ⊓ K) :
    borelIn K e S = K ⊓ normalizer ((R ⊓ K : Subgroup H) : Set H) := by
  have hb : borelIn K e S = (localBorel K e S).map K.subtype := by
    rw [borelIn, borelMap, MonoidHom.range_comp, range_subtype]
  rw [hb, localBorel_eq_normalizer, ← hSyl]
  have he := comap_normalizer_eq_of_le_range
    ((localSylow K e S : Subgroup K).map_le_range K.subtype)
  rw [comap_map_eq_self_of_injective K.subtype_injective] at he
  change (normalizer ((localSylow K e S : Subgroup K).map K.subtype : Set H)).comap
    K.subtype = normalizer (localSylow K e S : Set K) at he
  rw [← he, map_comap_eq, range_subtype, inf_comm]

theorem localSylow_omegaCenter {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) :
    let P := (localSylow K e S : Subgroup K).map K.subtype
    omegaOneCenterAmbient P = (center P).map P.subtype := by
  dsimp only
  let P := (localSylow K e S : Subgroup K).map K.subtype
  obtain ⟨g, hU, _⟩ := residualAt_conjugate hF hn S
  let f := (K.subtype.comp e.symm.toMonoidHom).comp (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f :=
    (K.subtype_injective.comp e.symm.injective).comp (MulAut.conj g).injective
  have hP : unipotent.map f = P := by
    rw [show f = (K.subtype.comp e.symm.toMonoidHom).comp
      (MulAut.conj g).toMonoidHom from rfl, ← map_map, hU, ← map_map]
    rfl
  let eu : unipotent (F := F) ≃* P :=
    ((unipotent (F := F)).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hP)
  let ec := centerCongr eu
  have hpow (z : center P) : z^2 = 1 := by
    apply ec.symm.injective
    rw [map_pow, map_one]
    let := CentralRootGeometry.center_elementary (F := F)
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (center (unipotent (F := F)))) (ec.symm z)
  change omegaOneCenterAmbient P = (center P).map P.subtype
  ext x
  constructor
  · intro hx
    obtain ⟨hxP, _, hc⟩ := (mem_omegaOneCenterAmbient_iff P x).mp hx
    refine ⟨⟨x,hxP⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    exact Subtype.ext (hc y y.property)
  · rintro ⟨z, hz, rfl⟩
    apply (mem_omegaOneCenterAmbient_iff P _).mpr
    refine ⟨z.property, ?_, ?_⟩
    · exact congrArg (fun y : center P => ((y : P) : H)) (hpow ⟨z,hz⟩)
    · intro y hy
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel

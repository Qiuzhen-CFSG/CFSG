module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import CFSG.Quasithin.Chapter11.Section01To02.NormalizerSteps
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers

/-!
# Recovering the chosen component from the plane orbit

The unique noncentral C-component of each plane normalizer is intrinsic to
that plane. Conjugation therefore carries its literal parabolic residual
to the residual attached to the image plane. Generation by these residuals
forces every permutation of the plane family to normalize L. Elements
centralizing V3/V1 fix every intermediate plane, while normalizers of L1
permute the Sylow fixed spaces. This proves both containments of 11.1.4
from the genuine preceding flag identities and 11.1.3.

The SL3 branch uses V3 = V and the proved uniqueness of the maximal
two-local overgroup of LT. No target normalizer containment is assumed.
The preceding geometric identities and component uniqueness remain explicit
premises for the flag/Cartan and component owners.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.3--4, printed p.765.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Subgroup
open CFSG.Quasithin.Chapter11
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G]

private theorem map_relative (e : G ≃* G) (H K : Subgroup G) :
    (K.subgroupOf H).map (e.subgroupMap H).toMonoidHom =
      (K.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom) := by
  apply map_injective (H.map e.toMonoidHom).subtype_injective
  rw [map_map, subgroupOf_map_subtype]
  have he : (H.map e.toMonoidHom).subtype.comp (e.subgroupMap H).toMonoidHom =
      e.toMonoidHom.comp H.subtype := rfl
  rw [he, ← map_map, subgroupOf_map_subtype, map_inf _ _ _ e.injective]

private theorem component_map (e : G ≃* G) {H K : Subgroup G}
    (h : Source.ComponentIn H K) :
    Source.ComponentIn (H.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  refine ⟨map_mono h.1, ?_⟩
  have hm := h.2.map_equiv (e.subgroupMap H)
  rwa [map_relative] at hm

private theorem noncentral_map (e : G ≃* G) {H U K : Subgroup G}
    (h : Source.NoncentralComponent H U K) :
    Source.NoncentralComponent (H.map e.toMonoidHom)
      (U.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  refine ⟨component_map e h.1, ?_⟩
  intro hc
  apply h.2
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [map_commutator]
  exact commutator_eq_bot_iff_le_centralizer.mpr hc

private theorem unique_map (e : G ≃* G) {H U K : Subgroup G}
    (h : Source.UniqueNoncentralComponent H U K) :
    Source.UniqueNoncentralComponent (H.map e.toMonoidHom)
      (U.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  refine ⟨noncentral_map e h.1, ?_⟩
  intro J hJ
  have hj := noncentral_map e.symm hJ
  simp only [map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G from by ext x; exact e.symm_apply_apply x, map_id] at hj
  have he := congrArg (map e.toMonoidHom) (h.2 _ hj)
  simpa only [map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G from by ext x; exact e.apply_symm_apply x, map_id] using he

private theorem residual_map [Finite G] (e : G ≃* G) (H : Subgroup G) :
    ((solvableResidual H).map H.subtype).map e.toMonoidHom =
      (solvableResidual (H.map e.toMonoidHom)).map (H.map e.toMonoidHom).subtype := by
  have he := congrArg (map (H.map e.toMonoidHom).subtype)
    (map_solvableResidual_eq (e.subgroupMap H).toMonoidHom (e.subgroupMap H).surjective)
  rw [map_map] at he ⊢
  have hc : (H.map e.toMonoidHom).subtype.comp (e.subgroupMap H).toMonoidHom =
      e.toMonoidHom.comp H.subtype := rfl
  rw [hc] at he
  exact he

private theorem localResidual_map [Finite G] (e : G ≃* G) (L U : Subgroup G) :
    (localResidual L U).map e.toMonoidHom =
      localResidual (L.map e.toMonoidHom) (U.map e.toMonoidHom) := by
  unfold localResidual
  rw [residual_map, map_inf _ _ _ e.injective, map_equiv_normalizer_eq]

/-- The actual plane orbit, with the common ambient conjugation convention. -/
def planeOrbit (V₂ L₁ : Subgroup G) : Set (Subgroup G) :=
  {U | ∃ l : L₁, U = V₂.map (MulAut.conj (l : G)).toMonoidHom}

/-- Source 11.1.3 transports to every plane in the L₁-orbit of V₂. -/
theorem orbit_unique [Finite G] {L V₂ L₁ : Subgroup G}
    (hL₁ : L₁ ≤ L)
    (h : Source.UniqueNoncentralComponent (normalizer (V₂ : Set G)) V₂
      (localResidual L V₂)) :
    ∀ U ∈ planeOrbit V₂ L₁,
      Source.UniqueNoncentralComponent (normalizer (U : Set G)) U (localResidual L U) := by
  rintro U ⟨l, rfl⟩
  have he := unique_map (MulAut.conj (l : G)) h
  have hn : L.map (MulAut.conj (l : G)).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer (hL₁ l.property))
  rw [map_equiv_normalizer_eq, localResidual_map, hn] at he
  exact he

/-- Recover L from the intrinsic noncentral components of a permuted plane family. -/
theorem normalizes_of_plane_permutation [Finite G]
    {L : Subgroup G} {Δ : Set (Subgroup G)}
    (hcomponents : ∀ U ∈ Δ,
      Source.UniqueNoncentralComponent (normalizer (U : Set G)) U (localResidual L U))
    (hgen : L = ⨆ U : Δ, localResidual L U.val)
    {g : G} (hg : ∀ U ∈ Δ, U.map (MulAut.conj g).toMonoidHom ∈ Δ) :
    g ∈ normalizer (L : Set G) := by
  let e := MulAut.conj g
  have hmap (U : Δ) : (localResidual L U.val).map e.toMonoidHom =
      localResidual L (U.val.map e.toMonoidHom) := by
    apply (hcomponents _ (hg U.val U.property)).2
    have hc := noncentral_map e (hcomponents U.val U.property).1
    rwa [map_equiv_normalizer_eq] at hc
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · conv_lhs => rw [hgen]
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro U
    change (localResidual L U.val).map e.toMonoidHom ≤ L
    rw [hmap]
    exact (le_iSup (fun W : Δ => localResidual L W.val)
      ⟨_, hg U.val U.property⟩).trans_eq hgen.symm
  · rw [card_map_of_injective e.injective]

/-- An automorphism trivial on A/W fixes every subgroup between W and A. -/
theorem sectionCentralizer_fixes [Finite G] {A W U : Subgroup G}
    (hWU : W ≤ U) (hUA : U ≤ A) {g : G}
    (hg : Source.CentralizesSection g A W) :
    U.map (MulAut.conj g).toMonoidHom = U := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    have h := U.mul_mem (hWU (hg.2.2 x (hUA hx))) hx
    change g * x * g⁻¹ ∈ U
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  · rw [card_map_of_injective (MulAut.conj g).injective]

private theorem centralizer_map (e : G ≃* G) (U : Subgroup G) :
    (centralizer (U : Set G)).map e.toMonoidHom =
      centralizer (U.map e.toMonoidHom : Set G) := by
  ext x
  rw [mem_map_equiv]
  constructor
  · intro hx y hy
    obtain ⟨z, hz, rfl⟩ := hy
    change e z * x = x * e z
    simpa only [map_mul, e.apply_symm_apply] using congrArg e (hx z hz)
  · intro hx y hy
    have h := hx (e y) (mem_map_of_mem e.toMonoidHom hy)
    simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm h

/-- Normalizing the actor and A permutes its Sylow fixed subgroups in A. -/
theorem normalizer_permutes_sylow_fixed [Finite G] {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G))
    (P : Sylow 2 B) :
    ∃ Q : Sylow 2 B,
      (A ⊓ centralizer ((P : Subgroup B).map B.subtype : Set G)).map
        (MulAut.conj g).toMonoidHom =
      A ⊓ centralizer ((Q : Subgroup B).map B.subtype : Set G) := by
  let e := MulAut.conj g
  let a := B.normalizerMonoidHom ⟨g, hB⟩
  refine ⟨P.mapSurjective (f := a.toMonoidHom)
    (show Function.Surjective a.toMonoidHom from a.surjective), ?_⟩
  have hn : A.map e.toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp hA
  rw [map_inf _ _ _ e.injective, centralizer_map,
    hn, Sylow.coe_mapSurjective, map_map, map_map]
  rfl

/-- Both source 11.1.4 containments from the genuine plane-orbit identities
and 11.1.3. The geometric premises are supplied by the flag/Cartan owner. -/
theorem normalizerControl_of_plane_geometry [Finite G]
    {L V₁ V₂ V₃ L₁ : Subgroup G}
    (hL₁ : L₁ ≤ L)
    (hunique : Source.UniqueNoncentralComponent (normalizer (V₂ : Set G)) V₂
      (localResidual L V₂))
    (hgen : L = ⨆ U : planeOrbit V₂ L₁, localResidual L U.val)
    (hinterval : ∀ U ∈ planeOrbit V₂ L₁, V₁ ≤ U ∧ U ≤ V₃)
    (hfixed : planeOrbit V₂ L₁ = Set.range (fun P : Sylow 2 L₁ =>
      V₃ ⊓ centralizer ((P : Subgroup L₁).map L₁.subtype : Set G))) :
    Source.NormalizerControl V₃ V₁ L₁ (normalizer (L : Set G)) := by
  have hc := orbit_unique hL₁ hunique
  constructor
  · intro g hg
    apply normalizes_of_plane_permutation hc hgen
    intro U hU
    rwa [sectionCentralizer_fixes (hinterval U hU).1 (hinterval U hU).2 hg]
  · rintro g ⟨h₃, h₁⟩
    apply normalizes_of_plane_permutation hc hgen
    intro U hU
    rw [hfixed] at hU ⊢
    obtain ⟨P, rfl⟩ := hU
    obtain ⟨Q, hQ⟩ := normalizer_permutes_sylow_fixed h₃ h₁ P
    exact ⟨Q, hQ.symm⟩

open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource

/-- Application to the literal chosen flag, retaining the original residual
and quotient-preimage definitions. -/
theorem chosen_normalizerControl [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField} {c : Coordinates D F}
    (f : InvariantFlag c)
    (hunique : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))
    (hgen : L = ⨆ U : planeOrbit (f.Vi 1) (f.Li 0), localResidual L U.val)
    (hinterval : ∀ U ∈ planeOrbit (f.Vi 1) (f.Li 0), f.Vi 0 ≤ U ∧ U ≤ f.Vi 2)
    (hfixed : planeOrbit (f.Vi 1) (f.Li 0) = Set.range (fun P : Sylow 2 (f.Li 0) =>
      f.Vi 2 ⊓ centralizer ((P : Subgroup (f.Li 0)).map (f.Li 0).subtype : Set G))) :
    Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0) (normalizer (L : Set G)) :=
  normalizerControl_of_plane_geometry ((localResidual_le _).trans inf_le_left)
    hunique hgen hinterval hfixed

/-- Uniqueness of the original maximal local overgroup controls the full
normalizer of the chosen seed, with no additional source premise. -/
theorem chosen_seed_normalizer_le [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) :=
  D.normal_subgroup_normalizer_le S.source.toHypothesis1221
    (D.le_component.trans le_sup_left) D.ne_bot (sup_le D.normalizes S.sylow_normalizes)

/-- The linear-three case of 11.1.4 uses the full-space flag identity. -/
theorem chosen_normalizerControl_of_top [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) (h₃ : f.Vi 2 = V) :
    Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0) (normalizer (L : Set G)) := by
  have hn : normalizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G) :=
    by rw [h₃]; exact chosen_seed_normalizer_le D S
  exact ⟨fun _ hg => hn hg.1, inf_le_left.trans hn⟩

/-- Source 11.1.4 on the actual flag: the linear full-space branch or the
nonlinear plane geometry supplied by the preceding model analysis. -/
theorem chosen_source_11_1_4 [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hunique : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))
    (hgeometry : f.Vi 2 = V ∨
      (L = ⨆ U : planeOrbit (f.Vi 1) (f.Li 0), localResidual L U.val) ∧
      (∀ U ∈ planeOrbit (f.Vi 1) (f.Li 0), f.Vi 0 ≤ U ∧ U ≤ f.Vi 2) ∧
      planeOrbit (f.Vi 1) (f.Li 0) = Set.range (fun P : Sylow 2 (f.Li 0) =>
        f.Vi 2 ⊓ centralizer ((P : Subgroup (f.Li 0)).map (f.Li 0).subtype : Set G))) :
    Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0) (normalizer (L : Set G)) := by
  rcases hgeometry with h₃ | ⟨hgen, hinterval, hfixed⟩
  · exact chosen_normalizerControl_of_top D S f h₃
  · exact chosen_normalizerControl f hunique hgen hinterval hfixed

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers

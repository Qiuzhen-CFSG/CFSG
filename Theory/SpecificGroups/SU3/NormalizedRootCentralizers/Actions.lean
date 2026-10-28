module
public import Theory.SpecificGroups.SU3.NormalizedRootCentralizers.Extensions
public import Theory.SpecificGroups.SU3.NormalizedRootCentralizers.ResidualAction
/-!
# Uniform unitary root centralizers through faithful component actions

The entire Sylow center transports through the actual inner embedding.
For a residual D = [D,T], the abelian quotient by inner-diagonal actors
kills the field part. Its normalization of the root Sylow then places D
in the triangular unitary actor group, where the matrix calculation gives
uniform centralizers. The normalizing actor T may lie outside the extension
containing D. The literal mixed outer preimage is included without any
splitting or independent recognition assumption.

Source: Aschbacher–Smith, A.3.16–18 and proof of 13.6.6, printed p.927.
-/

public section
open Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.NormalizedRootCentralizers
open BorelTorus BorelTorus.EvenCenterAction ExtensionBorel
variable {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    {H : Type*} [Group H]
include hn hcard hfixed

/-- Full-center transport for a faithful action compatible with the component's inner map. -/
theorem action_center (f : H →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hf : Function.Injective f) (U : Subgroup H)
    (hU : U.map f = (projectiveRoot J hJ).map MulAut.conj) :
    ((center U).map U.subtype).map f = (centralImage J hJ).map MulAut.conj := by
  rw [map_embeddedCenter U f hf, hU,
    ← map_embeddedCenter _ _ (binary_inner_injective J hJ hn hcard
      (huppert_II_10_4_conj_eq_frobenius J (2^n) hcard hfixed)),
    root_center J hn hcard hfixed hJ]

/-- Pull the actual inner-diagonal calculation back through a faithful action. -/
theorem uniform_of_action (f : H →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hf : Function.Injective f) (U B : Subgroup H)
    (hU : U.map f = (projectiveRoot J hJ).map MulAut.conj)
    (hB : B.map f ≤ actorBorel J hJ) (hD : B.map f ≤ J.unitaryConjHom.range)
    (r : H) (hr : r ∈ (center U).map U.subtype) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set H) =
      B ⊓ centralizer (((center U).map U.subtype : Subgroup H) : Set H) := by
  have hcenter := action_center J hJ hn hcard hfixed f hf U hU
  have hr' : f r ∈ (centralImage J hJ).map MulAut.conj := by
    rw [← hcenter]
    exact mem_map_of_mem f hr
  have he := actor_uniform J hJ hn hcard hfixed (B.map f) hB hD
    (f r) hr' (fun he => hne (hf (he.trans f.map_one.symm)))
  apply le_antisymm
  · rintro b ⟨hb, hc⟩
    have hc' : f b ∈ (B.map f) ⊓ centralizer ({f r} : Set _) := by
      refine ⟨mem_map_of_mem f hb, mem_centralizer_singleton_iff.mpr ?_⟩
      simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hc)
    rw [he] at hc'
    refine ⟨hb, mem_centralizer_iff.mpr ?_⟩
    intro x hx
    apply hf
    have hx' : f x ∈ (centralImage J hJ).map MulAut.conj :=
      hcenter ▸ mem_map_of_mem f hx
    simpa only [map_mul] using mem_centralizer_iff.mp hc'.2 (f x) hx'
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hr))

/-- The source residual identity discharges the inner-diagonal premise.
The actor normalizing D may lie outside the extension containing D. -/
theorem commutator_generated_uniform
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (f : H →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hf : Function.Injective f) (U D T : Subgroup H)
    (hU : U.map f = (projectiveRoot J hJ).map MulAut.conj)
    (hB : D.map f ≤ actorBorel J hJ) (hD : ⁅D,T⁆ = D)
    (r : H) (hr : r ∈ (center U).map U.subtype) (hne : r ≠ 1) :
    D ⊓ centralizer ({r} : Set H) =
      D ⊓ centralizer (((center U).map U.subtype : Subgroup H) : Set H) :=
  uniform_of_action J hJ hn hcard hfixed f hf U D hU hB
    (commutator_generated_unitary J hJ hn hcard
      (huppert_II_10_4_conj_eq_frobenius J (2^n) hcard hfixed) f D T hD) r hr hne

/-- Normalization of the actual Sylow, together with D = [D,T], is sufficient
in every extension acting faithfully on the unitary component. -/
theorem commutator_generated_normalizer_uniform
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (f : H →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hf : Function.Injective f) (U D T : Subgroup H)
    (hU : U.map f = (projectiveRoot J hJ).map MulAut.conj)
    (hN : D ≤ normalizer (U : Set H)) (hD : ⁅D,T⁆ = D)
    (r : H) (hr : r ∈ (center U).map U.subtype) (hne : r ≠ 1) :
    D ⊓ centralizer ({r} : Set H) =
      D ⊓ centralizer (((center U).map U.subtype : Subgroup H) : Set H) := by
  have hconj := huppert_II_10_4_conj_eq_frobenius J (2^n) hcard hfixed
  have hunitary := commutator_generated_unitary J hJ hn hcard hconj f D T hD
  have hi := binary_inner_injective J hJ hn hcard hconj
  apply commutator_generated_uniform J hJ hn hcard hfixed f hf U D T hU _ hD r hr hne
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨u, hu⟩ := hunitary (mem_map_of_mem f hd)
  apply (root_stabilizer_iff J hJ hcard hfixed (f d) (by
    rw [← hu, J.unitaryConjHom_apply]
    exact unitary_mem_semilinear J hJ u)).mp
  have hnorm := U.le_normalizer_map f (mem_map_of_mem f (hN hd))
  rw [hU, mem_normalizer_iff_map_conj_eq] at hnorm
  have he : (MulAut.conj (f d) : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) →*
      MulAut (ProjectiveSpecialUnitaryMatrixGroup J)).comp MulAut.conj =
        MulAut.conj.comp (f d).toMonoidHom := by
    ext x y
    simp
  rw [map_map, he, ← map_map] at hnorm
  exact map_injective hi hnorm

/-- The literal mixed outer preimage, with an ambient normalizing actor.
For the source nonsplit case use odd n divisible by three, a field actor
of order three and the diagonal outer class of order three. This result
works without choosing lifts that split the extension. -/
theorem mixedPreimage_uniform
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (σ : E ≃+* E) (d : J.unitarySubgroup)
    (D : Subgroup (mixedPreimage J hJ σ d))
    (T : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hD : ⁅D.map (mixedPreimage J hJ σ d).subtype, T⁆ =
      D.map (mixedPreimage J hJ σ d).subtype)
    (hB : D ≤ normalizer
      (Theory.GroupTheory.AutomorphismExtensionBorel.rootIn (projectiveRoot J hJ)
        (mixedPreimage J hJ σ d) : Set (mixedPreimage J hJ σ d)))
    (r : mixedPreimage J hJ σ d)
    (hr : r ∈ (center (Theory.GroupTheory.AutomorphismExtensionBorel.rootIn
      (projectiveRoot J hJ) (mixedPreimage J hJ σ d))).map
        (Theory.GroupTheory.AutomorphismExtensionBorel.rootIn
          (projectiveRoot J hJ) (mixedPreimage J hJ σ d)).subtype)
    (hne : r ≠ 1) :
    D ⊓ centralizer ({r} : Set (mixedPreimage J hJ σ d)) =
      D ⊓ centralizer (((center (Theory.GroupTheory.AutomorphismExtensionBorel.rootIn
        (projectiveRoot J hJ) (mixedPreimage J hJ σ d))).map
          (Theory.GroupTheory.AutomorphismExtensionBorel.rootIn
            (projectiveRoot J hJ) (mixedPreimage J hJ σ d)).subtype :
              Subgroup (mixedPreimage J hJ σ d)) : Set (mixedPreimage J hJ σ d)) := by
  let H := mixedPreimage J hJ σ d
  let U := Theory.GroupTheory.AutomorphismExtensionBorel.rootIn (projectiveRoot J hJ) H
  have hconj := huppert_II_10_4_conj_eq_frobenius J (2^n) hcard hfixed
  have hU : U.map H.subtype = (projectiveRoot J hJ).map MulAut.conj := by
    dsimp only [U, H]
    rw [Theory.GroupTheory.AutomorphismExtensionBorel.rootIn_eq_map _ _
      (inner_le_mixedPreimage J hJ σ d), map_map]
    rfl
  have hBa : D.map H.subtype ≤ actorBorel J hJ := by
    rintro _ ⟨x, hx, rfl⟩
    have hh := hB hx
    rw [normalizer_mixedPreimage J hJ hn hcard hconj] at hh
    exact hh
  have hunitary := commutator_generated_unitary J hJ hn hcard hconj
    (MonoidHom.id (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (D.map H.subtype) T hD
  rw [map_id] at hunitary
  exact uniform_of_action J hJ hn hcard hfixed H.subtype H.subtype_injective U D
    hU hBa hunitary r hr hne

end BenderSuzuki.MatrixGroups.HermitianForm.NormalizedRootCentralizers

module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Transfers
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport.Foundations

/-!
# Symmetry of the exterior conjugate pair

Suppose the exterior calculation gives [V,Vᵍ]=V₆ and reverse normalization
for each noncentralizing conjugate Vᵍ inside T. Conjugate the reverse pair
by g⁻¹, then move it into T by an element n of N_G(V). Applying the same
calculation again shows that n*g⁻¹ normalizes V₆. The local G₆ containment
and the original TI property then make it normalize V, a contradiction.

This argument uses Sylow conjugacy inside the literal normalizer of V.
It does not require a conjugation transport of the chosen-module record,
or infer normalization of V merely from membership in M. Zero.Geometry
constructs the commutator and reverse-normalization premises.
Source: Aschbacher--Smith, the symmetry step in 12.5.7, printed p.820.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

/-- Symmetry and the genuine TI step eliminate every noncentralizing zeroth generator. -/
theorem zero_centralizes_of_symmetric_commutators (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₆ : s.marking.Gi 6 ≤ s.marking.M)
    (hgeometry : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = s.marking.Vi 6 ∧
      V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G) := by
  let := D.elementary
  have hTN : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    le_sup_right.trans s.normalizes
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  intro A hA
  obtain ⟨g, rfl, hgT⟩ := (mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
  by_contra hnon
  have hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro he
    exact hnon (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  obtain ⟨hforward, hreverse⟩ := hgeometry g hgT hcomm
  have hBN : V.map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (V : Set G) := by
    have hb := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hreverse
    rwa [map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,
      offender_map_conj_inverse] at hb
  obtain ⟨n, hn, hnT⟩ := offender_exists_normalizer_conjugate_le_sylow V T hTN
    ((IsElementaryAbelian.isPGroup 2 V).map (MulAut.conj g⁻¹).toMonoidHom) hBN
  rw [offender_map_conj_map] at hnT
  have hnV : V.map (MulAut.conj n).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hn
  have hmove : ⁅V, V.map (MulAut.conj (n * g⁻¹)).toMonoidHom⁆ =
      (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map
        (MulAut.conj (n * g⁻¹)).toMonoidHom := by
    rw [map_commutator, offender_map_conj_map]
    simp only [inv_mul_cancel_right, hnV]
    exact commutator_comm _ _
  have hback := hgeometry (n * g⁻¹) hnT (by
    rw [hmove]
    exact fun he => hcomm ((map_eq_bot_iff_of_injective _
      (MulAut.conj (n * g⁻¹)).injective).mp he))
  have hfix : n * g⁻¹ ∈ s.marking.Gi 6 := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (s.marking.Vi 6).map (MulAut.conj (n * g⁻¹)).toMonoidHom = s.marking.Vi 6
    calc
      _ = (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map
          (MulAut.conj (n * g⁻¹)).toMonoidHom := congrArg _ hforward.symm
      _ = ⁅V, V.map (MulAut.conj (n * g⁻¹)).toMonoidHom⁆ := hmove.symm
      _ = s.marking.Vi 6 := hback.1
  have hng : n * g⁻¹ ∈ normalizer (V : Set G) :=
    normalizes_of_G₆_le s h structural hG₆ hfix
  have hg : g ∈ normalizer (V : Set G) := by
    have hi := (normalizer (V : Set G)).mul_mem
      ((normalizer (V : Set G)).inv_mem hn) hng
    have hgi : g⁻¹ ∈ normalizer (V : Set G) := by simpa [mul_assoc] using hi
    simpa only [inv_inv] using (normalizer (V : Set G)).inv_mem hgi
  apply hnon
  have he : V.map (MulAut.conj g).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hg
  exact he.le.trans (Subgroup.le_centralizer V)

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

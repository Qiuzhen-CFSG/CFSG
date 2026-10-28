module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSeed

/-!
# The actual symplectic central layer contains the marked natural module

The source coordinates identify its module centralizer with the two-core.
The marked radical-fixed vector and its A6 orbit place the entire module in
Z at the original vertex. This excludes critical distance zero and makes Z
elementary. Its faithful natural submodule identifies the centralizer at every
vertex, supplying exactly the extra hypothesis used in MS93 (2.2).

Source: MS93 (2.1)--(2.2), printed pp.855--857. The later identification of
the whole moving layer and reconstruction of the commutator core are separate.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
universe u
variable {M : Type u} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal]
variable (s : Source L R W)

omit [Finite M] in
/-- The marked natural module has precisely the ambient two-core as centralizer. -/
theorem module_centralizer (s : Source L R W) :
    centralizer (W : Set M) = pCore 2 M := by
  exact (CFSG.Quasithin.ChapterC.RankOne.SymmetricSix.natural_six_kernel_eq_centralizer
    W s.projection s.coordinates s.action).symm.trans s.projection_kernel

omit [Finite M] in
/-- The original coordinate map makes the marked module elementary. -/
theorem module_elementary (s : Source L R W) : IsElementaryAbelian 2 W := by
  let : IsElementaryAbelian 2 (Multiplicative (BinaryPermutation.natural (Fin 6))) := {
    is_comm := ⟨mul_comm⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun v => by
      rw [pow_two]
      change v.toAdd + v.toAdd = 0
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]) }
  exact IsElementaryAbelian.of_injective s.coordinates.toMonoidHom s.coordinates.injective

/-- The graph Z-layer contains the actual marked natural module. -/
theorem module_le_Z (s : Source L R W) :
    W.map (embedM R) ≤ Z R (alpha R) := by
  apply SymplecticSeed.module_le_Z s.projection s.component_image
    s.coordinates s.action s.module_elementary (s.module_le_core.trans s.core_le) s.w s.w_ne s.radical_fixes

/-- The native source has positive critical distance. -/
theorem criticalDistance_pos (s : Source L R W) :
    0 < criticalDistance R (alpha R) (s.geometry.exists_critical (alpha R) rfl) := by
  apply SymplecticSeed.criticalDistance_pos s.two_group s.core_le
    (s.module_le_core.trans s.core_le) (s.module_centralizer)
    (s.geometry.exists_critical (alpha R) rfl)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

/-- The native X-layer contains the actual module and is elementary. -/
theorem Z_le_X : Z R (alpha R) ≤ X R (alpha R) :=
  s.geometry.omega_bound (alpha R) rfl s.criticalDistance_pos

theorem Z_elementary : IsElementaryAbelian 2 (Z R (alpha R)) := by
  let : IsElementaryAbelian 2 (X R (alpha R)) := omegaCenter_elementary (Q R (alpha R))
  exact IsElementaryAbelian.of_le s.Z_le_X

/-- Faithfulness of the contained natural module identifies the entire base
Z-layer centralizer. -/
theorem C_alpha : C R (alpha R) = Q R (alpha R) := by
  apply le_antisymm
  · rintro x ⟨hx, hc⟩
    have hxM : x ∈ Mbar R := (stabilizer_m_base R) ▸ hx
    obtain ⟨m,rfl⟩ := hxM
    have hm : m ∈ centralizer (W : Set M) := by
      intro w hw
      apply embedM_injective R
      simpa only [map_mul] using hc (embedM R w)
        (s.module_le_Z (mem_map_of_mem _ hw))
    rw [s.module_centralizer] at hm
    rw [Q_alpha R s.two_group s.core_le]
    exact mem_map_of_mem _ hm
  · intro x hx
    exact ⟨hx.1, le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)) hx⟩

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

omit s [Finite M] in
private theorem C_covariance (g : FreeAmalgam R) (a : Vertex R) :
    C R (act R g a) = (C R a).map (MulAut.conj g⁻¹).toMonoidHom := by
  let e := MulAut.conj g⁻¹
  rw [C, stabilizer_act, Z_act]
  apply le_antisymm
  · rintro x ⟨⟨y, hy, rfl⟩, hc⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    intro z hz
    apply e.injective
    have hh : e z * e y = e y * e z := hc (e z) (mem_map_of_mem e.toMonoidHom hz)
    simpa only [map_mul] using hh
  · rintro x ⟨y, ⟨hy, hc⟩, rfl⟩
    refine ⟨mem_map_of_mem e.toMonoidHom hy, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change e z * e y = e y * e z
    simpa only [map_mul] using congrArg e (hc z hz)

/-- The same exact centralizer at every original-group vertex. -/
theorem C_eq_Q (a : Vertex R) (ha : color R a = false) : C R a = Q R a := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hh := C_covariance (R := R) g (alpha R)
  have hq := Q_act R g (alpha R)
  simp only [alpha, act_mVertex, one_mul] at hh hq
  have hbase := s.C_alpha
  change C R (mVertex R 1) = Q R (mVertex R 1) at hbase
  rw [hh, hbase, hq]

/-- The marked natural module supplies the genuine edge-centralizer hypothesis. -/
theorem edgeCentralizerCondition : EdgeCentralizerCondition R := by
  intro a t ha hat
  have ht : color R t = true := by
    have hh := adjacent_color_ne R hat
    cases hcol : color R t <;> simp_all
  apply le_antisymm
  · rintro x ⟨hx, hc⟩
    rw [← s.C_eq_Q a ha]
    exact ⟨hx.2 a (adjacent_symm R hat), hc⟩
  · intro x hx
    refine ⟨Q_le_adjacent_h R ht hat hx, ?_⟩
    exact le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha)) hx

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

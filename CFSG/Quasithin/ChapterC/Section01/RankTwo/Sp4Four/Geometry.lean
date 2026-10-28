module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.ThompsonOffender
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSeed
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Actual MS holomorph geometry before nonbinary recognition

The central orbit identifies the graph Z-layer at its original vertex.
Its faithful centralizer excludes critical distance zero; the generic
amalgam theorem gives an even positive distance. The graph commutator core
is the literal intrinsic core of the original component, via its actual
embedding. These facts need no supplied natural module or distance bound.

Source: MS93 (2.0)--(2.2), pp.854--857; the initial reduction of (3.2).
-/
public section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.MSCentralOrbit
variable {H : Type*} [Group H] [Finite H]

/-- The original omega orbit is exactly the graph Z-layer. -/
theorem Z_alpha_eq_omegaOrbit (R : Subgroup H) :
    Z R (alpha R) = (omegaOrbit R).map (embedM R) :=
  NaturalSixControl.SymplecticSeed.Z_eq_seedHull R

/-- The source characteristic condition yields actual positive even critical
geometry, with no nonbinary natural-module assumption. -/
theorem exists_positive_even_geometry (R : Subgroup H)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hms : MSCharacteristicCondition R)
    (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H) :
    ∃ g : Geometry R, 0 < g.b R ∧ Even (g.b R) := by
  let g := geometry R hp hne hms
  refine ⟨g, ?_, g.even (alpha R) rfl⟩
  apply NaturalSixControl.SymplecticSeed.criticalDistance_pos hp hQR ?_ hfaith
  exact (omegaOrbit_le_centralOmega R hQR hself).trans
    (fun _ hx => hQR ((mem_omegaCenterIn_iff _ _).mp hx).1)

/-- The graph centralizer is the first-neighborhood kernel at the base vertex. -/
theorem C_alpha_eq_Q (R : Subgroup H) (hp : IsPGroup 2 R)
    (hQR : pCore 2 H ≤ R)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H) :
    C R (alpha R) = Q R (alpha R) := by
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    have hxM : x ∈ Mbar R := (stabilizer_m_base R) ▸ hx
    obtain ⟨m,rfl⟩ := hxM
    have hm : m ∈ centralizer (omegaOrbit R : Set H) := by
      intro w hw
      apply embedM_injective R
      have hz : embedM R w ∈ Z R (alpha R) := by
        rw [Z_alpha_eq_omegaOrbit]
        exact mem_map_of_mem _ hw
      simpa only [map_mul] using hc (embedM R w) hz
    rw [hfaith] at hm
    rw [Q_alpha R hp hQR]
    exact mem_map_of_mem _ hm
  · intro x hx
    exact ⟨hx.1, le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)) hx⟩

omit [Finite H] in
private theorem C_covariance (R : Subgroup H) (g : FreeAmalgam R) (a : Vertex R) :
    C R (act R g a) = (C R a).map (MulAut.conj g⁻¹).toMonoidHom := by
  let e := MulAut.conj g⁻¹
  rw [C,stabilizer_act,Z_act]
  apply le_antisymm
  · rintro x ⟨⟨y,hy,rfl⟩,hc⟩
    refine ⟨y,⟨hy,?_⟩,rfl⟩
    intro z hz
    apply e.injective
    have hh : e z * e y = e y * e z := hc (e z) (mem_map_of_mem e.toMonoidHom hz)
    simpa only [map_mul] using hh
  · rintro x ⟨y,⟨hy,hc⟩,rfl⟩
    refine ⟨mem_map_of_mem e.toMonoidHom hy,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    change e z * e y = e y * e z
    simpa only [map_mul] using congrArg e (hc z hz)

/-- Centralizer control transports to every vertex of original-group color. -/
theorem C_eq_Q (R : Subgroup H) (hp : IsPGroup 2 R)
    (hQR : pCore 2 H ≤ R)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (a : Vertex R) (ha : color R a = false) : C R a = Q R a := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  have hh := C_covariance R g (alpha R)
  have hq := Q_act R g (alpha R)
  simp only [alpha,act_mVertex,one_mul] at hh hq
  have hbase := C_alpha_eq_Q R hp hQR hfaith
  change C R (mVertex R 1) = Q R (mVertex R 1) at hbase
  rw [hh,hbase,hq]

/-- The actual initial central orbit discharges the extra centralizer premise
of source (2.2), including critical reversal and both endpoint offenders. -/
theorem edgeCentralizerCondition (R : Subgroup H) (hp : IsPGroup 2 R)
    (hQR : pCore 2 H ≤ R)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H) :
    EdgeCentralizerCondition R := by
  intro a t ha hat
  have ht : color R t = true := by
    have hh := adjacent_color_ne R hat
    cases hcol : color R t <;> simp_all
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    rw [← C_eq_Q R hp hQR hfaith a ha]
    exact ⟨hx.2 a (adjacent_symm R hat),hc⟩
  · intro x hx
    refine ⟨Q_le_adjacent_h R ht hat hx,?_⟩
    exact le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha)) hx

/-- The ambient core commutator is the actual intrinsic core of a normal
p-perfect component; the quotient or module type is not used. -/
theorem commutatorCore_eq_intrinsic (K : Subgroup H) [K.Normal]
    (hperfect : IsPPerfect 2 K) :
    ⁅pCore 2 H,K⁆ = (⁅pCore 2 K,(⊤ : Subgroup K)⁆).map K.subtype := by
  apply le_antisymm
  · exact commutator_le_core_commutator_of_isSubnormal K (pCore 2 H)
      (inferInstance : K.Normal).isSubnormal hperfect pCore_isPGroup
      (by rw [normalizer_eq_top]; exact le_top)
  · rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    apply commutator_mono _ le_rfl
    rw [pCore_subnormal_eq_comap 2 (inferInstance : K.Normal).isSubnormal,
      map_comap_eq, range_subtype]
    exact inf_le_right

/-- The literal graph core is the embedded original intrinsic commutator core. -/
theorem graphCore_eq_intrinsic (K R : Subgroup H) [K.Normal]
    (hp : IsPGroup 2 R) (hQR : pCore 2 H ≤ R) (hres : pResidual 2 H = K) :
    core R (alpha R) =
      ((⁅pCore 2 K,(⊤ : Subgroup K)⁆).map K.subtype).map (embedM R) := by
  rw [core_alpha R hp hQR hres]
  congr 1
  apply commutatorCore_eq_intrinsic
  rw [← hres]
  exact isPPerfect_pResidual 2

end CFSG.Quasithin.ChapterC.MSCentralOrbit

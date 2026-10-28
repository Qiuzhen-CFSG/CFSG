module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleAlternatingEightGeometryOrbits
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleAlternating
public import Theory.GroupTheory.LocalSylowCentralizerRepresentative

/-!
# Constructing the original alternating-eight fusion seed

Failure of global TI gives an outside fusion pair in the actual V. The
orbit-size comparison forces weights two and six; conjugation in L makes
the target the complement vz. Local Sylow-centralizer selection then moves
both points together. An M-conjugate cannot change the selected weight to
six, since that would already realize the forbidden fusion inside M.
NoEscape identifies the selected local centralizer with its full ambient
centralizer, giving the literal required Sylow image C_T(v).

The final application supplies precisely the eight-letter input of
`alternating_of_core_geometry`. The independent six-letter branch and the
later omega-center argument are outside this geometric construction.

Source: Aschbacher--Smith, 12.2.16, printed pp.799--800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open BinaryPermutation ChapterI.Section06To08 Representation ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace AlternatingEightCoreCoordinates
variable (C : AlternatingEightCoreCoordinates L V)

omit [Finite G] in
/-- Adjust the target within its L-orbit, retaining a genuine outside transporter. -/
theorem align_pair (v w : V) (hv : C.weight v = 2) (hw : C.weight w = 6)
    {g : G} (hout : g ∉ normalizer (L : Set G))
    (hg : g * (v : G) * g⁻¹ = w) :
    ∃ a : G, a ∉ normalizer (L : Set G) ∧ a * (v : G) * a⁻¹ = (v : G) * (C.z : G) := by
  have hweight : C.weight w = C.weight (v * C.z) := by rw [C.weight_mul_z,hv,hw]
  obtain ⟨l,hl,he⟩ := C.conjugator_of_weight w (v * C.z) hweight
  refine ⟨l*g,?_,?_⟩
  · intro hh
    apply hout
    have hm := (normalizer (L : Set G)).mul_mem
      ((normalizer (L : Set G)).inv_mem (L.le_normalizer hl)) hh
    simpa only [inv_mul_cancel_left] using hm
  · calc
      (l*g) * (v : G) * (l*g)⁻¹ = l * (g * (v : G) * g⁻¹) * l⁻¹ := by group
      _ = l * (w : G) * l⁻¹ := by rw [hg]
      _ = (v : G) * (C.z : G) := he

omit [Finite G] in
/-- An outside complementary fusion pair prevents the normalizer from swapping its two weights. -/
theorem selected_weight_two (hnone : NoEscape L V)
    (v w : V) (hv : C.weight v = 2) {g m : G}
    (hout : g ∉ normalizer (L : Set G))
    (hg : g * (v : G) * g⁻¹ = (v : G) * (C.z : G))
    (hm : m ∈ normalizer (L : Set G)) (hw : m * (v : G) * m⁻¹ = w) :
    C.weight w = 2 := by
  have he := (EightCore.equal_size_iff (C.word v) (C.word w)).mp
    (C.normalizer_preserves_size v w hm hw)
  change C.weight v = C.weight w ∨ C.weight v + C.weight w = 8 at he
  have hw26 : C.weight w = 2 ∨ C.weight w = 6 := by omega
  rcases hw26 with hw2 | hw6
  · exact hw2
  have hv1 : (v : G) ≠ 1 := by
    intro hh
    have h0 : C.weight v = 0 := (C.weight_zero_iff v).mpr (Subtype.ext hh)
    omega
  have hweight : C.weight w = C.weight (v * C.z) := by rw [C.weight_mul_z,hv,hw6]
  obtain ⟨l,hl,hlw⟩ := C.conjugator_of_weight w (v * C.z) hweight
  exfalso
  apply hout
  apply conjugator_mem_of_centralizer_le (hnone v v.property hv1)
  refine ⟨l*m,(normalizer (L : Set G)).mul_mem (L.le_normalizer hl) hm,?_⟩
  calc
    (l*m) * (v : G) * (l*m)⁻¹ = l * (m * (v : G) * m⁻¹) * l⁻¹ := by group
    _ = l * (w : G) * l⁻¹ := by rw [hw]
    _ = (v : G) * (C.z : G) := hlw
    _ = g * (v : G) * g⁻¹ := hg.symm

/-- Select the literal point Sylow while preserving the core coordinates and outside fusion. -/
theorem seed_of_pair
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} K) (hnone : NoEscape L V)
    (hMV : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (v : V) (hv : C.weight v = 2) {g : G}
    (hout : g ∉ normalizer (L : Set G))
    (hg : g * (v : G) * g⁻¹ = (v : G) * (C.z : G)) :
    Nonempty (AlternatingEightFusionSeed T L V) := by
  obtain ⟨m,hm,S,hS⟩ := T.exists_conjugate_local_centralizer_sylow
    (normalizer (L : Set G)) (structural G T L h).1 (v : G) (D.le_sylow v.property)
  let w : V := ⟨m * (v : G) * m⁻¹,(mem_normalizer_iff.mp (hMV hm) v).mp v.property⟩
  have hw : C.weight w = 2 := C.selected_weight_two hnone v w hv hout hg hm rfl
  have hw1 : (w : G) ≠ 1 := by
    intro hh
    have h0 : C.weight w = 0 := (C.weight_zero_iff w).mpr (Subtype.ext hh)
    omega
  have hcentral : normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G) =
      centralizer ({(w : G)} : Set G) := inf_eq_right.mpr (hnone w w.property hw1)
  have hs : ∃ R : Sylow 2 (centralizer ({(w : G)} : Set G)),
      (R : Subgroup (centralizer ({(w : G)} : Set G))).map
        (centralizer ({(w : G)} : Set G)).subtype =
          (T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G) := by
    have hh : ∃ R : Sylow 2 (normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G) : Subgroup G),
        (R : Subgroup _).map
          (normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G)).subtype =
            (T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G) := ⟨S,hS⟩
    rw [hcentral] at hh
    exact hh
  obtain ⟨R,hR⟩ := hs
  have hmz : m * (C.z : G) * m⁻¹ = C.z := mul_inv_eq_iff_eq_mul.mpr
    (mem_centralizer_singleton_iff.mp
      (normalizer_centralizes_fixed_line h D structural C.z.property C.z_ne
        C.z_fixed C.fixed_line hm))
  refine ⟨{
    groupEquiv := C.groupEquiv
    vectorEquiv := C.vectorEquiv
    intertwines := C.intertwines
    v := w
    z := C.z
    weight_two := hw
    constant := C.constant
    sylow := R
    sylow_image := hR
    g := m*g*m⁻¹
    outside := ?_
    conjugates := ?_ }⟩
  · intro hh
    apply hout
    have hn := (normalizer (L : Set G)).mul_mem
      ((normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).inv_mem hm) hh) hm
    simpa [mul_assoc] using hn
  · calc
      (m*g*m⁻¹) * (w : G) * (m*g*m⁻¹)⁻¹ = m * (g * (v : G) * g⁻¹) * m⁻¹ := by
        dsimp only [w]; group
      _ = m * ((v : G) * (C.z : G)) * m⁻¹ := by rw [hg]
      _ = (w : G) * (m * (C.z : G) * m⁻¹) := by dsimp only [w]; group
      _ = (w : G) * (C.z : G) := by rw [hmz]

end AlternatingEightCoreCoordinates

/-- The eight-letter geometric input to the original alternating row of 12.2.16. -/
theorem alternatingEight_core_geometry
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} K) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hcore : Chapter6.Source.IsConjugationModel L V
      (alternatingCoreRepresentation (Fin 8))) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V) := by
  classical
  obtain ⟨e,f,hf⟩ := hcore
  let C : AlternatingEightCoreCoordinates L V := ⟨e,f,hf⟩
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) :=
    (((structural G T L h).2.2 V D).2.2.2).resolve_right hne
  by_cases hTI : IsTISubgroup V
  · exact Or.inl hTI
  right
  have hn := mt (isTISubgroup_iff V).mpr hTI
  push Not at hn
  obtain ⟨g,hg,x,hx,hgx,hx1⟩ := hn
  have hout : g ∉ normalizer (L : Set G) := fun hh => hg (hMV hh)
  let v : V := ⟨x,hx⟩
  let w : V := ⟨g*x*g⁻¹,hgx⟩
  rcases C.outside_weights h D structural hnone hMV v w hx1 hout rfl with hc | hc
  · obtain ⟨a,ha,hea⟩ := C.align_pair v w hc.1 hc.2 hout rfl
    exact C.seed_of_pair h D structural hnone hMV v hc.1 ha hea
  · have hi : g⁻¹ * (w : G) * (g⁻¹)⁻¹ = v := by dsimp only [w,v]; group
    have hout' : g⁻¹ ∉ normalizer (L : Set G) := fun hh =>
      hout (by simpa only [inv_inv] using (normalizer (L : Set G)).inv_mem hh)
    obtain ⟨a,ha,hea⟩ := C.align_pair w v hc.2 hc.1 hout' hi
    exact C.seed_of_pair h D structural hnone hMV w hc.2 ha hea

/-- Application to the literal alternating row: only the independent six-letter branch remains. -/
theorem alternating_of_six_core_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (six : (letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulAction (alternatingCoreRepresentation (Fin 6))) → IsTISubgroup V)
    (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 8)
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulCentralAction (alternatingNatural n)) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V) := by
  exact alternating_of_core_geometry D h.quasisimple hne six
    (alternatingEight_core_geometry h D structural hnone hne) n hlo hhi e

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

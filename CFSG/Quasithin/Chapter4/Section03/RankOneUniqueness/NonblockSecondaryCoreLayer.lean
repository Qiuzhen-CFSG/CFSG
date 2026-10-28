module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameCoreCoverage
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryComponent
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryNormalizer
public import Theory.GroupTheory.PGroup.CharacteristicTwoNormalClosure
public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.Frattini.NormalClosureElementary

/-!
# A quadratic orbit inside the original secondary component core

Let N=N_G(Z_S) and E=⟨U^N⟩, with U=Z(Q). The source radical bound
puts O₂(N) in R₂. Since U is the second center of R₂, its displacement
under O₂(N) lies in the normal root Z_S, which U centralizes. The
characteristic-two normal-closure theorem gives E≤O₂(N). Normal-closure
commutator transfer then gives [O₂(N),E]≤Z_S and Φ(E)≤Z_S; in particular
E has class at most two and E/Z_S is elementary abelian.

The original crossing element forces U<E: equality would make T normalize
U, whose full normalizer is H. Since the selected K_Z is normal in N
and contains U, all of E lies in K_Z and hence in its intrinsic two-core.
This puts every original T-conjugate of U in the same O₂(K_Z), without
assuming a terminal quotient model or SecondarySourceData. The final
application uses the actual sourceComponent and its original two embeddings.

These statements strengthen the geometry available before strict secondary
core enlargement. They do not prove K₂<O₂(K_Z)K₂, construct MSData or its
simultaneous markings, or complete the nonblock contradiction. Those remain
with qt-d-1222-rankone-uniqueness-nonblock; the independent whole-core
nonbinary classification retains qt-c134-nonbinary-linear-three-source.
Source: Aschbacher--Smith, original 4.3.10--14, printed pp.617--618,
and the characteristic-two quadratic normal-closure argument.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}

/-- The normal closure of the actual natural center in the original root normalizer. -/
@[expose] noncomputable def rootCoreLayer (c : SourceConfiguration T L) : Subgroup G :=
  (normalClosure ((U c).subgroupOf (rootNormalizer c) : Set (rootNormalizer c))).map
    (rootNormalizer c).subtype

namespace RootCoordinates
variable (m : RootCoordinates d)
include m

omit [Finite G] m in
private theorem center_elementary (d : MSData c n) : IsElementaryAbelian 2 (U c) := by
  obtain ⟨A,B,hA,_,_,_,_,_,hi,_⟩ := d.exists_elementary_core_decomposition
  let := hA
  exact IsElementaryAbelian.of_injective (inclusion (hi.ge.trans inf_le_left))
    (inclusion_injective _)

omit [Finite G] m in
private theorem center_le_rootNormalizer (d : MSData c n) : U c ≤ rootNormalizer c :=
  ((le_centralizer (U c)).trans (centralizer_le d.root_le_center)).trans
    (Subgroup.centralizer_le_normalizer _)

private theorem rootNormalizer_core_le_radical (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (rootNormalizer c).pCoreIn 2 ≤ R₂ c :=
  m.enlarged_core_le_radical_source hn D _
    (sup_le (secondary_centralizes_root.trans (Subgroup.centralizer_le_normalizer _))
      (inf_le_left.trans (root_normalized c D)))

private theorem rootNormalizer_core_displacement (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ⁅pCore 2 (rootNormalizer c),(U c).subgroupOf (rootNormalizer c)⁆ ≤
      (root c).subgroupOf (rootNormalizer c) := by
  apply (map_le_iff_le_comap).mp
  rw [Subgroup.map_commutator,map_subgroupOf_eq_of_le (center_le_rootNormalizer d)]
  rw [commutator_comm]
  exact (commutator_mono le_rfl (m.rootNormalizer_core_le_radical hn D)).trans
    (m.center_radical_commutator_le_root hn D)

/-- Characteristic two places the entire orbit in the root normalizer's two-core. -/
theorem rootCoreLayer_le_core (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    rootCoreLayer c ≤ (rootNormalizer c).pCoreIn 2 := by
  let N := rootNormalizer c
  let Z := (root c).subgroupOf N
  let A := (U c).subgroupOf N
  let : Z.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : IsElementaryAbelian 2 (U c) := center_elementary d
  have hAc : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf (center_le_rootNormalizer d)
  have hZA : ⁅Z,A⁆ = ⊥ := by
    apply (map_injective N.subtype_injective)
    rw [Subgroup.map_commutator,Subgroup.map_bot,
      map_subgroupOf_eq_of_le (show root c ≤ N from (root c).le_normalizer),
      map_subgroupOf_eq_of_le (center_le_rootNormalizer d)]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (d.root_le_center.trans (le_centralizer (U c)))
  have hp := normalClosure_isPGroup_of_characteristicTwo Z A
    (EndgameSieve.rootNormalizer_characteristicTwo c D h) inferInstance
    (m.rootNormalizer_core_displacement hn D) hZA hAc
  exact map_mono (le_sSup ⟨inferInstance,hp⟩ : normalClosure (A : Set N) ≤ pCore 2 N)

omit [Finite G] m in
/-- The original natural center embeds in its actual root-normalizer orbit. -/
theorem rootCoreLayer_contains_center (d : MSData c n) : U c ≤ rootCoreLayer c := by
  have hh := map_mono (f := (rootNormalizer c).subtype)
    (le_normalClosure : (U c).subgroupOf (rootNormalizer c) ≤
      normalClosure ((U c).subgroupOf (rootNormalizer c) : Set _))
  rwa [map_subgroupOf_eq_of_le (center_le_rootNormalizer d)] at hh

omit [Finite G] m in
/-- The orbit is normalized by the complete root normalizer. -/
theorem rootCoreLayer_normalized : rootNormalizer c ≤ normalizer (rootCoreLayer c : Set G) := by
  have hh := (normalClosure ((U c).subgroupOf (rootNormalizer c) : Set _)).le_normalizer_map
    (rootNormalizer c).subtype
  simpa only [rootCoreLayer,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh

/-- The whole root-normalizer two-core acts trivially on the orbit modulo Z_S. -/
theorem rootCoreLayer_core_commutator (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ⁅(rootNormalizer c).pCoreIn 2,rootCoreLayer c⁆ ≤ root c := by
  let N := rootNormalizer c
  let Z := (root c).subgroupOf N
  let : Z.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hh := map_mono (f := N.subtype) (commutator_normalClosure_le_of_normal
    (pCore 2 N) ((U c).subgroupOf N) Z (m.rootNormalizer_core_displacement hn D))
  rw [Subgroup.map_commutator,map_subgroupOf_eq_of_le
    (show root c ≤ N from (root c).le_normalizer)] at hh
  exact hh

/-- The original orbit has central commutator in the literal source root. -/
theorem rootCoreLayer_class_two (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ⁅rootCoreLayer c,rootCoreLayer c⁆ ≤ root c ∧
      ⁅⁅rootCoreLayer c,rootCoreLayer c⁆,rootCoreLayer c⁆ = ⊥ := by
  have hder := (commutator_mono (m.rootCoreLayer_le_core hn D h) le_rfl).trans
    (m.rootCoreLayer_core_commutator hn D)
  refine ⟨hder,?_⟩
  apply bot_unique
  apply (commutator_mono hder le_rfl).trans
  apply le_of_eq
  rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
  exact ((m.rootCoreLayer_le_core hn D h).trans (m.rootNormalizer_core_le_radical hn D)).trans
    (m.radical_centralizes_root hn D)


/-- The whole orbit subgroup has Frattini subgroup in the original root. -/
theorem rootCoreLayer_frattini_le_root (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (frattini (rootCoreLayer c)).map (rootCoreLayer c).subtype ≤ root c := by
  let N := rootNormalizer c
  let A := (U c).subgroupOf N
  let E := normalClosure (A : Set N)
  let : IsElementaryAbelian 2 (U c) := center_elementary d
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf (center_le_rootNormalizer d)
  have hE : E ≤ pCore 2 N := by
    apply (map_le_map_iff_of_injective N.subtype_injective).mp
    exact m.rootCoreLayer_le_core hn D h
  have hh := map_mono (f := N.subtype)
    (normalClosure_frattini_image_le_commutator A (pCore 2 N) pCore_isPGroup hE)
  rw [Subgroup.map_commutator,←frattini_image_map E N.subtype N.subtype_injective] at hh
  exact hh.trans (m.rootCoreLayer_core_commutator hn D)

/-- The orbit modulo the same root is an elementary two-section of the core. -/
theorem rootCoreLayer_root_quotient_elementary (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let : ((root c).subgroupOf (rootCoreLayer c)).Normal :=
      normal_subgroupOf_of_le_normalizer (map_subtype_le _)
    IsElementaryAbelian 2 (rootCoreLayer c ⧸ (root c).subgroupOf (rootCoreLayer c)) := by
  let : ((root c).subgroupOf (rootCoreLayer c)).Normal :=
    normal_subgroupOf_of_le_normalizer (map_subtype_le _)
  apply elementary_quotient_of_frattini_le
    ((isPGroup_pCoreIn 2 (rootNormalizer c)).to_le (m.rootCoreLayer_le_core hn D h))
  exact map_le_iff_le_comap.mp (m.rootCoreLayer_frattini_le_root hn D h)

omit m in
/-- The crossing element forces strict growth beyond U, independently of the terminal models. -/
theorem center_lt_rootCoreLayer (d : MSData c n)
    (D : Chapter12.Section02.ChosenModule T L V) : U c < rootCoreLayer c := by
  apply lt_of_le_of_ne (rootCoreLayer_contains_center d)
  intro he
  have ht : c.t ∈ normalizer (U c : Set G) := by
    rw [he]
    exact rootCoreLayer_normalized (root_normalized c D c.crossing_mem)
  rw [center_normalizer_eq d D] at ht
  exact c.crossing_outside ⟨c.crossing_mem,ht⟩

/-- A normal component containing K₂ contains this same orbit in its two-core. -/
theorem rootCoreLayer_le_component_core (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (B : Subgroup (rootNormalizer c)) (hBn : B.Normal)
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype) :
    rootCoreLayer c ≤ (B.map (rootNormalizer c).subtype).pCoreIn 2 := by
  let := hBn
  have hUB : (U c).subgroupOf (rootNormalizer c) ≤ B := by
    intro u hu
    have hh := hsec (m.center_le_secondary hn hu)
    exact (mem_map_iff_mem (rootNormalizer c).subtype_injective).mp hh
  have hlB : rootCoreLayer c ≤ B.map (rootNormalizer c).subtype :=
    map_mono (normalClosure_le_normal hUB)
  exact (le_inf hlB (m.rootCoreLayer_le_core hn D h)).trans
    (inf_pCoreIn_le_of_le 2 (map_subtype_le _))

omit [Finite G] m in
/-- Every original Sylow conjugate of U belongs to the same orbit subgroup. -/
theorem crossed_center_le_rootCoreLayer (d : MSData c n)
    (D : Chapter12.Section02.ChosenModule T L V) (t : G) (ht : t ∈ (T : Subgroup G)) :
    (U c).map (MulAut.conj t).toMonoidHom ≤ rootCoreLayer c := by
  have he := mem_normalizer_iff_map_conj_eq.mp
    (rootCoreLayer_normalized (root_normalized c D ht))
  exact (map_mono (rootCoreLayer_contains_center d)).trans_eq he

end RootCoordinates

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree

/-- Apply the orbit, Frattini and crossing conclusions to the selected original component.
Only the earlier MS witness and its simultaneous markings remain explicit. -/
theorem MSData.sourceComponent_core_layer (d : MSData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) :
    let B := d.sourceComponent hn D h hL hSL
    U c < rootCoreLayer c ∧
      rootCoreLayer c ≤ (B.map (rootNormalizer c).subtype).pCoreIn 2 ∧
      (frattini (rootCoreLayer c)).map (rootCoreLayer c).subtype ≤ root c ∧
      ⁅rootCoreLayer c,rootCoreLayer c⁆ ≤ root c ∧
      ⁅⁅rootCoreLayer c,rootCoreLayer c⁆,rootCoreLayer c⁆ = ⊥ ∧
      ∀ t ∈ (T : Subgroup G), (U c).map (MulAut.conj t).toMonoidHom ≤
        (B.map (rootNormalizer c).subtype).pCoreIn 2 := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  obtain ⟨_,hBn,hsec,_⟩ := d.sourceComponent_spec hn D h hL hSL
  have hc := m.rootCoreLayer_le_component_core hn D h _ hBn hsec.le
  obtain ⟨hcomm,hclass⟩ := m.rootCoreLayer_class_two hn D h
  exact ⟨RootCoordinates.center_lt_rootCoreLayer d D,hc,m.rootCoreLayer_frattini_le_root hn D h,
    hcomm,hclass,fun t ht =>
    (RootCoordinates.crossed_center_le_rootCoreLayer d D t ht).trans hc⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

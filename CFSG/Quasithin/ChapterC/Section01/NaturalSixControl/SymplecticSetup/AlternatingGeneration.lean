module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.Generation
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Actual A6 normal-closure generation for MS93

For the same marked A6 image, any relative normal closure escaping the
local two-core maps onto the simple quotient. Joining with the edge group
therefore recovers the whole vertex group. Actual edge transitivity supplies
MS93 (2.3)(b) at every edge of the free-holomorph tree.

The original quotient map and two-core are retained. The commutator and
edge-witness estimates of (2.3)(c,d) remain separate module obligations.
Source: MS93 (3.8), first paragraph, printed p.877.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M}
  [L.Normal] [W.Normal] (s : Source L R W)

omit [Finite M] in
private theorem base_normal_closure_core_top
    (himage : s.projection.range = alternatingGroup (Fin 6))
    (N : Subgroup (FreeAmalgam R))
    (hN : N ≤ Mbar R) (hn : Mbar R ≤ normalizer (N : Set (FreeAmalgam R)))
    (hne : ¬ N ≤ (pCore 2 M).map (embedM R)) :
    N ⊔ (pCore 2 M).map (embedM R) = Mbar R := by
  let A : Subgroup M := N.comap (embedM R)
  let : A.Normal := by
    constructor
    intro x hx m
    show embedM R (m*x*m⁻¹) ∈ N
    simpa only [map_mul,map_inv] using
      le_normalizer_iff.mp hn (embedM R m) ⟨m,rfl⟩ (embedM R x) hx
  let q : M →* alternatingGroup (Fin 6) :=
    s.projection.codRestrict _ (fun m => himage ▸ ⟨m,rfl⟩)
  have hq : Function.Surjective q := by
    intro y
    have hy : (y : Equiv.Perm (Fin 6)) ∈ s.projection.range := by rw [himage]; exact y.property
    obtain ⟨m,hm⟩ := hy
    exact ⟨m,Subtype.ext hm⟩
  have hk : q.ker = pCore 2 M := by
    rw [←s.projection_kernel]
    ext m
    exact Subtype.ext_iff
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : (A.map q).Normal := Normal.map inferInstance q hq
  have htop : A.map q = ⊤ := by
    rcases (inferInstance : (A.map q).Normal).eq_bot_or_eq_top with hz | ht
    · have hA : A ≤ pCore 2 M := by
        rw [←hk]
        exact (Subgroup.map_eq_bot_iff A).mp hz
      apply False.elim
      apply hne
      have hm := map_mono (f := embedM R) hA
      simpa only [A,map_comap_eq,inf_eq_right.mpr (show N ≤ (embedM R).range from hN)] using hm
    · exact ht
  have hAQ : A ⊔ pCore 2 M = ⊤ := by
    have hh := congrArg (Subgroup.comap q) htop
    simpa only [comap_map_eq,hk,comap_top] using hh
  have hm := congrArg (Subgroup.map (embedM R)) hAQ
  change N ⊔ (pCore 2 M).map (embedM R) = (embedM R).range
  simpa only [Subgroup.map_sup,A,map_comap_eq,inf_eq_right.mpr (show N ≤ (embedM R).range from hN),
    ←MonoidHom.range_eq_map] using hm

/-- A6 simplicity gives the printed normal-closure generation on every edge. -/
theorem generation_of_alternating_image
    (himage : s.projection.range = alternatingGroup (Fin 6)) :
    CriticalCriterion.Generation R := by
  apply Generation.of_edge R (alpha R) (beta R) rfl (base_adjacent R)
  intro x hx hout
  let N := conjugatesIn (zpowers x) (Mbar R)
  have hxR : x ∈ R.map (embedM R) := by simpa only [Q_beta] using hx
  have hNM : N ≤ Mbar R := conjugatesIn_le _ _
    ((zpowers_le.mpr hxR).trans (map_le_range _ _))
  have hxN : x ∈ N := by
    apply le_iSup (fun g : Mbar R => rightConjugate (zpowers x) g) (1 : Mbar R)
    exact ⟨x,mem_zpowers x,by simp⟩
  have htop := s.base_normal_closure_core_top himage N hNM
    (conjugatesIn_normalized _ _) (fun hh => hout (by
      rw [Q_alpha R s.two_group s.core_le]
      exact hh hxN))
  have hQR : (pCore 2 M).map (embedM R) ≤ R.map (embedM R) := map_mono s.core_le
  rw [show stabilizer R (alpha R) = Mbar R from stabilizer_m_base R]
  change N ⊔ Q R (beta R) = Mbar R
  rw [Q_beta]
  apply le_antisymm (sup_le hNM (map_le_range _ _))
  rw [←htop]
  exact sup_le_sup_left hQR N

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionFrattini
public import CFSG.Quasithin.ChapterG.Section02.Setup

/-!
# The full central-line normalizer in the escaping branch

Apply Frattini inside N_G(Z_S), where C_G(Z_S) is normal and its Sylow
subgroup is the literal S = C_T(Z_S). The source bound N_G(S) ≤ M gives
an elementwise factorization N_G(Z_S) = C_G(Z_S) N_M(Z_S), without assuming
C_G(Z_S) ≤ M. The TI property makes the factor in N_M(Z_S) normalize V_L,
so the normalizer and centralizer generate the same closure U.

The raw G.2 setup is then defined with its original five ambient subgroups.
Its closure, generated group, two-core and intersection agree with the
literal U, L₁, R and E in Chapter 6, retaining right conjugation throughout.
This constructs the comparison needed to apply G.2.3 in 6.1.21; it does
not assume or assert the remaining G.2 hypotheses or the escape geometry.
Their construction remains with qt-d-1222-rankone-recognition-natural.

Source: Aschbacher–Smith, 6.1.9(5), printed p.669; G.2.1 and the application
of G.2.3 in 6.1.21, printed pp.332–334, 675–676.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

private theorem frattini_factorization
    (I N : Subgroup G) (hIN : I ≤ N) (hNI : N ≤ normalizer (I : Set G))
    (P : Sylow 2 I) :
    ∀ d ∈ N, ∃ c ∈ I, ∃ m ∈ N ⊓ normalizer ((P : Subgroup I).map I.subtype : Set G),
      d = c * m := by
  let I' := I.subgroupOf N
  let : I'.Normal := (normal_subgroupOf_iff_le_normalizer hIN).mpr hNI
  let e : I ≃* I' := (subgroupOfEquivOfLe hIN).symm
  let P' : Sylow 2 I' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : ((P' : Subgroup I').map I'.subtype).map N.subtype =
      (P : Subgroup I).map I.subtype := by
    change (((P : Subgroup I).map e.toMonoidHom).map I'.subtype).map N.subtype = _
    rw [map_map,map_map]
    rfl
  intro d hd
  have hmem : (⟨d,hd⟩ : N) ∈ I' ⊔ normalizer ((P' : Subgroup I').map I'.subtype : Set N) := by
    rw [sup_comm,P'.normalizer_sup_eq_top]
    trivial
  obtain ⟨c,hc,m,hm,he⟩ := mem_sup_of_normal_left.mp hmem
  refine ⟨c,hc,m,⟨m.property,?_⟩,(congrArg Subtype.val he).symm⟩
  have hh := ((P' : Subgroup I').map I'.subtype).le_normalizer_map N.subtype
    (mem_map_of_mem N.subtype hm)
  rwa [hmap] at hh

variable {κ : GroupClass} {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- Source 6.1.9(5) from the normalizer bound in 6.1.9(2), valid in both
centralizer branches. The two factors belong to the literal relative subgroups. -/
theorem central_line_factorization_of_S_normalizer
    (h : Hypothesis611 κ T L M V n)
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M) :
    CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L V) := by
  let Z := ZS (T : Subgroup G) L V
  let I := centralizer (Z : Set G)
  let N := normalizer (Z : Set G)
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) :=
    h.sylow_normalizes_ZS.trans (normalizer_le_normalizer_centralizer Z)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
  have hfactor := frattini_factorization I N (centralizer_le_normalizer _)
    (normalizer_le_normalizer_centralizer Z) P
  rw [hP,subgroupOf_map_subtype] at hfactor
  intro d hd
  obtain ⟨c,hc,m,hm,he⟩ := hfactor d hd
  exact ⟨c,hc,m,⟨hNS hm.2,hm.1⟩,he⟩

/-- The normalizer and centralizer generate exactly the same closure of the
natural seed. This identifies the G.2 closure with the literal escaping U. -/
theorem natural_escape_normalizer_span
    (h : Hypothesis611 κ T L M V n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M) :
    conjugateSpanBy (layer L V) (Escape.H (T : Subgroup G) L V) =
      Escape.U (T : Subgroup G) L V := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨d,hd,b,hb,rfl⟩
    change d * b * d⁻¹ ∈ Escape.U (T : Subgroup G) L V
    obtain ⟨c,hc,m,hm,he⟩ := central_line_factorization_of_S_normalizer h hNS d hd
    have hmB : m ∈ normalizer (layer L V : Set G) :=
      inf_normalizer_le_of_trivial_intersections hE.ti h.ZS_ne_bot inf_le_left hm
    have hmb : m * b * m⁻¹ ∈ layer L V := (mem_normalizer_iff.mp hmB b).mp hb
    have hh : c * (m * b * m⁻¹) * c⁻¹ ∈ Escape.U (T : Subgroup G) L V :=
      (le_iSup (fun i : Escape.I (T : Subgroup G) L V =>
        (layer L V).map (MulAut.conj (i : G)).toMonoidHom) ⟨c,hc⟩)
        (mem_map_of_mem (MulAut.conj c).toMonoidHom hmb)
    rw [he]
    simpa only [mul_inv_rev, mul_assoc, SetLike.mem_coe] using hh
  · apply iSup_le
    intro i x hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hx
    exact subset_closure ⟨i, (centralizer_le_normalizer _) i.property, b, hb, rfl⟩

/-- The full central-line normalizer normalizes U, with the closure identity
supplied by the original local normalizer bound. -/
theorem natural_escape_normalizer_normalizes_U
    (h : Hypothesis611 κ T L M V n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M) :
    Escape.H (T : Subgroup G) L V ≤ normalizer (Escape.U (T : Subgroup G) L V : Set G) := by
  rw [← natural_escape_normalizer_span h hE hNS]
  exact le_normalizer_conjugateSpanBy _ _


/-- The literal G.2 data used by the escaping branch. No G.2 hypothesis or
conclusion is built into these five ambient subgroups. -/
@[expose] def naturalEscapeSetup (T L V : Subgroup G) : ChapterG.Section02.Setup G where
  V := layer L V
  V₁ := ZS T L V
  L := L
  T := T
  H := Escape.H T L V

/-- Identify all four G.2 constructions with their original Chapter 6 names,
including the right conjugate and the two-core of the actual generated group. -/
theorem natural_escape_G2_constructions
    (h : Hypothesis611 κ T L M V n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (l : G) :
    let D := naturalEscapeSetup (T : Subgroup G) L V
    D.U = Escape.U (T : Subgroup G) L V ∧
      D.I l = Escape.L1 (T : Subgroup G) L V l ∧
      D.S l = Escape.R (T : Subgroup G) L V l ∧
      D.S₂ l = Escape.E (T : Subgroup G) L V l := by
  have hU : (naturalEscapeSetup (T : Subgroup G) L V).U = Escape.U (T : Subgroup G) L V :=
    natural_escape_normalizer_span h hE hNS
  have hI : (naturalEscapeSetup (T : Subgroup G) L V).I l = Escape.L1 (T : Subgroup G) L V l := by
    change (naturalEscapeSetup (T : Subgroup G) L V).U ⊔
      ((naturalEscapeSetup (T : Subgroup G) L V).U).map (MulAut.conj l⁻¹).toMonoidHom = _
    rw [hU]
    rfl
  refine ⟨hU,hI,?_,?_⟩
  · change ((naturalEscapeSetup (T : Subgroup G) L V).I l).pCoreIn 2 = _
    rw [hI]
    rfl
  · change (naturalEscapeSetup (T : Subgroup G) L V).U ⊓
      ((naturalEscapeSetup (T : Subgroup G) L V).U).map (MulAut.conj l⁻¹).toMonoidHom = _
    rw [hU]
    rfl

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

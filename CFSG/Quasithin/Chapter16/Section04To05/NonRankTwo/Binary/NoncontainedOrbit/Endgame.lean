module

public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Binary.NoncontainedOrbit.Definitions
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Stellmacher.ElementaryAbelianMaxJ

/-!
# Residual reduction in the noncontained binary branch

This is the final deduction on printed p.1201 of Aschbacher–Smith,
combined manuscript of 1 March 2004, Lemma 16.5.12. The component is
perfect, so the two-residual of C_G(z)=LT is L. If the two-residual of
I=N_G(J(T)) centralizes Z(J(T)), its own two-perfectness puts it in the
two-residual of C_G(Z(J(T))) and hence in L. The Sylow supplement then
gives I=N_L(J(T))T. The local normalizer calculation forces I to fix A,
contradicting an orbit of size three.

The four-subgroup geometry, fusion orbit, and action on the Thompson
center are explicit premises here. They remain obligations of the
noncontained-branch assembly; this module does not assert 16.5.12.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G]

/-- Conjugation invariance of the elementary Thompson construction makes
T a subgroup of its normalizer. -/
theorem sylow_le_thompsonNormalizer (T : Sylow 2 G) :
    (T : Subgroup G) ≤
      normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)).map
    (MulAut.conj t).toMonoidHom = _
  have he : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = T :=
    mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
  rw [← Stellmacher.elementaryAbelianMaxJ_map_equiv (MulAut.conj t), he]

variable [Finite G] {T : Sylow 2 G} {z u g : G} {L R X : Subgroup G}

/-- The residual equality uses perfectness of the genuine component and
normalization by T, not an ambient normality assumption on L. -/
theorem centralizer_twoResidual_eq_component
    (h : EarlierInputs T z L g R X u)
    (c : ElementaryConfiguration T z u g L R) :
    (pResidual 2 (involutionCentralizer z)).map (involutionCentralizer z).subtype = L := by
  let _ : IsQuasisimple (L.subgroupOf (involutionCentralizer z)) := h.component.2.2
  let _ : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component.1).toMonoidHom)
    (subgroupOfEquivOfLe h.component.1).surjective
  have hp : IsPPerfect 2 L := by
    intro N hN hq
    let _ := hN
    have hsub : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hq.isNilpotent
    apply eq_top_iff.mpr
    intro l _
    exact (QuotientGroup.eq_one_iff l).mp (Subsingleton.elim _ _)
  rw [c.centralizer_eq]
  exact embedded_pResidual_join_pGroup L (T : Subgroup G) hp T.isPGroup'
    h.sylow_normalizes

/-- Once A belongs to the maximal-order family, its distinguished central
involution lies in the actual center of J(T). -/
theorem central_mem_thompsonCenter
    (h : EarlierInputs T z L g R X u)
    (c : ElementaryConfiguration T z u g L R)
    (hA : elementaryGroup T L u ∈
      Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G)) :
    z ∈ (center (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G))).map
      (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)).subtype := by
  let J := Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)
  have hAJ : elementaryGroup T L u ≤ J := le_sSup hA
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun B hB => hB.1
  refine ⟨⟨z, hAJ c.central_mem_elementary⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro j
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (h.sylow_centralizes (hJT j.property))

/-- The full residual chain, with all residuals embedded from their own
groups. Two-perfectness justifies the first, stronger containment. -/
theorem thompsonNormalizer_residual_chain
    (h : EarlierInputs T z L g R X u)
    (c : ElementaryConfiguration T z u g L R)
    (hA : elementaryGroup T L u ∈
      Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G))
    (hfixed : let J := Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)
      let I := normalizer (J : Set G)
      (pResidual 2 I).map I.subtype ≤
        centralizer ((center J).map J.subtype : Set G)) :
    let J := Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)
    let I := normalizer (J : Set G)
    let C := centralizer ((center J).map J.subtype : Set G)
    (pResidual 2 I).map I.subtype ≤ (pResidual 2 C).map C.subtype ∧
      (pResidual 2 C).map C.subtype ≤ L := by
  dsimp only
  let J := Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)
  let I := normalizer (J : Set G)
  let C := centralizer ((center J).map J.subtype : Set G)
  let D := (pResidual 2 I).map I.subtype
  have hDC : D ≤ C := hfixed
  have hpD : IsPPerfect 2 (D.subgroupOf C) :=
    (isPPerfect_embedded_pResidual 2 I).of_surjective
      (subgroupOfEquivOfLe hDC).symm.toMonoidHom
      (subgroupOfEquivOfLe hDC).symm.surjective
  have hDres := map_mono (f := C.subtype)
    (le_pResidual_of_isPPerfect (D.subgroupOf C) hpD)
  rw [map_subgroupOf_eq_of_le hDC] at hDres
  refine ⟨hDres, ?_⟩
  have hCz : C ≤ involutionCentralizer z := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hx z (central_mem_thompsonCenter h c hA)).symm
  exact (embedded_pResidual_mono 2 hCz).trans
    (centralizer_twoResidual_eq_component h c).le

/-- The ambient Sylow subgroup restricts to a Sylow subgroup of I. Its
residual supplement gives the source's factorization N_L(J(T))T. -/
theorem thompsonNormalizer_eq_component_normalizer_join_sylow
    (h : EarlierInputs T z L g R X u)
    (c : ElementaryConfiguration T z u g L R)
    (hA : elementaryGroup T L u ∈
      Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G))
    (hfixed : let J := Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)
      let I := normalizer (J : Set G)
      (pResidual 2 I).map I.subtype ≤
        centralizer ((center J).map J.subtype : Set G)) :
    let I := normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G)
    I = (L ⊓ I) ⊔ (T : Subgroup G) := by
  dsimp only
  let I := normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G)
  have hTI : (T : Subgroup G) ≤ I := sylow_le_thompsonNormalizer T
  have hs := congrArg (fun S : Subgroup I => S.map I.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTI))
  rw [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTI,
    ← MonoidHom.range_eq_map, range_subtype] at hs
  have hdL := thompsonNormalizer_residual_chain h c hA hfixed
  apply le_antisymm ?_ (sup_le inf_le_right hTI)
  calc
    _ = (pResidual 2 I).map I.subtype ⊔ (T : Subgroup G) := hs.symm
    _ ≤ (L ⊓ I) ⊔ (T : Subgroup G) := sup_le (le_sup_of_le_left (le_inf (hdL.1.trans hdL.2) (map_subtype_le _)))
      le_sup_right

open scoped Pointwise

/-- The join is the actual set product N_L(J(T))T, and N_L(J(T)) is
normal inside I. No ambient normality of the component is claimed. -/
theorem thompsonNormalizer_factorization
    (h : EarlierInputs T z L g R X u)
    (c : ElementaryConfiguration T z u g L R)
    (hA : elementaryGroup T L u ∈
      Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G))
    (hfixed : let J := Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)
      let I := normalizer (J : Set G)
      (pResidual 2 I).map I.subtype ≤
        centralizer ((center J).map J.subtype : Set G)) :
    let I := normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G)
    ((L ⊓ I).subgroupOf I).Normal ∧
      (I : Set G) = ((L ⊓ I : Subgroup G) : Set G) * ((T : Subgroup G) : Set G) := by
  dsimp only
  let I := normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G)
  have hf : I = (L ⊓ I) ⊔ (T : Subgroup G) :=
    thompsonNormalizer_eq_component_normalizer_join_sylow h c hA hfixed
  have hIL : I ≤ normalizer (L : Set G) :=
    hf.le.trans (sup_le (inf_le_left.trans L.le_normalizer) h.sylow_normalizes)
  have hIK : I ≤ normalizer ((L ⊓ I : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro i hi x hx
    exact ⟨(mem_normalizer_iff.mp (hIL hi) x).mp hx.1,
      I.mul_mem (I.mul_mem hi hx.2) (I.inv_mem hi)⟩
  refine ⟨normal_subgroupOf_of_le_normalizer hIK, ?_⟩
  rw [← coe_mul_of_right_le_normalizer_left (L ⊓ I) (T : Subgroup G)
    ((sylow_le_thompsonNormalizer T).trans hIK), ← hf]

/-- The terminal contradiction is conditional on the three genuine geometric
outputs. Constructing those outputs is still required for 16.5.12. -/
theorem noncontained_contradiction_of_local_action
    (h : EarlierInputs T z L g R X u)
    (c : ElementaryConfiguration T z u g L R)
    (hA : elementaryGroup T L u ∈
      Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G))
    (hfixed : let J := Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)
      let I := normalizer (J : Set G)
      (pResidual 2 I).map I.subtype ≤
        centralizer ((center J).map J.subtype : Set G))
    (hlocal : L ⊓
      normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
        normalizer (elementaryGroup T L u : Set G))
    (hTA : (T : Subgroup G) ≤ normalizer (elementaryGroup T L u : Set G))
    (horbit : Nat.card (thompsonNormalizerOrbit T (elementaryGroup T L u)) = 3) : False := by
  have hI : normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
      normalizer (elementaryGroup T L u : Set G) := by
    rw [thompsonNormalizer_eq_component_normalizer_join_sylow h c hA hfixed]
    exact sup_le hlocal hTA
  have he : thompsonNormalizerOrbit T (elementaryGroup T L u) =
      {elementaryGroup T L u} := by
    ext B
    constructor
    · rintro ⟨i, hi, he⟩
      exact he.symm.trans (mem_normalizer_iff_map_conj_eq.mp (hI hi))
    · rintro rfl
      exact ⟨1, one_mem _, conjBy_one _⟩
  rw [he] at horbit
  have hone : Nat.card ({elementaryGroup T L u} : Set (Subgroup G)) = 1 :=
    Nat.card_unique
  omega

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary

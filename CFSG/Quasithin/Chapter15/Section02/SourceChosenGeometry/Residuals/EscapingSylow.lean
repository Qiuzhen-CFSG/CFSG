module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Assembly

/-!
# Sylow geometry of an original escaping plane overgroup

For the actual offender plane `E = [V,B]`, the original input already proves
all geometric ingredients of 15.2.16--18.  Its residual and `S = C_T(E)` lie
in every escaping overgroup.  Such an overgroup cannot contain `T`, and the
equal-plane row is impossible.  A Sylow extension of `S` has index at most
two over `S`; if larger, it normalizes `S` and therefore lies in the literal
intersection `M ∩ Mc`.  The source intersection factorization then forces
`T` into the escaping group, a contradiction.

These statements use `ResidualInput` directly, without the partner's
prime-to-three residual identity or `PlaneUniquenessPreceding`.  The public
Sylow theorem supplies the actual subgroup needed by the equality-row
component exclusions.

Source: Aschbacher--Smith, 15.2.16--18, printed pp.1112--1113,
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}

/-- The full centralizer of the actual offender plane lies in the original
partner intersection with any escaping group. -/
theorem ResidualInput.plane_centralizer_le_intersection
    (r : ResidualInput h H B) (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    centralizer (⁅V,B⁆ : Subgroup G) ≤ Mc ⊓ I := by
  have hc : centralizer (⁅V,B⁆ : Subgroup G) ≤ Mc := by
    rw [r.partner_eq_centralizer]
    exact centralizer_le r.seed_le_plane
  exact le_inf hc ((inf_eq_right.mpr hc).symm ▸ hI.2.1)

/-- Both literal source subgroups K and S lie in the escaping intersection. -/
theorem ResidualInput.residual_sup_planeCentralizer_le
    (r : ResidualInput h H B) (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    residual H ⊔ planeCentralizer T ⁅V,B⁆ ≤ Mc ⊓ I :=
  (sup_le r.residual_centralizes_plane inf_le_right).trans
    (r.plane_centralizer_le_intersection hI)

/-- The original residual cannot be contained in M, since it generates H
together with the fixed Sylow subgroup. -/
theorem ResidualInput.residual_not_le_left (r : ResidualInput h H B) :
    ¬ residual H ≤ M := by
  intro hKM
  apply r.outside.1.2
  rw [←r.residual_join]
  exact sup_le hKM h.maximal.1.2

/-- Every escaping overgroup is in the index-two plane row. -/
theorem ResidualInput.escape_index
    (r : ResidualInput h H B) (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    Nat.card (centralInvolutions T) = 2 ∧
      (planeCentralizer T ⁅V,B⁆).relIndex (T : Subgroup G) = 2 := by
  rcases r.plane_alternatives with ⟨_,he⟩ | hi
  · have hMcI : Mc ≤ I := by
      have hle := hI.2.1
      rw [←he,←r.partner_eq_centralizer,inf_idem] at hle
      exact hle
    have hcore : pCore 2 I ≠ ⊥ := by
      intro he
      apply hI.1
      change (pCore 2 I).map I.subtype = ⊥
      rw [he,Subgroup.map_bot]
    obtain ⟨N,hN,hIN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot I hcore
    have hNM : N = Mc := by
      apply Set.mem_singleton_iff.mp
      rw [←h.partner]
      exact ⟨hN,r.partner_eq_centralizer ▸ hMcI.trans hIN⟩
    exact (hI.2.2 (hNM ▸ hIN)).elim
  · exact hi

/-- An original escaping H-member cannot contain the ambient Sylow T. -/
theorem ResidualInput.sylow_not_le_escape
    (r : ResidualInput h H B) (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    ¬ (T : Subgroup G) ≤ I := by
  intro hTI
  have hcore : pCore 2 I ≠ ⊥ := by
    intro he
    apply hI.1
    change (pCore 2 I).map I.subtype = ⊥
    rw [he,Subgroup.map_bot]
  obtain ⟨N,hN,hIN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot I hcore
  have hNT : N ∈ maximalTwoLocalOvergroups (T : Subgroup G) := ⟨hN,hTI.trans hIN⟩
  rw [r.two_overgroups,Set.mem_insert_iff,Set.mem_singleton_iff] at hNT
  rcases hNT with rfl | rfl
  · exact r.residual_not_le_left ((le_sup_left.trans
      (r.residual_sup_planeCentralizer_le hI)).trans (inf_le_right.trans hIN))
  · exact hI.2.2 hIN

/-- The chosen module centralizer already lies in every escaping I. -/
theorem ResidualInput.module_centralizer_le_escape
    (r : ResidualInput h H B) (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    centralizer (V : Set G) ≤ I :=
  (centralizer_le r.plane_le).trans
    ((r.plane_centralizer_le_intersection hI).trans inf_le_right)

/-- Source 15.2.18(1) for the literal offender plane, without the
partner-residual identity: S is a Sylow subgroup of the escaping I. -/
theorem ResidualInput.sylow_in_escape
    (r : ResidualInput h H B) (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = planeCentralizer T ⁅V,B⁆ := by
  let S := planeCentralizer T ⁅V,B⁆
  have hSI : S ≤ I :=
    (le_sup_right.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_right
  obtain ⟨P,hSP⟩ := ((T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    (K := I)).exists_le_sylow
  let R : Subgroup G := (P : Subgroup I).map I.subtype
  have hSR : S ≤ R := by
    rw [←map_subgroupOf_eq_of_le hSI]
    exact map_mono hSP
  refine ⟨P,?_⟩
  change R = S
  by_contra hne
  have hp : IsPGroup 2 R := P.isPGroup'.map I.subtype
  have hRI : R ≤ I := map_subtype_le _
  have hmul : Nat.card S * S.relIndex R = Nat.card R := by
    simpa only [relIndex_bot_left] using relIndex_mul_relIndex ⊥ S R bot_le hSR
  have hmulT : Nat.card S * 2 = Nat.card T := by
    have he := relIndex_mul_relIndex ⊥ S (T : Subgroup G) bot_le inf_le_left
    have hhalf : S.relIndex (T : Subgroup G) = 2 := (r.escape_index hI).2
    simpa only [relIndex_bot_left,hhalf] using he
  have hbound : Nat.card R ≤ Nat.card T := card_le_sylow_two hp T
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hiPos : 0 < S.relIndex R := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hiNe : S.relIndex R ≠ 1 := by
    intro he
    exact hne (le_antisymm (relIndex_eq_one.mp he) hSR)
  have hiLower : 2 ≤ S.relIndex R := by omega
  have hi : S.relIndex R = 2 := by nlinarith only [hmul,hmulT,hbound,hpos,hiLower]
  have hcard : Nat.card R = Nat.card T := by rw [←hmul,hi,hmulT]
  have hnS : (S.subgroupOf R).Normal := normal_of_index_eq_two hi
  have hRS : R ≤ normalizer (S : Set G) := (normal_subgroupOf_iff_le_normalizer hSR).mp hnS
  have hRA : R ≤ M ⊓ Mc := hRS.trans r.planeCentralizer_normalizer_le_intersection
  obtain ⟨Q,hRQ⟩ := hp.exists_le_sylow
  have hRcardQ : Nat.card Q ≤ Nat.card R := by
    rw [hcard]
    exact (Nat.card_congr (Q.equiv T).toEquiv).le
  have hRQeq : R = (Q : Subgroup G) := eq_of_le_of_card_ge hRQ hRcardQ
  have hintersection : M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
    rw [r.partner_eq_centralizer]
    exact h.seed_centralizer_eq r.full
  let A := M ⊓ Mc
  let C := M ⊓ centralizer (V : Set G)
  have hCA : C ≤ A := by
    change C ≤ M ⊓ Mc
    rw [hintersection]
    exact le_sup_left
  have hTA : (T : Subgroup G) ≤ A := by
    change (T : Subgroup G) ≤ M ⊓ Mc
    rw [hintersection]
    exact le_sup_right
  have hAC : A ≤ normalizer (C : Set G) :=
    inf_le_left.trans ((le_inf M.le_normalizer
      (h.prepared.normalized.trans (normalizer_le_normalizer_centralizer V))).trans
        inf_normalizer_le_normalizer_inf)
  let : (C.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hAC
  have hgen : C.subgroupOf A ⊔ (T : Subgroup G).subgroupOf A = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hCA,map_subgroupOf_eq_of_le hTA,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hintersection.symm
  have hquot : IsPGroup 2 (A ⧸ C.subgroupOf A) :=
    isPGroup_quotient_of_sup_eq_top _ _ T.isPGroup'.comap_subtype hgen
  have hQA : (Q : Subgroup G) ≤ A := hRQeq ▸ hRA
  have hcover := congrArg (Subgroup.map A.subtype)
    ((Q.subtype hQA).sup_eq_top_of_quotient_isPGroup (C.subgroupOf A) hquot)
  have hcover' : R ⊔ C = A := by
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hQA,
      map_subgroupOf_eq_of_le hCA,←MonoidHom.range_eq_map,range_subtype,←hRQeq] at hcover
    exact hcover
  apply r.sylow_not_le_escape hI
  exact hTA.trans (hcover' ▸ sup_le hRI (inf_le_right.trans (r.module_centralizer_le_escape hI)))

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry

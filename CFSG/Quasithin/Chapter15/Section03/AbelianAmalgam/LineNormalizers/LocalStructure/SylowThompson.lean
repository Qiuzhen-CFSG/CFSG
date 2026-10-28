module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.Definitions
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Stellmacher.ElementaryAbelianMaxJMap
public import Theory.GroupTheory.SylowNormalizerFrattini
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Sylow restriction and the original Thompson product

The kernel identity from 15.3.66(5) identifies `O₂(Y_E T_E)` with `C_T(E)`
once `T_E` is Sylow in the original `G_E`. Normality of `C_G(E)` gives its
Sylow intersection. The actual maximum elementary family then gives
`J(T_E) = J(C_T(E)) ≤ J(C_G(E))` when `J(T_E)` centralizes `E`.

For `I = J(C_G(E))`, intersecting a Sylow subgroup of `G_E` with `I`
produces an intermediate subgroup with the same Thompson subgroup as `T_E`.
Frattini and the control of `N_G(J(T_E))` give `G_E = I M_E`. Hence the
selected escaping line forces `I` and its image modulo `Q_E` to be nontrivial.
The local calculation that controls the Thompson subgroup and its normalizer
remains an explicit prerequisite. No arbitrary stable-family saturation is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 15.3.67, printed p.1153, PDF p.1170, before the temporary replacement.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem restrict_sylow_image (A H S : Subgroup G)
    (hAH : A ≤ H) (hSA : S ≤ A)
    (U : Sylow 2 H) (hU : (U : Subgroup H).map H.subtype = S) :
    ∃ P : Sylow 2 A, (P : Subgroup A).map A.subtype = S := by
  let f : A →* H := inclusion hAH
  have hUr : (U : Subgroup H) ≤ f.range := by
    intro x hx
    have hxS : (x : G) ∈ S := hU ▸ mem_map_of_mem H.subtype hx
    exact ⟨⟨x, hSA hxS⟩, rfl⟩
  let P := U.comapOfInjective f (inclusion_injective hAH) hUr
  have hmap : (P : Subgroup A).map f = (U : Subgroup H) := map_comap_eq_self hUr
  refine ⟨P, ?_⟩
  calc
    (P : Subgroup A).map A.subtype = ((P : Subgroup A).map f).map H.subtype := by
      rw [map_map]
      rfl
    _ = S := by rw [hmap, hU]

private theorem normal_intersection_sylow_image (C H S : Subgroup G)
    (hCH : C ≤ H) (hC : (C.subgroupOf H).Normal)
    (U : Sylow 2 H) (hU : (U : Subgroup H).map H.subtype = S) :
    ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = S ⊓ C := by
  let C' := C.subgroupOf H
  let : C'.Normal := hC
  obtain ⟨Q, hQ⟩ := U.exists_sylow_map_eq_inf_of_normal C'
  let e : C' ≃* C := subgroupOfEquivOfLe hCH
  let P := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨P, ?_⟩
  calc
    (P : Subgroup C).map C.subtype = ((Q : Subgroup C').map C'.subtype).map H.subtype := by
      change ((Q : Subgroup C').map e.toMonoidHom).map C.subtype = _
      rw [map_map, map_map]
      rfl
    _ = S ⊓ C := by
      rw [hQ, map_inf _ _ _ H.subtype_injective, hU, map_subgroupOf_eq_of_le hCH]

omit [Finite G] in
/-- The kernel equality in 15.3.66(5) identifies the two-core with `C_T(E)`. -/
theorem lineS_eq_centralizer (Y T E : Subgroup G)
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hkernel : lineS Y T E = (lineY Y E ⊔ lineT T E) ⊓ lineC E) :
    lineS Y T E = T ⊓ lineC E := by
  have hAH : lineY Y E ⊔ lineT T E ≤ lineNormalizer E :=
    sup_le ((lineY_le Y E).trans inf_le_right) inf_le_right
  obtain ⟨P, hP⟩ := restrict_sylow_image _ _ _ hAH le_sup_right U hU
  have hS : lineS Y T E ≤ lineT T E := by
    exact hP ▸ pCoreIn_le_sylow (lineY Y E ⊔ lineT T E) P
  apply le_antisymm
  · exact le_inf (hS.trans inf_le_left) (hkernel ▸ inf_le_right)
  · rw [hkernel]
    refine le_inf ?_ inf_le_right
    exact (le_inf inf_le_left
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))).trans le_sup_right

/-- The original line Sylow subgroup meets the normal centralizer in a Sylow subgroup. -/
theorem lineC_sylow (T E : Subgroup G)
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) :
    ∃ P : Sylow 2 (lineC E), (P : Subgroup (lineC E)).map (lineC E).subtype = T ⊓ lineC E := by
  obtain ⟨P, hP⟩ := normal_intersection_sylow_image (lineC E) (lineNormalizer E)
    (lineT T E) (Subgroup.centralizer_le_normalizer _) inferInstance U hU
  refine ⟨P, ?_⟩
  simpa only [lineT, inf_assoc, inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)] using hP

private theorem maxJ_eq_of_intermediate (S R : Subgroup G)
    (hJR : elementaryAbelianMaxJ S ≤ R) (hRS : R ≤ S) :
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ S := by
  have hs := elementaryAbelianMaxOrder_le_and_j_le_of_eq R S hRS
  have hl := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S R hJR
  have he := le_antisymm hs.1 hl.1
  exact le_antisymm (hs.2 he) (hl.2 he.symm)

/-- The specific maximum-family containment implies both Thompson equality and Baumann equality. Proving that containment is the separate local action calculation. -/
theorem thompson_baumann_of_centralizing (T V E : Subgroup G)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T) (hEV : E ≤ V)
    (hJ : elementaryAbelianMaxJ (lineT T E) ≤ lineR T V) :
    elementaryAbelianMaxJ (lineT T E) = elementaryAbelianMaxJ (lineR T V) ∧
      lineB T E = ChapterB.baumann (lineR T V) ∧ lineB T E ≤ lineR T V := by
  have hCN : centralizer (V : Set G) ≤ lineNormalizer E :=
    (centralizer_le hEV).trans (Subgroup.centralizer_le_normalizer _)
  have hR : lineR T V ≤ lineT T E := le_inf inf_le_left (inf_le_right.trans hCN)
  have hVTE : V ≤ lineT T E := le_inf hVT (V.le_centralizer.trans hCN)
  have he : lineT T E ⊓ centralizer (V : Set G) = lineR T V := by
    exact le_antisymm (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf hR inf_le_right)
  have hB : lineB T E = ChapterB.baumann (lineR T V) := by
    exact (ChapterB.lemma_B_2_3_5 (lineT T E) V hVTE (hJ.trans inf_le_right)).trans
      (congrArg ChapterB.baumann he)
  exact ⟨(maxJ_eq_of_intermediate _ _ hJ hR).symm, hB, hB ▸ inf_le_left⟩

omit [Finite G] in
private theorem normalizer_maxJ (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (elementaryAbelianMaxJ_map_equiv (MulAut.conj g) S).symm.trans
    (congrArg elementaryAbelianMaxJ (mem_normalizer_iff_map_conj_eq.mp hg))

/-- Thompson heredity and Sylow conjugacy place `J(T_E)` in the published `I = J(C_E)`. -/
theorem lineT_maxJ_le_lineI (T E : Subgroup G)
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hJ : elementaryAbelianMaxJ (lineT T E) ≤ T ⊓ lineC E) :
    elementaryAbelianMaxJ (lineT T E) ≤ lineI E := by
  obtain ⟨P, hP⟩ := lineC_sylow T E U hU
  have hS : T ⊓ lineC E ≤ lineT T E :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  rw [← maxJ_eq_of_intermediate (lineT T E) (T ⊓ lineC E) hJ hS, ← hP,
    elementaryAbelianMaxJ_map_injective _ (lineC E).subtype_injective]
  have hm := map_mono (f := (lineC E).subtype) (elementaryAbelianMaxJ_sylow_le_top P)
  have he : elementaryAbelianMaxJ (lineC E) =
      (elementaryAbelianMaxJ (⊤ : Subgroup (lineC E))).map (lineC E).subtype := by
    rw [← elementaryAbelianMaxJ_map_injective _ (lineC E).subtype_injective,
      ← MonoidHom.range_eq_map, range_subtype]
  exact hm.trans he.ge

/-- Frattini inside the relatively normal `I` gives the original setwise product `G_E = I M_E`. -/
theorem lineI_product (M T E : Subgroup G)
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hJ : elementaryAbelianMaxJ (lineT T E) ≤ T ⊓ lineC E)
    (hN : normalizer (elementaryAbelianMaxJ (lineT T E) : Set G) ≤ M) :
    (lineNormalizer E : Set G) = (lineI E : Set G) * (lineM M E : Set G) := by
  let H := lineNormalizer E
  let I := (lineI E).subgroupOf H
  let : I.Normal := lineI_normal_in_lineNormalizer E
  obtain ⟨P, hP⟩ := U.exists_sylow_map_eq_inf_of_normal I
  let R := ((P : Subgroup I).map I.subtype).map H.subtype
  have hR : R = lineT T E ⊓ lineI E := by
    rw [show R = ((P : Subgroup I).map I.subtype).map H.subtype from rfl,
      hP, map_inf _ _ _ H.subtype_injective, hU,
      map_subgroupOf_eq_of_le (lineI_le_lineNormalizer E)]
  have hJR : elementaryAbelianMaxJ (lineT T E) ≤ R := by
    rw [hR]
    exact le_inf (sSup_le fun _ hA => hA.1) (lineT_maxJ_le_lineI T E U hU hJ)
  have hJeq := maxJ_eq_of_intermediate (lineT T E) R hJR (hR ▸ inf_le_left)
  have hNR : normalizer (R : Set G) ≤ M := by
    have hn := normalizer_maxJ R
    rw [hJeq] at hn
    exact hn.trans hN
  have hfr : I ⊔ normalizer ((P : Subgroup I).map I.subtype : Set H) = ⊤ := by
    rw [sup_comm]
    exact P.normalizer_sup_eq_top
  apply Set.Subset.antisymm
  · intro g hg
    have hg' : (⟨g, hg⟩ : H) ∈ I ⊔ normalizer ((P : Subgroup I).map I.subtype : Set H) :=
      hfr ▸ mem_top _
    obtain ⟨i, hi, n, hn, he⟩ := mem_sup_of_normal_left.mp hg'
    have hnR : (n : G) ∈ normalizer (R : Set G) :=
      ((P : Subgroup I).map I.subtype).le_normalizer_map H.subtype
        (mem_map_of_mem H.subtype hn)
    exact ⟨i, hi, n, ⟨hNR hnR, n.property⟩, congrArg Subtype.val he⟩
  · rintro g ⟨i, hi, m, hm, rfl⟩
    exact H.mul_mem (lineI_le_lineNormalizer E hi) hm.2

omit [Finite G] in
/-- An escaping line normalizer forces its Thompson factor to escape `M`. -/
theorem lineI_escapes (M E : Subgroup G)
    (hescape : ¬ lineNormalizer E ≤ M)
    (hprod : (lineNormalizer E : Set G) = (lineI E : Set G) * (lineM M E : Set G)) :
    ¬ lineI E ≤ M := by
  intro hI
  apply hescape
  intro g hg
  change g ∈ (lineNormalizer E : Set G) at hg
  rw [hprod] at hg
  obtain ⟨i, hi, m, hm, rfl⟩ := hg
  exact M.mul_mem (hI hi) hm.1

omit [Finite G] in
/-- Since the original two-core is contained in `T_E ≤ M`, the escaping Thompson factor has a nontrivial image modulo `Q_E`. -/
theorem lineI_image_ne_bot (M T E : Subgroup G) (hTM : T ≤ M)
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hI : ¬ lineI E ≤ M) :
    ((lineI E).subgroupOf (lineNormalizer E)).map
      (QuotientGroup.mk' (pCore 2 (lineNormalizer E))) ≠ ⊥ := by
  intro he
  have hIQ := (Subgroup.map_eq_bot_iff _).mp he
  apply hI
  intro x hx
  have hxQ := hIQ (show (⟨x, lineI_le_lineNormalizer E hx⟩ : lineNormalizer E) ∈
    (lineI E).subgroupOf (lineNormalizer E) from hx)
  have hxcore : x ∈ (lineNormalizer E).pCoreIn 2 :=
    mem_map_of_mem (lineNormalizer E).subtype ((QuotientGroup.ker_mk' _).le hxQ)
  have hcore : (lineNormalizer E).pCoreIn 2 ≤ lineT T E := hU ▸ pCoreIn_le_sylow _ U
  exact hTM (hcore hxcore).1

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure

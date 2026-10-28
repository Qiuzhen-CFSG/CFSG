module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Contracts
public import Theory.GroupTheory.CommonNormalSubgroup
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The elementary assembly of the local single-block index argument

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.5 and
C.5.7, printed pp.155 and 160; application E.6.14, printed p.251.

The conjugate closure of `U(L)` cannot lie in `O₂(H)`, since it would be
a nontrivial common normal subgroup. This selects a noncommuting conjugate.
Maximality of `N_A(L)` then kills the Frattini subgroup fixed by that
conjugator. The two `R`-invariant maximum elementary abelian subgroups of
`Baum(R)` form a genuine conjugation orbit, giving the required index.

The last theorem is conditional on the two precise local calculations in
`Contracts`. It does not discharge them or assert the source theorem.
In particular no SQTK hypothesis on the ambient group or on `A ⊔ H`
is inferred from the separate local SQTK hypotheses.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex

open Subgroup
universe u
variable {G : Type u} [Group G]
variable {K : GroupClass.{u}} {A H R L : Subgroup G}

private theorem conj_mul (B : Subgroup G) (a b : G) :
    B.map (MulAut.conj (a * b)).toMonoidHom =
      (B.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply, mul_assoc]

private theorem conj_one (B : Subgroup G) :
    B.map (MulAut.conj (1 : G)).toMonoidHom = B := by
  rw [map_one]
  exact B.map_id

private theorem map_symm_map (e : G ≃* G) (B : Subgroup G) :
    (B.map e.toMonoidHom).map e.symm.toMonoidHom = B := by
  rw [map_map]
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext g
    simp
  rw [he, map_id]

theorem Configuration.normalizes_S (h : Configuration K A H R L) :
    A ≤ normalizer (S R : Set G) :=
  h.normalizes_R.trans (Stellmacher.normalizer_le_normalizer_baumann R)

theorem Configuration.join_eq [Finite G] (h : Configuration K A H R L) : L ⊔ R = H := by
  obtain ⟨P, hP⟩ := h.sylow
  have he := congrArg (fun B : Subgroup H => B.map H.subtype)
    (pResidual_sup_sylow_eq_top P)
  rwa [Subgroup.map_sup, hP, h.residual, ← MonoidHom.range_eq_map, range_subtype] at he

theorem Configuration.normalizes_L (h : Configuration K A H R L) :
    H ≤ normalizer (L : Set G) := by
  rw [← h.residual]
  exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))

/-- The core commutator bound used in C.5.5. Normality in `H` places
`[O₂(H),L]` inside `O₂(L)`; two-perfection makes the commutator idempotent,
so it lies in the actual block module `[O₂(L),L]`. -/
theorem Configuration.commutator_le_module [Finite G] (h : Configuration K A H R L) :
    ⁅pCoreIn 2 H, L⁆ ≤ U L := by
  have hLH : L ≤ H := h.join_eq ▸ le_sup_left
  have hLP : L ≤ normalizer (pCoreIn 2 H : Set G) :=
    hLH.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hPL : pCoreIn 2 H ≤ normalizer (L : Set G) :=
    (pCoreIn_le 2 H).trans h.normalizes_L
  have hcL : ⁅pCoreIn 2 H, L⁆ ≤ L :=
    le_normalizer_iff_commutator_le_right.mp hPL
  have hcP : ⁅pCoreIn 2 H, L⁆ ≤ pCoreIn 2 H :=
    le_normalizer_iff_commutator_le_left.mp hLP
  have hcore : ⁅pCoreIn 2 H, L⁆ ≤ pCoreIn 2 L :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 H).to_le hcP) hcL
      (normalizer_commutator_ge_right _ _)
  have hi := commutator_isPPerfect_idempotent L (pCoreIn 2 H)
    h.block.chi.short.twoPerfect (isPGroup_pCoreIn 2 H) hLP
  rw [U, ChapterC.blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  exact hi.symm.le.trans (commutator_mono hcore le_rfl)

private theorem normalizes_D_of_normalizes_S_L {B : Subgroup G}
    (hS : B ≤ normalizer (S R : Set G)) (hL : B ≤ normalizer (L : Set G)) :
    B ≤ normalizer (D R L : Set G) :=
  (le_inf hS (hL.trans (normalizer_le_normalizer_centralizer L))).trans
    inf_normalizer_le_normalizer_inf

private theorem Configuration.normalizer_normalizes_Q (h : Configuration K A H R L) :
    localNormalizer A L ≤ normalizer (Q R L : Set G) := by
  have hs : localNormalizer A L ≤ normalizer ((L ⊔ S R : Subgroup G) : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans h.normalizes_S)).trans
      (normalizer_inf_normalizer_le_normalizer_sup L (S R))
  exact hs.trans (normalizer_le_normalizer_characteristic_image (L ⊔ S R)
    (pCore 2 (L ⊔ S R : Subgroup G)))

private theorem Configuration.normalizer_normalizes_F (h : Configuration K A H R L) :
    localNormalizer A L ≤ normalizer (F R L : Set G) :=
  (normalizes_D_of_normalizes_S_L (inf_le_left.trans h.normalizes_S) inf_le_right).trans
    (normalizer_le_normalizer_characteristic_image (D R L) (frattini (D R L)))

private theorem Configuration.H_normalizes_F [Finite G] (h : Configuration K A H R L) :
    H ≤ normalizer (F R L : Set G) := by
  have hr : R ≤ normalizer (D R L : Set G) :=
    normalizes_D_of_normalizes_S_L (h.le_A.trans h.normalizes_S)
      ((Chapter1.isSylowIn_iff.mp h.sylow).2.1.trans h.normalizes_L)
  have hl : L ≤ normalizer (D R L : Set G) :=
    (le_centralizer_iff.mpr (show D R L ≤ centralizer (L : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  rw [← h.join_eq]
  exact (sup_le hl hr).trans
    (normalizer_le_normalizer_characteristic_image (D R L) (frattini (D R L)))

private theorem Configuration.common_eq_bot (h : Configuration K A H R L)
    {N : Subgroup G} (hNR : N ≤ R)
    (hAN : A ≤ normalizer (N : Set G)) (hHN : H ≤ normalizer (N : Set G)) : N = ⊥ := by
  by_contra hne
  apply h.no_common
  refine ⟨N, hNR, hne, Chapter3.normalIn_iff_le_normalizer.mpr ?_⟩
  rw [Chapter3.generated_eq_sup]
  exact ⟨hNR.trans (h.le_A.trans le_sup_left), sup_le hAN hHN⟩

/-- The local pushing-up hypothesis used at the start of C.5.3. A
characteristic subgroup of `R` which is normal in `H` must be trivial.
This uses relative normality and does not require the join to be SQTK. -/
theorem Configuration.characteristic_eq_bot_of_normal_in_H
    (h : Configuration K A H R L) (C : Subgroup R) [C.Characteristic]
    (hCH : ((C.map R.subtype).subgroupOf H).Normal) : C = ⊥ := by
  have hCR : C.map R.subtype ≤ R := map_subtype_le C
  have hRH : R ≤ H := (Chapter1.isSylowIn_iff.mp h.sylow).2.1
  have hz := h.common_eq_bot hCR
    (h.normalizes_R.trans (normalizer_le_normalizer_characteristic_image R C))
    ((normal_subgroupOf_iff_le_normalizer (hCR.trans hRH)).mp hCH)
  exact (map_injective R.subtype_injective) (hz.trans (map_bot R.subtype).symm)

/-- C.5.5 in the local setting, together with selection of the noncommuting
conjugate used in C.5.6. Only the explicit Baumann calculations are pending. -/
theorem exists_noncommuting_conjugate [Finite G] (h : Configuration K A H R L)
    (hb : BaumannStructure H R L) :
    ∃ x ∈ A, ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G) := by
  let V : Subgroup G := ⨆ a : A, (U L).map (MulAut.conj (a : G)).toMonoidHom
  have hu : U L ≤ V := by
    have he := le_iSup (fun a : A => (U L).map (MulAut.conj (a : G)).toMonoidHom) 1
    simpa only [OneMemClass.coe_one, conj_one] using he
  have hur : U L ≤ R := hb.module_le.trans inf_le_left
  have hvR : V ≤ R := by
    apply iSup_le
    intro a
    have he := mem_normalizer_iff_map_conj_eq.mp (h.normalizes_R a.property)
    exact he ▸ map_mono hur
  have hAV : A ≤ normalizer (V : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha v hv
    have hm : V.map (MulAut.conj a).toMonoidHom ≤ V := by
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro b
      rw [← conj_mul]
      exact le_iSup_of_le (⟨a * b, A.mul_mem ha b.property⟩ : A) le_rfl
    exact hm (mem_map_of_mem (MulAut.conj a).toMonoidHom hv)
  have hu_ne : U L ≠ ⊥ := by
    intro he
    have hi := (map_injective L.subtype_injective) (he.trans (map_bot L.subtype).symm)
    exact h.block.chi.short.blockU_ne_bot hi
  have hescape : ¬ V ≤ pCoreIn 2 H := by
    apply not_le_of_no_common_normal_subgroup A H L R (pCoreIn 2 H) (U L) V
      (h.join_eq ▸ sup_le le_sup_left (h.le_A.trans le_sup_right))
      (h.le_A.trans le_sup_left) _ hu hu_ne hvR hAV h.commutator_le_module
    intro N hNR hN
    apply h.common_eq_bot hNR
    · exact le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer
        (hNR.trans (h.le_A.trans le_sup_left))).mp hN)
    · exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
        (hNR.trans (h.le_A.trans le_sup_left))).mp hN)
  by_contra he
  push Not at he
  apply hescape
  apply iSup_le
  intro a
  exact (le_inf ((le_iSup _ a).trans hvR) (he a a.property)).trans hb.centralizer_le

private theorem outside_normalizer_of_noncommuting (h : Configuration K A H R L)
    (hb : BaumannStructure H R L) {x : G}
    (hnc : ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G)) :
    x ∉ localNormalizer A L := by
  intro hn
  have he := mem_normalizer_iff_map_conj_eq.mp (h.normalizer_normalizes_Q hn)
  have huq : U L ≤ Q R L := by
    rw [hb.core_eq]
    refine le_inf hb.module_le ?_
    have hel := h.block.chi.short.elementary.map L.subtype
    let : IsElementaryAbelian 2 (U L) := hel
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact hnc ((he ▸ map_mono huq).trans (hb.core_eq ▸ inf_le_right))

/-- The first paragraph of C.5.7: maximality and the common-normal
exclusion kill `Φ(C_S(L))` once C.5.6(4) supplies its invariance. -/
theorem frattini_eq_bot [Finite G] (h : Configuration K A H R L)
    (hb : BaumannStructure H R L) {x : G} (hx : x ∈ A)
    (hnc : ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G))
    (hf : (F R L).map (MulAut.conj x).toMonoidHom = F R L) : F R L = ⊥ := by
  have hcontain : localNormalizer A L ≤ localNormalizer A (F R L) :=
    le_inf inf_le_left h.normalizer_normalizes_F
  have hfix : x ∈ localNormalizer A (F R L) :=
    ⟨hx, mem_normalizer_iff_map_conj_eq.mpr hf⟩
  have hA : localNormalizer A (F R L) = A := by
    rcases h.maximal.eq_or_eq hcontain inf_le_left with he | he
    · exact False.elim (outside_normalizer_of_noncommuting h hb hnc (he ▸ hfix))
    · exact he
  exact h.common_eq_bot ((map_subtype_le _).trans (inf_le_left.trans inf_le_left))
    (hA ▸ inf_le_right) h.H_normalizes_F

private theorem invariantFamily_map {B E : Subgroup G} (e : G ≃* G)
    (hR : R.map e.toMonoidHom = R) (hB : B.map e.toMonoidHom = B)
    (hE : E ∈ invariantFamily R B) : E.map e.toMonoidHom ∈ invariantFamily R B := by
  refine ⟨⟨hB ▸ map_mono hE.1.1, hE.1.2.1.map e.toMonoidHom, ?_⟩, ?_⟩
  · intro Y hY hYe
    have hback : Y.map e.symm.toMonoidHom ≤ B := by
      have hm := map_mono (f := e.symm.toMonoidHom) hY
      have he : B.map e.symm.toMonoidHom = B := by
        calc
          B.map e.symm.toMonoidHom = (B.map e.toMonoidHom).map e.symm.toMonoidHom :=
            congrArg (fun Y : Subgroup G => Y.map e.symm.toMonoidHom) hB.symm
          _ = B := map_symm_map e B
      rwa [he] at hm
    have hc := hE.1.2.2 _ hback (hYe.map e.symm.toMonoidHom)
    simpa only [card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective,
      card_map_of_injective (f := e.toMonoidHom) e.injective] using hc
  · rw [← map_equiv_normalizer_eq]
    exact hR ▸ map_mono hE.2

private theorem index_two_of_pair (h : Configuration K A H R L)
    {B : Subgroup G} (hne : Q R L ≠ B)
    (hpair : invariantFamily R (S R) = {Q R L, B})
    {x : G} (hx : x ∈ A) (hmove : (Q R L).map (MulAut.conj x).toMonoidHom = B) :
    (localNormalizer A L).relIndex A = 2 := by
  have hq : Q R L ∈ invariantFamily R (S R) := by rw [hpair]; simp
  have himages (a : G) (ha : a ∈ A) :
      (Q R L).map (MulAut.conj a).toMonoidHom = Q R L ∨
      (Q R L).map (MulAut.conj a).toMonoidHom = B := by
    have hi := invariantFamily_map (MulAut.conj a)
      (mem_normalizer_iff_map_conj_eq.mp (h.normalizes_R ha))
      (mem_normalizer_iff_map_conj_eq.mp (h.normalizes_S ha)) hq
    simpa only [hpair, Set.mem_insert_iff, Set.mem_singleton_iff] using hi
  have hout : x ∉ localNormalizer A (Q R L) := by
    intro hn
    exact hne ((mem_normalizer_iff_map_conj_eq.mp hn.2).symm.trans hmove)
  have hnormalizer : localNormalizer A L = localNormalizer A (Q R L) := by
    rcases h.maximal.eq_or_eq (le_inf inf_le_left h.normalizer_normalizes_Q) inf_le_left with he | he
    · exact he.symm
    · exact False.elim (hout (he.ge hx))
  rw [hnormalizer]
  have hback := (himages x⁻¹ (A.inv_mem hx)).resolve_left (by
    intro he
    apply hout
    exact ⟨hx, (normalizer (Q R L : Set G)).inv_mem_iff.mp
      (mem_normalizer_iff_map_conj_eq.mpr he)⟩)
  have hswap : B.map (MulAut.conj x).toMonoidHom = Q R L := by
    rw [← hback, ← conj_mul, mul_inv_cancel, conj_one]
  apply relIndex_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨x, hx, hout, ?_⟩
  intro a ha
  rcases himages a ha with he | he
  · exact Or.inr ⟨ha, mem_normalizer_iff_map_conj_eq.mpr he⟩
  · refine Or.inl ⟨A.mul_mem hx ha, mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    change (Q R L).map (MulAut.conj (x * a)).toMonoidHom = Q R L
    rw [conj_mul, he, hswap]

/-- Conditional local C.5.7 assembly. Both local structural inputs still
have to be proved; the source theorem is not complete until then. -/
theorem singleBlockIndexInput_of_local_calculations
    [Finite G]
    (hb : BaumannInput (G := G) K) (hc : ConjugateInput (G := G) K) :
    SingleBlockIndexInput (G := G) K := by
  intro A H R L hA hH hchar hSyl huniq hRA hAR hno hres hblock hmax
  let h : Configuration K A H R L :=
    ⟨hA, hH, hchar, hSyl, huniq, hRA, hAR, hno, hres, hblock, hmax⟩
  have hs := hb A H R L h
  obtain ⟨x, hx, hnc⟩ := exists_noncommuting_conjugate h hs
  obtain ⟨hf, hpair⟩ := hc A H R L h hs x hx hnc
  have hzero := frattini_eq_bot h hs hx hnc hf
  have hne : Q R L ≠ (Q R L).map (MulAut.conj x).toMonoidHom := by
    intro he
    have huq : U L ≤ Q R L := by
      rw [hs.core_eq]
      have hel := hblock.chi.short.elementary.map L.subtype
      let : IsElementaryAbelian 2 (U L) := hel
      exact le_inf hs.module_le (le_centralizer_iff_isMulCommutative.mpr inferInstance)
    exact hnc ((he.symm ▸ map_mono huq).trans (hs.core_eq ▸ inf_le_right))
  exact index_two_of_pair h hne (hpair hzero) hx rfl

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex

end

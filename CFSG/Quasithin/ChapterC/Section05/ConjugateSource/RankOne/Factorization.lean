module

public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Indices
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Pair

/-!
# Counting and residual lifting in C.5.6(1),(2)

The action index first gives `S = Uˣ Q`. For a conjugate pair generating
modulo `Q`, normality and two-perfection remove `Q`. The intersection of
their centralizers in `Q` has index at most `q²`, while the actual module
quotient gives the reverse bound for `C_Q(L)`. Equality forces that
intersection to be `D`, and then `Q = U D` with `D` centralizing `Uˣ`.

The final theorem supplies both the natural action indices and quotient
generating pair from the preceding marked C.5.4 data. Relative normality
uses only S-normality of the two modules; the whole Sylow group need not
preserve the selected block.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.6(1),(2),
printed pp.156–157 (PDF pp.167–168).
-/

public section

open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem join_index (B C : Subgroup G)
    (hn : C ≤ normalizer (B : Set G)) : B.relIndex (C ⊔ B) = B.relIndex C := by
  let T := C ⊔ B
  let : (B.subgroupOf T).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le hn B.le_normalizer)
  have hi := relIndex_sup_right (C.subgroupOf T) (B.subgroupOf T)
  rw [← subgroupOf_sup le_sup_left le_sup_right,
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf le_sup_left] at hi
  exact hi

private theorem equal_of_index (B C T : Subgroup G) (hBC : B ≤ C) (hCT : C ≤ T)
    (hi : B.relIndex T ≤ C.relIndex T) : B = C := by
  have ht := relIndex_mul_relIndex B C T hBC hCT
  have hc : 0 < C.relIndex T := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hb : 0 < B.relIndex C := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have he : B.relIndex C = 1 := by nlinarith
  exact le_antisymm hBC (relIndex_eq_one.mp he)

private theorem span_of_index (B C T : Subgroup G) (hBT : B ≤ T) (hCT : C ≤ T)
    (hn : C ≤ normalizer (B : Set G)) (hi : B.relIndex C = B.relIndex T) :
    T = C ⊔ B := by
  have ht := relIndex_mul_relIndex B (C ⊔ B) T le_sup_right (sup_le hCT hBT)
  rw [join_index B C hn, hi] at ht
  have hp : 0 < B.relIndex T := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have he : (C ⊔ B).relIndex T = 1 := by nlinarith
  exact le_antisymm (relIndex_eq_one.mp he) (sup_le hCT hBT)

omit [Finite G] in
private theorem map_centralizer (B : Subgroup G) (e : G ≃* G) :
    (centralizer (B : Set G)).map e.toMonoidHom =
      centralizer (B.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro g hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hg (e y) (mem_map_of_mem _ hy)

omit [Finite G] in
private theorem inter_index (B C T : Subgroup G) (ht : T ≤ B) :
    (B ⊓ C).relIndex T = C.relIndex T := by
  have he : (B ⊓ C).subgroupOf T = C.subgroupOf T := by
    ext t
    exact ⟨And.right, fun h => ⟨ht t.property, h⟩⟩
  exact congrArg Subgroup.index he

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {R L : Subgroup G} {x : G} {F : Type*} [Field F]

structure Factorization (R L : Subgroup G) (x : G) : Prop where
  core : Q R L = U L ⊔ D R L
  centralizes : D R L ≤ centralizer ((U L).map (MulAut.conj x⁻¹).toMonoidHom : Set G)
  span : S R = (U L).map (MulAut.conj x⁻¹).toMonoidHom ⊔ Q R L

omit [Finite G] in
/-- The actual two-core is normal in S. -/
theorem S_normalizes_Q (R L : Subgroup G) : S R ≤ normalizer (Q R L : Set G) :=
  (le_sup_right : S R ≤ L ⊔ S R).trans ((L ⊔ S R).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (L ⊔ S R) (pCore 2 (L ⊔ S R : Subgroup G))))

omit [Finite G] in
/-- The normalizer of the Baumann group carries `U` back into it. -/
theorem conjugate_le_S (h : Setup R L F)
    (hx : x ∈ normalizer (R : Set G)) : (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ S R := by
  have hs : (S R).map (MulAut.conj x⁻¹).toMonoidHom = S R :=
    h.stable hx
  exact hs ▸ map_mono h.module_le

/-- Equality of the action indices forces the first product decomposition. -/
theorem span_of_actionIndices (h : Setup R L F) (hx : x ∈ normalizer (R : Set G)) {q : ℕ}
    (hi : ActionIndices R L x q) :
    S R = (U L).map (MulAut.conj x⁻¹).toMonoidHom ⊔ Q R L := by
  have hv := conjugate_le_S h hx
  apply span_of_index (Q R L) _ (S R) (h.core ▸ inf_le_left) hv
    (hv.trans (S_normalizes_Q R L))
  rw [h.core]
  rw [inter_index _ _ _ hv, inf_relIndex_left]
  exact hi.conjugate.trans hi.actor.symm

omit [Finite G] in
private theorem perfect_le_of_join (B P T : Subgroup G)
    (hB : IsPPerfect 2 B) (hT : IsPGroup 2 T)
    (hn : T ≤ normalizer (P : Set G)) (hb : B ≤ P ⊔ T) : B ≤ P := by
  let J := P ⊔ T
  let : (P.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hn)
  have hg : P.subgroupOf J ⊔ T.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self _
  have hq := isPGroup_quotient_of_sup_eq_top (P.subgroupOf J) (T.subgroupOf J)
    hT.comap_subtype hg
  have hp : pResidual 2 J ≤ P.subgroupOf J := sInf_le ⟨inferInstance, hq⟩
  have hr := le_pResidual_of_isPPerfect (B.subgroupOf J)
    (hB.of_surjective (subgroupOfEquivOfLe hb).symm.toMonoidHom
      (subgroupOfEquivOfLe hb).symm.surjective)
  intro b hb'
  exact hp (hr (show (⟨b, hb hb'⟩ : J) ∈ B.subgroupOf J from hb'))

omit [Finite G] in
/-- The block preserves the actual two-core of `LS`. -/
theorem L_normalizes_Q (R L : Subgroup G) : L ≤ normalizer (Q R L : Set G) :=
  (le_sup_left : L ≤ L ⊔ S R).trans ((L ⊔ S R).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (L ⊔ S R)
      (pCore 2 (L ⊔ S R : Subgroup G))))

omit [Finite G] in
/-- The two-core preserves the conjugate module inside the Baumann group. -/
theorem Q_normalizes_conjugate (h : Setup R L F) (hx : x ∈ normalizer (R : Set G)) :
    Q R L ≤ normalizer ((U L).map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
  exact (h.core ▸ inf_le_left).trans (h.conjugate_normalized hx)

omit [Finite G] in
/-- Relative normality and two-perfection lift generation modulo the two-core. -/
theorem lift_generating_pair (h : Setup R L F) (hx : x ∈ normalizer (R : Set G)) {y : G} (hy : y ∈ L)
    (hgen : L ≤ ((U L).map (MulAut.conj x⁻¹).toMonoidHom ⊔
      ((U L).map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom) ⊔ Q R L) :
    L ≤ (U L).map (MulAut.conj x⁻¹).toMonoidHom ⊔
      ((U L).map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
  let V := (U L).map (MulAut.conj x⁻¹).toMonoidHom
  have hn := Q_normalizes_conjugate h hx
  have hQy : (Q R L).map (MulAut.conj y).toMonoidHom = Q R L :=
    mem_normalizer_iff_map_conj_eq.mp (L_normalizes_Q R L hy)
  have hn' : Q R L ≤ normalizer (V.map (MulAut.conj y).toMonoidHom : Set G) := by
    rw [← map_equiv_normalizer_eq, ← hQy]
    exact map_mono hn
  exact perfect_le_of_join L _ (Q R L) h.short.twoPerfect
    (isPGroup_pCoreIn 2 (L ⊔ S R))
    ((le_inf hn hn').trans (normalizer_inf_normalizer_le_normalizer_sup _ _)) hgen

/-- The intersection-index argument deriving all three factorizations. -/
theorem factorization_of_actionIndices_and_pair
    (h : Setup R L F)
    (hx : x ∈ normalizer (R : Set G)) {q : ℕ} (hi : ActionIndices R L x q)
    (hpair : ∃ y ∈ L, L ≤ (U L).map (MulAut.conj x⁻¹).toMonoidHom ⊔
      ((U L).map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom) :
    Factorization R L x := by
  let V := (U L).map (MulAut.conj x⁻¹).toMonoidHom
  obtain ⟨y, hy, hgen⟩ := hpair
  let W := V.map (MulAut.conj y).toMonoidHom
  let I := Q R L ⊓ (centralizer (V : Set G) ⊓ centralizer (W : Set G))
  have hUS := h.module_le
  have hUQ := h.module_le_core
  have hQS : Q R L ≤ S R := h.core ▸ inf_le_left
  have hUL : U L ≤ L := map_subtype_le _
  have hDQ : D R L ≤ Q R L := by
    rw [h.core]
    exact le_inf inf_le_left (inf_le_right.trans (centralizer_le hUL))
  have hDI : I ≤ D R L := by
    have hc : centralizer (V : Set G) ⊓ centralizer (W : Set G) ≤
        centralizer (L : Set G) := by
      apply le_centralizer_iff.mpr
      apply hgen.trans
      apply sup_le
      · exact le_centralizer_iff.mp inf_le_left
      · exact le_centralizer_iff.mp inf_le_right
    exact le_inf (inf_le_left.trans hQS) (inf_le_right.trans hc)
  have hvS : (centralizer (V : Set G)).relIndex (S R) = q := by
    have hs : (S R).map (MulAut.conj x⁻¹).toMonoidHom = S R :=
      h.stable hx
    rw [← map_centralizer (U L) (MulAut.conj x⁻¹), ← hs,
      relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hi.actor
  have hvQ : (centralizer (V : Set G)).relIndex (Q R L) ≤ q := by
    rw [← hvS]
    exact relIndex_le_of_le_right hQS index_ne_zero_of_finite
  have hQy : (Q R L).map (MulAut.conj y).toMonoidHom = Q R L := by
    apply mem_normalizer_iff_map_conj_eq.mp
    exact L_normalizes_Q R L hy
  have hwQ : (centralizer (W : Set G)).relIndex (Q R L) ≤ q := by
    rw [show W = V.map (MulAut.conj y).toMonoidHom from rfl,
      ← map_centralizer V (MulAut.conj y), ← hQy,
      relIndex_map_map_of_injective _ _ (MulAut.conj y).injective]
    exact hvQ
  have hiQ : I.relIndex (Q R L) ≤ q * q := by
    change (Q R L ⊓ _).relIndex (Q R L) ≤ _
    rw [inf_relIndex_left]
    exact relIndex_inf_le.trans (Nat.mul_le_mul hvQ hwQ)
  have hDU : (D R L).relIndex (U L) = q * q := by
    rw [D, inter_index _ _ _ hUS]
    exact hi.module
  have hDlow : q * q ≤ (D R L).relIndex (Q R L) := by
    rw [← hDU]
    exact relIndex_le_of_le_right hUQ index_ne_zero_of_finite
  have hID : I = D R L :=
    equal_of_index I (D R L) (Q R L) hDI hDQ (hiQ.trans hDlow)
  have hDindex : (D R L).relIndex (Q R L) = q * q :=
    le_antisymm (hID ▸ hiQ) hDlow
  refine ⟨?_, ?_, span_of_actionIndices h hx hi⟩
  · apply span_of_index (D R L) (U L) (Q R L) hDQ hUQ
    · exact (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le hUL))).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact hDU.trans hDindex.symm
  · exact hID ▸ (inf_le_right.trans inf_le_left : I ≤ centralizer (V : Set G))

/-- C.5.6(1) and the first spanning equality in (2), with both the
natural indices and quotient pair-generation discharged. -/
theorem Setup.factorization (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    Factorization R L x := by
  have hi := h.indices hx hnc
  obtain ⟨y, hy, hgen⟩ := h.quotient_pair (span_of_actionIndices h hx hi)
  exact factorization_of_actionIndices_and_pair h hx hi
    ⟨y, hy, lift_generating_pair h hx hy hgen⟩

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end

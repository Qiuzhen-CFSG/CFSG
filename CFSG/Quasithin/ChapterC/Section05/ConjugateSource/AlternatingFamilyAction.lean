module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFamily

/-!
# The genuine action on the four maximum elementary subgroups

The inner Sylow exchange r lies in R∩K outside Baum(R) and swaps the two
transposition images. It therefore swaps the two extra members of the proved
four-family. When R normalizes K, precisely the two conjugate cores are
R-invariant, and every R-normalizer preserves that pair. The core span then
identifies Baum(R) with the elementary Thompson subgroup of R.

The final family uses the source right-conjugate convention Aʳ=r⁻¹Ar and
proves the index-two intersection assertion for the extra member.
Source: Aschbacher–Smith, C.5.6(5),(7)(ii) and C.5.7, printed pp.158–160.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

omit [Finite G] in
private theorem core_image (h : AlternatingPairSetup R K L) :
    actionImage h.action ((K ⊔ ChapterB.baumann R).pCoreIn 2) = ⊥ := by
  unfold actionImage
  rw [Subgroup.map_eq_bot_iff]
  intro q hq
  rw [h.action_kernel]
  exact (h.core ▸ hq).2

private theorem opposite_image (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    actionImage h.action ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ⊔
      (ChapterB.baumann R ⊓ centralizer (K : Set G))) = ChapterB.Offenders.D 5 := by
  let S := ChapterB.baumann R
  have hSn := normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx)
  have hVS : (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ S :=
    (map_mono h.module_le).trans_eq (mem_normalizer_iff_map_conj_eq.mp hSn)
  rw [actionImage_sup h.action (hVS.trans le_sup_right) (inf_le_left.trans le_sup_right)]
  have hD : actionImage h.action (S ⊓ centralizer (K : Set G)) = ⊥ := by
    apply le_bot_iff.mp
    exact (actionImage_mono h.action (h.product ▸ le_sup_right)).trans (core_image h).le
  rw [hD, sup_bot_eq]
  exact h.conjugate_action_image x hx hnc

private theorem exists_exchange (h : AlternatingPairSetup R K L) :
    ∃ r : (K ⊔ ChapterB.baumann R : Subgroup G),
      (r : G) ∈ R ⊓ K ∧ (r : G) ∉ ChapterB.baumann R ∧ h.action r = exchange := by
  obtain ⟨r, hr, he⟩ := h.pairExchange_mem
  change h.action r = exchange at he
  refine ⟨r, hr, ?_, he⟩
  intro hs
  apply exchange_not_mem_actor
  rw [← he, ← h.baumann_image]
  exact mem_map_of_mem h.action hs

theorem AlternatingPairSetup.family_exchange
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hphi : let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
      (frattini D).map D.subtype = ⊥) :
    let S := ChapterB.baumann R
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := (K ⊔ S).pCoreIn 2
    let D := S ⊓ centralizer (K : Set G)
    ∃ B : Subgroup G, ∃ r : G,
      r ∈ R ⊓ K ∧ r ∉ S ∧
      elementaryAbelianMaxSubgroups R = {Q, V ⊔ D, B, B.map (MulAut.conj r).toMonoidHom} ∧
      actionImage h.action B = line 0 ∧
      ¬ R ≤ normalizer (B : Set G) ∧
      ¬ R ≤ normalizer (B.map (MulAut.conj r).toMonoidHom : Set G) := by
  let S := ChapterB.baumann R
  let Q := (K ⊔ S).pCoreIn 2
  let W := (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ⊔ (S ⊓ centralizer (K : Set G))
  obtain ⟨B₀, B₁, hfamily, h0, h1⟩ := h.family_eq_four x hx hnc hphi
  change actionImage h.action B₀ = line 0 at h0
  change actionImage h.action B₁ = line 1 at h1
  obtain ⟨r, hr, hrS, he⟩ := exists_exchange h
  have hb0 : B₀ ∈ elementaryAbelianMaxSubgroups R := by rw [hfamily]; simp
  have hb1 : B₁ ∈ elementaryAbelianMaxSubgroups R := by rw [hfamily]; simp
  have h0N : B₀ ≤ K ⊔ S :=
    ((baumann_maxFamily R ▸ hb0).1).trans le_sup_right
  have h1N : B₁ ≤ K ⊔ S :=
    ((baumann_maxFamily R ▸ hb1).1).trans le_sup_right
  have h0move := moved_of_line_zero h.action h0N h0 r he
  have h1move := moved_of_line_one h.action h1N h1 r he
  have hrR : R.map (MulAut.conj (r : G)).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (R.le_normalizer hr.1)
  have hbr : B₀.map (MulAut.conj (r : G)).toMonoidHom ∈ elementaryAbelianMaxSubgroups R := by
    have hh := (maxFamily_map_injective_iff (MulAut.conj (r : G)).toMonoidHom (MulAut.conj (r : G)).injective R B₀).mpr hb0
    simpa only [hrR] using hh
  have hrimage : actionImage h.action (B₀.map (MulAut.conj (r : G)).toMonoidHom) = line 1 := by
    rw [actionImage_conj h.action h0N r, h0, he, exchange_line_zero]
  have hBr : B₀.map (MulAut.conj (r : G)).toMonoidHom = B₁ := by
    rw [hfamily] at hbr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbr
    rcases hbr with hc | hw | hb | hb
    · have hc' := congrArg (actionImage h.action) hc
      rw [hrimage, core_image h] at hc'
      exact False.elim (line_ne_bot 1 hc')
    · have hw' := congrArg (actionImage h.action) hw
      rw [hrimage, opposite_image h x hx hnc] at hw'
      have hh := congrArg (fun A : Subgroup FivePerm => Nat.card A) hw'
      rw [Enumeration.line_card, Enumeration.actor_card] at hh
      omega
    · exact False.elim (h0move hb.symm)
    · exact hb
  refine ⟨B₀, r, hr, hrS, ?_, h0, ?_, ?_⟩
  · rw [hBr]
    exact hfamily
  · intro hn
    exact h0move (mem_normalizer_iff_map_conj_eq.mp (hn hr.1)).symm
  · rw [hBr]
    intro hn
    exact h1move (mem_normalizer_iff_map_conj_eq.mp (hn hr.1)).symm
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup Stellmacher
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.family_structure
    (h : AlternatingPairSetup R K L) (hRK : R ≤ normalizer (K : Set G))
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hphi : let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
      (frattini D).map D.subtype = ⊥) :
    let S := ChapterB.baumann R
    let Q := (K ⊔ S).pCoreIn 2
    (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ⊔
        (S ⊓ centralizer (K : Set G)) = Q.map (MulAut.conj x⁻¹).toMonoidHom ∧
    {B ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (B : Set G)} =
      {Q, Q.map (MulAut.conj x⁻¹).toMonoidHom} := by
  let S := ChapterB.baumann R
  let Q := (K ⊔ S).pCoreIn 2
  let e := MulAut.conj x⁻¹
  let Q' := Q.map e.toMonoidHom
  let W := (sourceModule K).map e.toMonoidHom ⊔ (S ⊓ centralizer (K : Set G))
  obtain ⟨B, r, _, _, hf, _, hnB, hnBr⟩ := h.family_exchange x hx hnc hphi
  have hRQ : R ≤ normalizer (Q : Set G) := by
    have hRN : R ≤ normalizer ((K ⊔ S : Subgroup G) : Set G) :=
      (le_inf hRK (R.le_normalizer.trans (normalizer_le_normalizer_baumann R))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact hRN.trans (normalizer_le_normalizer_characteristic_image (K ⊔ S) (pCore 2 (K ⊔ S : Subgroup G)))
  have heR : R.map e.toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hx)
  have hRQ' : R ≤ normalizer (Q' : Set G) := by
    rw [← heR]
    exact (map_mono hRQ).trans (le_normalizer_map e.toMonoidHom)
  have hQmem : Q ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; exact Set.mem_insert _ _
  have hQ'mem : Q' ∈ elementaryAbelianMaxSubgroups R := by
    have hh := (maxFamily_map_injective_iff e.toMonoidHom e.injective R Q).mpr hQmem
    rwa [heR] at hh
  have hQ'ne : Q' ≠ Q := by
    intro he
    have hUQ : sourceModule K ≤ Q := le_sup_left.trans_eq h.product.symm
    exact hnc (((map_mono (f := e.toMonoidHom) hUQ).trans_eq he).trans
      (h.core.le.trans inf_le_right))
  have hQ'W : Q' = W := by
    have hh := hQ'mem
    rw [hf] at hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with he | he | he | he
    · exact (hQ'ne he).elim
    · exact he
    · exact (hnB (he ▸ hRQ')).elim
    · exact (hnBr (he ▸ hRQ')).elim
  refine ⟨hQ'W.symm, ?_⟩
  ext A
  constructor
  · rintro ⟨hA, hnA⟩
    rw [hf] at hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA ⊢
    rcases hA with he | he | he | he
    · exact Or.inl he
    · exact Or.inr (he.trans hQ'W.symm)
    · exact (hnB (he ▸ hnA)).elim
    · exact (hnBr (he ▸ hnA)).elim
  · intro hA
    rcases Set.mem_insert_iff.mp hA with rfl | he
    · exact ⟨hQmem, hRQ⟩
    · have he := Set.mem_singleton_iff.mp he
      subst A
      exact ⟨hQ'mem, hRQ'⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup Stellmacher
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.extra_family_index
    (h : AlternatingPairSetup R K L) (B : Subgroup G)
    (hB : B ∈ elementaryAbelianMaxSubgroups R)
    (himage : actionImage h.action B = line 0) :
    ((K ⊔ ChapterB.baumann R).pCoreIn 2).relIndex B = 2 := by
  let S := ChapterB.baumann R
  have hBS : B ≤ S := (baumann_maxFamily R ▸ hB).1
  have hi := relIndex_ker (B.subgroupOf (K ⊔ S)) h.action
  rw [h.action_kernel, relIndex_subgroupOf (hBS.trans le_sup_right)] at hi
  change (centralizer (sourceModule K : Set G)).relIndex B = Nat.card (actionImage h.action B) at hi
  rw [himage, Enumeration.line_card] at hi
  rw [h.core, inf_comm (ChapterB.baumann R), ← relIndex_inf_mul_relIndex,
    inf_of_le_right hBS, relIndex_eq_one.mpr hBS, mul_one]
  exact hi
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.baumann_eq_maxJ
    (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hphi : let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
      (frattini D).map D.subtype = ⊥) :
    ChapterB.baumann R = elementaryAbelianMaxJ R := by
  let S := ChapterB.baumann R
  let Q := (K ⊔ S).pCoreIn 2
  let e := MulAut.conj x⁻¹
  obtain ⟨B₀, B₁, hf, _, _⟩ := h.family_eq_four x hx hnc hphi
  have hQ : Q ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; exact Set.mem_insert _ _
  have hRx : R.map e.toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hx)
  have hQx : Q.map e.toMonoidHom ∈ elementaryAbelianMaxSubgroups R := by
    have hh := (maxFamily_map_injective_iff e.toMonoidHom e.injective R Q).mpr hQ
    rwa [hRx] at hh
  apply le_antisymm
  · exact (h.core_conjugate_span x hx hnc).le.trans (sup_le (le_sSup hQ) (le_sSup hQx))
  · apply sSup_le
    intro A hA
    exact (baumann_maxFamily R ▸ hA).1
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.core_pair_preserved
    (h : AlternatingPairSetup R K L) (hRK : R ≤ normalizer (K : Set G))
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hphi : let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
      (frattini D).map D.subtype = ⊥)
    (m : G) (hm : m ∈ normalizer (R : Set G)) :
    let Q := (K ⊔ ChapterB.baumann R).pCoreIn 2
    Q.map (MulAut.conj m).toMonoidHom = Q ∨
      Q.map (MulAut.conj m).toMonoidHom = Q.map (MulAut.conj x⁻¹).toMonoidHom := by
  let Q := (K ⊔ ChapterB.baumann R).pCoreIn 2
  let f := MulAut.conj m
  let F := {B ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (B : Set G)}
  have hF : F = {Q, Q.map (MulAut.conj x⁻¹).toMonoidHom} :=
    (h.family_structure hRK x hx hnc hphi).2
  have hQ : Q ∈ F := by rw [hF]; exact Set.mem_insert _ _
  have hmR : R.map f.toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp hm
  have hmax := (maxFamily_map_injective_iff f.toMonoidHom f.injective R Q).mpr hQ.1
  have hnorm : R ≤ normalizer (Q.map f.toMonoidHom : Set G) := by
    rw [← hmR]
    exact (map_mono hQ.2).trans (le_normalizer_map f.toMonoidHom)
  have hQm : Q.map f.toMonoidHom ∈ F := ⟨by simpa only [hmR] using hmax, hnorm⟩
  rw [hF] at hQm
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hQm

/-- The source A₅ alternative, with literal right conjugates and the actual inner r. -/
theorem AlternatingPairSetup.single_block_family
    (h : AlternatingPairSetup R K L) (hRK : R ≤ normalizer (K : Set G))
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hphi : let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
      (frattini D).map D.subtype = ⊥) :
    let S := ChapterB.baumann R
    let Q := (K ⊔ S).pCoreIn 2
    ∃ A : Subgroup G, ∃ r : G,
      r ∈ R ⊓ K ∧ r ∉ S ∧ Q.relIndex A = 2 ∧
      elementaryAbelianMaxSubgroups R =
        {Q, Q.map (MulAut.conj x⁻¹).toMonoidHom, A, A.map (MulAut.conj r⁻¹).toMonoidHom} := by
  obtain ⟨A, r, hr, hrS, hf, ha, _, _⟩ := h.family_exchange x hx hnc hphi
  have hm : A ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  refine ⟨A, r⁻¹, (R ⊓ K).inv_mem hr, ?_, h.extra_family_index A hm ha, ?_⟩
  · exact fun hs => hrS (by simpa only [inv_inv] using (ChapterB.baumann R).inv_mem hs)
  · simpa only [inv_inv, (h.family_structure hRK x hx hnc hphi).1] using hf
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

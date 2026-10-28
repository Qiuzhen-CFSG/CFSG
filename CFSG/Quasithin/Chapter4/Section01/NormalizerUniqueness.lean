module

public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import CFSG.Quasithin.ChapterA.Section04.Signalizers
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.Quasithin.EvenCharacteristic

/-!
# Uniqueness for Sylow section-centralizer normalizers

Lemma 4.1.2 of Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed p. 605 (PDF p. 622).
For every Sylow two-subgroup R₊ of C = C_M(M₊/O₂(M₊)), the subgroup
N_M(R₊) has M as its unique maximal two-local overgroup.

The commutator criterion identifies the Chapter 4 section centralizer with
Appendix A's genuine section centralizer. It is normal in M, so Sylow
restriction supplies T ∩ C. A.4.2(4) makes this Sylow subgroup a signalizer,
and hence M₊ normalizes it. The Frattini argument supplies the literal set
product required by Hypothesis 4.1.1. Finally, conjugacy inside C transports
uniqueness to every Sylow subgroup. No nontriviality assumption is used.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4
variable {G : Type*} [Group G]

/-- The Chapter 4 commutator preimage and the Appendix A section action
have the same kernel, including the normalization condition. -/
theorem sectionCentralizerIn_eq_twoSectionCentralizer (M X : Subgroup G) :
    sectionCentralizerIn M X = ChapterA.Section04.twoSectionCentralizer X M := by
  apply le_antisymm
  · apply (ChapterA.Section04.le_twoSectionCentralizer_iff X M _).mpr
    have h := (le_sectionCentralizer_iff (sectionCentralizerIn M X) X).mp inf_le_right
    exact ⟨inf_le_left, h.1, (commutator_comm X _).trans_le h.2⟩
  · have h := (ChapterA.Section04.le_twoSectionCentralizer_iff X M _).mp le_rfl
    exact le_inf h.1 ((le_sectionCentralizer_iff _ X).mpr
      ⟨h.2.1, (commutator_comm _ X).trans_le h.2.2⟩)

/-- Normalizing X inside M also normalizes the centralizer of X/O₂(X)
inside M. In particular this applies when X is normal in M. -/
theorem sectionCentralizerIn_normalized {M X : Subgroup G}
    (hX : M ≤ normalizer (X : Set G)) :
    M ≤ normalizer (sectionCentralizerIn M X : Set G) := by
  rw [sectionCentralizerIn_eq_twoSectionCentralizer]
  exact ChapterA.Section04.twoSectionCentralizer_normalized X M hX

variable [Finite G]

private theorem frattini_factorization {C M : Subgroup G} (hCM : C ≤ M)
    (hMC : M ≤ normalizer (C : Set G)) (S : Sylow 2 C) :
    (M : Set G) = (C : Set G) *
      ((M ⊓ normalizer ((S : Subgroup C).map C.subtype : Set G)) : Set G) := by
  let C' := C.subgroupOf M
  let : C'.Normal := (normal_subgroupOf_iff_le_normalizer hCM).mpr hMC
  let e : C ≃* C' := (subgroupOfEquivOfLe hCM).symm
  let S' : Sylow 2 C' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : ((S' : Subgroup C').map C'.subtype).map M.subtype =
      (S : Subgroup C).map C.subtype := by
    change (((S : Subgroup C).map e.toMonoidHom).map C'.subtype).map M.subtype = _
    rw [map_map, map_map]
    rfl
  have hfr : C' ⊔ normalizer ((S' : Subgroup C').map C'.subtype : Set M) = ⊤ := by
    rw [sup_comm]
    exact S'.normalizer_sup_eq_top
  apply Set.Subset.antisymm
  · intro m hm
    have hm' : (⟨m, hm⟩ : M) ∈ C' ⊔
        normalizer ((S' : Subgroup C').map C'.subtype : Set M) := by rw [hfr]; trivial
    obtain ⟨c, hc, n, hn, he⟩ := mem_sup_of_normal_left.mp hm'
    refine ⟨c, hc, n, ⟨n.property, ?_⟩, congrArg Subtype.val he⟩
    have hh := ((S' : Subgroup C').map C'.subtype).le_normalizer_map M.subtype
      (mem_map_of_mem M.subtype hn)
    rwa [hmap] at hh
  · rintro _ ⟨c, hc, n, hn, rfl⟩
    exact M.mul_mem (hCM hc) hn.1

private theorem aligned_sylow {T : Sylow 2 G} {M X : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hMX : M ≤ normalizer (X : Set G)) :
    ∃ S : Sylow 2 (sectionCentralizerIn M X),
      (S : Subgroup (sectionCentralizerIn M X)).map (sectionCentralizerIn M X).subtype =
        sectionCentralizerIn (T : Subgroup G) X := by
  let C := sectionCentralizerIn M X
  have hCM : C ≤ M := inf_le_left
  let C' := C.subgroupOf M
  let : C'.Normal := (normal_subgroupOf_iff_le_normalizer hCM).mpr
    (sectionCentralizerIn_normalized hMX)
  obtain ⟨U, hU⟩ := (T.subtype hTM).exists_subgroupOf_eq_of_normal C'
  let e : C' ≃* C := subgroupOfEquivOfLe hCM
  refine ⟨U.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((U : Subgroup C').map e.toMonoidHom).map C.subtype = _
  rw [hU, map_map]
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨hc, c.property.2⟩
  · intro hx
    exact ⟨⟨⟨x, hTM hx.1⟩, ⟨hTM hx.1, hx.2⟩⟩, hx.1, rfl⟩

omit [Finite G] in
private theorem unique_map {I M : Subgroup G} (h : UniqueMaximalOvergroup I M)
    (e : G ≃* G) :
    UniqueMaximalOvergroup (I.map e.toMonoidHom) (M.map e.toMonoidHom) := by
  refine ⟨Theory.Quasithin.isMaximalTwoLocal_map e h.1, map_mono h.2.1, ?_⟩
  intro N hN hIN
  have hh : I ≤ N.map e.symm.toMonoidHom := by
    simpa [map_map] using map_mono (f := e.symm.toMonoidHom) hIN
  have he := h.2.2 _ (Theory.Quasithin.isMaximalTwoLocal_map e.symm hN) hh
  simpa [map_map] using congrArg (fun A : Subgroup G => A.map e.toMonoidHom) he

/-- Aschbacher–Smith 4.1.2: M is the unique maximal two-local overgroup
of the relative normalizer of any Sylow two-subgroup of C_M(M₊/O₂(M₊)). -/
theorem lemma_4_1_2 {K : GroupClass} {T : Sylow 2 G} {M Mplus : Subgroup G}
    (h : Hypothesis411 K T M Mplus)
    (S : Sylow 2 (sectionCentralizerIn M Mplus)) :
    UniqueMaximalOvergroup
      (M ⊓ normalizer ((S : Subgroup (sectionCentralizerIn M Mplus)).map
        (sectionCentralizerIn M Mplus).subtype : Set G)) M := by
  let C := sectionCentralizerIn M Mplus
  have hMX : M ≤ normalizer (Mplus : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.plus_le).mp h.plus_normal
  obtain ⟨S₀, hS₀⟩ := aligned_sylow h.sylow_le hMX
  let R₀ := (S₀ : Subgroup C).map C.subtype
  have hplus : Mplus ≤ normalizer (R₀ : Set G) := by
    have he := sectionCentralizerIn_eq_twoSectionCentralizer M Mplus
    have hs : ∃ U : Sylow 2 (ChapterA.Section04.twoSectionCentralizer Mplus M),
        (U : Subgroup (ChapterA.Section04.twoSectionCentralizer Mplus M)).map
          (ChapterA.Section04.twoSectionCentralizer Mplus M).subtype = R₀ := by
      rw [← he]
      exact ⟨S₀, rfl⟩
    have hsub : (Mplus.subgroupOf M).IsSubnormal := h.plus_normal.isSubnormal
    have hh := (ChapterA.Section04.maximal_signalizer_iff_sylow Mplus M R₀
      h.plus_le hsub h.plus_perfect).mpr hs
    exact ((ChapterA.Section04.isMaximalTwoSignalizer_iff _ _ _).mp hh).1.normalizes
  have huniq : UniqueMaximalOvergroup (M ⊓ normalizer (R₀ : Set G)) M := by
    apply h.uniqueness _ inf_le_left
    · apply sup_le
      · exact le_inf h.plus_le hplus
      · rw [← hS₀]
        exact le_inf ((map_subtype_le _).trans inf_le_left) le_normalizer
    · exact frattini_factorization inf_le_left (sectionCentralizerIn_normalized hMX) S₀
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C S₀ S
  have hconj : R₀.map (MulAut.conj (c : G)).toMonoidHom =
      (S : Subgroup C).map C.subtype := by
    rw [← hc]
    change ((S₀ : Subgroup C).map C.subtype).map (MulAut.conj (c : G)).toMonoidHom =
      ((S₀ : Subgroup C).map (MulAut.conj c).toMonoidHom).map C.subtype
    rw [map_map, map_map]
    rfl
  have hM : M.map (MulAut.conj (c : G)).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer c.property.1)
  have hh := unique_map huniq (MulAut.conj (c : G))
  rwa [Subgroup.map_inf _ _ _ (MulAut.conj (c : G)).injective, hM,
    map_equiv_normalizer_eq, hconj] at hh

end CFSG.Quasithin.Chapter4

end

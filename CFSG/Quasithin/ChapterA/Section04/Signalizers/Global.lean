module

public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Normalizer
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.SylowCore

/-!
# Global maximal signalizers and the normal-closure conclusion

For X normal in M and R = O₂(XT), A.4.2(5) gives maximality in M.
The normalizer containment gives global maximality. Applying the Sylow
characterization inside N_G(X) identifies R as Sylow in C_G(X/O₂(X));
conjugacy then makes every Sylow of this centralizer globally maximal.
Finally C_M(X/O₂(X)) is normal in M, so it contains the normal closure
of R under M, and R remains Sylow in that intermediate subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.4.2(7), printed p. 57. No subnormality of X in G is assumed.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterA.Section04
variable {G : Type*} [Group G]

private theorem signalizer_map (X M R : Subgroup G) (e : G ≃* G)
    (h : IsTwoSignalizer X M R) :
    IsTwoSignalizer (X.map e.toMonoidHom) (M.map e.toMonoidHom) (R.map e.toMonoidHom) := by
  apply (isTwoSignalizer_iff _ _ _).mpr
  refine ⟨map_mono h.le, h.isPGroup.map _, ?_⟩
  exact (map_mono h.normalizes).trans (R.le_normalizer_map e.toMonoidHom)

/-- Maximal signalizers transport under automorphisms of the ambient group. -/
theorem maximal_signalizer_map (X M R : Subgroup G) (e : G ≃* G)
    (h : IsMaximalTwoSignalizer X M R) :
    IsMaximalTwoSignalizer (X.map e.toMonoidHom) (M.map e.toMonoidHom) (R.map e.toMonoidHom) := by
  have hm := (isMaximalTwoSignalizer_iff _ _ _).mp h
  apply (isMaximalTwoSignalizer_iff _ _ _).mpr
  refine ⟨signalizer_map X M R e hm.1, ?_⟩
  intro S hS hRS
  have hs := signalizer_map _ _ _ e.symm hS
  have hback (A : Subgroup G) : (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
    ext x
    simp only [mem_map_equiv, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]
  rw [hback, hback] at hs
  have hr : R ≤ S.map e.symm.toMonoidHom := by
    simpa only [hback] using map_mono (f := e.symm.toMonoidHom) hRS
  have he := map_mono (f := e.toMonoidHom) (hm.2 _ hs hr)
  have hforward : (S.map e.symm.toMonoidHom).map e.toMonoidHom = S := by
    ext x
    simp only [mem_map_equiv, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  rwa [hforward] at he

/-- A globally maximal signalizer that normalizes X is Sylow in C_G(X/O₂(X)). -/
theorem global_maximal_signalizer_sylow (X R : Subgroup G)
    (hX : IsPPerfect 2 X) (hRN : R ≤ normalizer (X : Set G))
    (hR : IsMaximalTwoSignalizer X ⊤ R) :
    ∃ S : Sylow 2 (twoSectionCentralizer X ⊤),
      (S : Subgroup (twoSectionCentralizer X ⊤)).map
        (twoSectionCentralizer X ⊤).subtype = R := by
  have hm := (isMaximalTwoSignalizer_iff _ _ _).mp hR
  have hlocal : IsMaximalTwoSignalizer X (normalizer (X : Set G)) R := by
    apply (isMaximalTwoSignalizer_iff _ _ _).mpr
    refine ⟨(isTwoSignalizer_iff _ _ _).mpr ⟨hRN, hm.1.isPGroup, hm.1.normalizes⟩, ?_⟩
    intro S hS hRS
    exact hm.2 S ((isTwoSignalizer_iff _ _ _).mpr
      ⟨le_top, hS.isPGroup, hS.normalizes⟩) hRS
  have hc : twoSectionCentralizer X (normalizer (X : Set G)) =
      twoSectionCentralizer X ⊤ := by
    ext g
    simp only [mem_twoSectionCentralizer, mem_top, true_and, and_self_left]
  have hs := (maximal_signalizer_iff_sylow X (normalizer (X : Set G)) R
    le_normalizer (inferInstance : (X.subgroupOf (normalizer (X : Set G))).Normal).isSubnormal
    hX).mp hlocal
  rwa [hc] at hs

variable [Finite G]

/-- Once one Sylow of the global section centralizer is globally maximal,
all its Sylow two-subgroups are globally maximal signalizers. -/
theorem section_sylows_globally_maximal (X R : Subgroup G)
    (hR : IsMaximalTwoSignalizer X ⊤ R)
    (hSyl : ∃ S : Sylow 2 (twoSectionCentralizer X ⊤),
      (S : Subgroup (twoSectionCentralizer X ⊤)).map
        (twoSectionCentralizer X ⊤).subtype = R)
    (S : Sylow 2 (twoSectionCentralizer X ⊤)) :
    IsMaximalTwoSignalizer X ⊤
      ((S : Subgroup (twoSectionCentralizer X ⊤)).map
        (twoSectionCentralizer X ⊤).subtype) := by
  obtain ⟨P, rfl⟩ := hSyl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (twoSectionCentralizer X ⊤) P S
  have hmap := maximal_signalizer_map X ⊤ _ (MulAut.conj (g : G)) hR
  have hx : X.map (MulAut.conj (g : G)).toMonoidHom = X :=
    mem_normalizer_iff_map_conj_eq.mp (twoSectionCentralizer_le_normalizer X ⊤ g.property)
  rw [hx, map_top_of_surjective _ (MulAut.conj (g : G)).surjective] at hmap
  have he : ((P : Subgroup (twoSectionCentralizer X ⊤)).map
      (twoSectionCentralizer X ⊤).subtype).map (MulAut.conj (g : G)).toMonoidHom =
      (S : Subgroup (twoSectionCentralizer X ⊤)).map (twoSectionCentralizer X ⊤).subtype := by
    rw [← hg, Sylow.coe_subgroup_smul]
    change ((P : Subgroup (twoSectionCentralizer X ⊤)).map
      (twoSectionCentralizer X ⊤).subtype).map (MulAut.conj (g : G)).toMonoidHom =
      ((P : Subgroup (twoSectionCentralizer X ⊤)).map (MulAut.conj g).toMonoidHom).map
        (twoSectionCentralizer X ⊤).subtype
    rw [map_map, map_map]
    rfl
  rwa [he] at hmap
/-- The normal case of A.4.2(5), with T taken directly in M. -/
theorem normal_sylow_core_isMaximal (X M : Subgroup G)
    (hXM : X ≤ M) (hMX : M ≤ normalizer (X : Set G)) (hX : IsPPerfect 2 X)
    (T : Sylow 2 M) :
    IsMaximalTwoSignalizer X M ((X ⊔ (T : Subgroup M).map M.subtype).pCoreIn 2) := by
  have hn : (X.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMX
  have h := sylow_normalizer_core_isMaximal X M hXM hn.isSubnormal hX
  rw [inf_of_le_left hMX] at h
  exact h T

omit [Finite G] in
private theorem sylow_in_intermediate (C R L : Subgroup G)
    (hSyl : ∃ S : Sylow 2 C, (S : Subgroup C).map C.subtype = R)
    (hRL : R ≤ L) (hLC : L ≤ C) :
    ∃ S : Sylow 2 L, (S : Subgroup L).map L.subtype = R := by
  obtain ⟨P, hP⟩ := hSyl
  have hp : IsPGroup 2 R := hP ▸ P.isPGroup'.map C.subtype
  obtain ⟨S, hRS⟩ := (hp.comap_subtype : IsPGroup 2 (R.subgroupOf L)).exists_le_sylow
  have hRU : R ≤ (S : Subgroup L).map L.subtype := by
    intro r hr
    exact ⟨⟨r, hRL hr⟩, hRS hr, rfl⟩
  have hUC : (S : Subgroup L).map L.subtype ≤ C := (map_subtype_le _).trans hLC
  have hPU : (P : Subgroup C) ≤ ((S : Subgroup L).map L.subtype).subgroupOf C := by
    intro p hp
    exact hRU (hP ▸ mem_map_of_mem _ hp)
  have he := P.is_maximal' (S.isPGroup'.map L.subtype).comap_subtype hPU
  refine ⟨S, le_antisymm ?_ hRU⟩
  intro u hu
  have hmem : (⟨u, hUC hu⟩ : C) ∈ (P : Subgroup C) := by
    rw [← he]
    exact hu
  rw [← hP]
  exact ⟨⟨u, hUC hu⟩, hmem, rfl⟩

/-- A.4.2(7), including the global Sylow-family inclusion and the Sylow
assertion in the actual normal closure generated by M-conjugates of R. -/
theorem normal_sylow_core_conclusions (X M : Subgroup G)
    (hXM : X ≤ M) (hMX : M ≤ normalizer (X : Set G)) (hX : IsPPerfect 2 X)
    (T : Sylow 2 M)
    (hNM : normalizer ((X ⊔ (T : Subgroup M).map M.subtype).pCoreIn 2 : Set G) ≤ M) :
    let R := (X ⊔ (T : Subgroup M).map M.subtype).pCoreIn 2
    (∃ S : Sylow 2 (twoSectionCentralizer X ⊤),
      (S : Subgroup (twoSectionCentralizer X ⊤)).map
        (twoSectionCentralizer X ⊤).subtype = R) ∧
    (∀ S : Sylow 2 (twoSectionCentralizer X ⊤),
      IsMaximalTwoSignalizer X ⊤ ((S : Subgroup (twoSectionCentralizer X ⊤)).map
        (twoSectionCentralizer X ⊤).subtype)) ∧
    IsMaximalTwoSignalizer X ⊤ R ∧
    IsMaximalTwoSignalizer X M R ∧
    (∀ U : Subgroup G, IsMaximalTwoSignalizer X M U ↔
      ∃ S : Sylow 2 (twoSectionCentralizer X M),
        (S : Subgroup (twoSectionCentralizer X M)).map
          (twoSectionCentralizer X M).subtype = U) ∧
    R = (normalizer (R : Set G)).pCoreIn 2 ∧
    (∃ S : Sylow 2 ((normalClosure (R.subgroupOf M : Set M)).map M.subtype),
      (S : Subgroup ((normalClosure (R.subgroupOf M : Set M)).map M.subtype)).map
        ((normalClosure (R.subgroupOf M : Set M)).map M.subtype).subtype = R) := by
  dsimp only
  let R := (X ⊔ (T : Subgroup M).map M.subtype).pCoreIn 2
  have hn : (X.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMX
  have hmaxM : IsMaximalTwoSignalizer X M R := normal_sylow_core_isMaximal X M hXM hMX hX T
  have hm := ((isMaximalTwoSignalizer_iff _ _ _).mp hmaxM).1
  have hmaxG := maximal_signalizer_in_top_of_normalizer_le X M R hmaxM hNM
  have hSylG := global_maximal_signalizer_sylow X R hX
    (signalizer_le_normalizer X M R hXM hn.isSubnormal hX hm) hmaxG
  have hSylM := (maximal_signalizer_iff_sylow X M R hXM hn.isSubnormal hX).mp hmaxM
  have hodd : Odd (M.subgroupOf (normalizer (R : Set G))).index := by
    rw [subgroupOf_eq_top.mpr hNM, index_top]
    decide
  refine ⟨hSylG, section_sylows_globally_maximal X R hmaxG hSylG, hmaxG, hmaxM,
    fun U => maximal_signalizer_iff_sylow X M U hXM hn.isSubnormal hX,
    maximal_signalizer_eq_normalizer_core_of_odd_index X M R hmaxM hodd, ?_⟩
  let L := (normalClosure (R.subgroupOf M : Set M)).map M.subtype
  have hRL : R ≤ L := by
    have h := map_mono (f := M.subtype) (le_normalClosure (H := R.subgroupOf M))
    rwa [map_subgroupOf_eq_of_le hm.le] at h
  have hLC : L ≤ twoSectionCentralizer X M := by
    let C := twoSectionCentralizer X M
    have hCN : M ≤ normalizer (C : Set G) := twoSectionCentralizer_normalized X M hMX
    let : (C.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hCN
    have hRC := signalizer_le_twoSectionCentralizer X M R hXM hn.isSubnormal hX hm
    have h := map_mono (f := M.subtype) (normalClosure_le_normal
      (N := C.subgroupOf M) (show (R.subgroupOf M : Set M) ⊆ C.subgroupOf M from
        fun _ hr => hRC hr))
    rwa [map_subgroupOf_eq_of_le (twoSectionCentralizer_le X M)] at h
  exact sylow_in_intermediate (twoSectionCentralizer X M) R L hSylM hRL hLC
end CFSG.Quasithin.ChapterA.Section04

end

module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.AlternatingGeneration
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Action
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Rank-one generation for A₇ sections with a two-group supplement

For K normalized by an ambient Sylow two-subgroup T, conjugation of KT on
K/O₂(K) has a two-group kernel when that quotient is A₇. The genuine
Aut(A₇)=S₇ equivalence gives a seven-letter action with the prescribed
quotient image. The two solvable local subgroups used in E.1.14 pull back
to solvable overgroups of T and generate KT. Solvable E₁-generation and
inheritance then give n(KT) ≤ 1.

This supplies the numeric A₇ exclusion in Aschbacher–Smith 13.6.27,
printed p.934, using E.1.14(3), p.214, with the original two-core quotient.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE
open alternatingGroup.SevenSolvableGeneration
variable {G : Type*} [Group G] [Finite G]

private theorem generation_of_seven_action (L : Subgroup G) (T : Sylow 2 G)
    (hLT : L ⊔ (T : Subgroup G) = ⊤)
    (f₀ : G →* Equiv.Perm (Fin 7)) [Group.IsSolvable f₀.ker]
    (hLf₀ : L.map f₀ = alternatingGroup (Fin 7)) : IsEGenerated 1 G := by
  obtain ⟨g, hgP, hgQ⟩ := exists_conjugate_le_locals
    ((T : Subgroup G).map f₀) (T.isPGroup'.map f₀)
  let f : G →* Equiv.Perm (Fin 7) := (MulAut.conj g).toMonoidHom.comp f₀
  have hfker : f.ker = f₀.ker := by
    ext x
    change MulAut.conj g (f₀ x) = 1 ↔ f₀ x = 1
    exact (MulAut.conj g).map_eq_one_iff
  let : Group.IsSolvable f.ker := hfker ▸ inferInstance
  have hLf : L.map f = alternatingGroup (Fin 7) := by
    rw [show L.map f = (L.map f₀).map (MulAut.conj g).toMonoidHom from (map_map _ _ _).symm,
      hLf₀]
    exact Normal.map_conj_eq _ g
  let P := leftLocal.comap f
  let Q := rightLocal.comap f
  have hTP : (T : Subgroup G) ≤ P := by
    apply map_le_iff_le_comap.mp
    simpa only [map_map] using hgP
  have hTQ : (T : Subgroup G) ≤ Q := by
    apply map_le_iff_le_comap.mp
    simpa only [map_map] using hgQ
  let : Group.IsSolvable P := isSolvable_comap_of_solvable_ker f leftLocal
  let : Group.IsSolvable Q := isSolvable_comap_of_solvable_ker f rightLocal
  have hA : alternatingGroup (Fin 7) ≤ f.range := by
    rw [← hLf]
    exact map_le_range f L
  have he : alternatingGroup (Fin 7) =
      (alternatingGroup (Fin 7) ⊓ leftLocal) ⊔
        (alternatingGroup (Fin 7) ⊓ rightLocal) := by
    have hh := congrArg (map (alternatingGroup (Fin 7)).subtype) even_locals_generate
    simpa only [Subgroup.map_sup, map_comap_eq, ← MonoidHom.range_eq_map, range_subtype] using hh.symm
  have hLPQ : L ≤ P ⊔ Q := by
    have hm : L.map f ≤ (P ⊔ Q).map f := by
      rw [hLf, he]
      change _ ≤ ((leftLocal.comap f) ⊔ (rightLocal.comap f)).map f
      rw [Subgroup.map_sup, map_comap_eq, map_comap_eq]
      exact sup_le_sup (inf_le_inf_right _ hA) (inf_le_inf_right _ hA)
    have hk : f.ker ≤ P ⊔ Q := by
      apply le_trans (show f.ker ≤ P from ?_) le_sup_left
      intro x hx
      change f x ∈ leftLocal
      rw [show f x = 1 from hx]
      exact one_mem _
    have hc := comap_mono (f := f) hm
    rw [comap_map_eq, comap_map_eq, sup_eq_left.mpr hk] at hc
    exact le_sup_left.trans hc
  have hPQ : P ⊔ Q = ⊤ := top_unique (hLT ▸ sup_le hLPQ (hTP.trans le_sup_left))
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget 1 T Ω
  rw [← hPQ]
  exact sup_le
    (ChiefOrbit.solvable_overgroup_le_generationTarget (by decide) T P hTP hΩ)
    (ChiefOrbit.solvable_overgroup_le_generationTarget (by decide) T Q hTQ hΩ)

/-- A normalizing Sylow extension of an A₇ two-core quotient is E₁-generated. -/
theorem isEGenerated_one_of_alternatingSeven_quotient
    (K : Subgroup G) (T : Sylow 2 G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    IsEGenerated 1 (K ⊔ (T : Subgroup G) : Subgroup G) := by
  let J := K ⊔ (T : Subgroup G)
  let c : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  let a := pCoreJoinAction 2 hn
  let d := (MulAut.congr e).trans c.symm
  let f : J →* Equiv.Perm (Fin 7) := d.toMonoidHom.comp a
  have hc : center (K ⧸ pCore 2 K) = ⊥ := by
    apply bot_unique
    intro x hx
    have hh : e x ∈ center (alternatingGroup (Fin 7)) := (centerCongr e ⟨x, hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hh
    exact e.injective (hh.trans e.map_one.symm)
  have hfker : f.ker = a.ker := by
    ext x
    change d (a x) = 1 ↔ a x = 1
    exact d.map_eq_one_iff
  let : Group.IsNilpotent f.ker := by
    rw [hfker]
    exact (pCoreJoinAction_kernel_isPGroup 2 hn T.isPGroup' hc).isNilpotent
  have hfK (k : K) : f (inclusion le_sup_left k) =
      (e (QuotientGroup.mk' (pCore 2 K) k)).val := by
    change c.symm ((MulAut.congr e) (pCoreJoinAction 2 hn (inclusion le_sup_left k))) = _
    rw [pCoreJoinAction_on_component, MulAut.congr_conj]
    apply c.injective
    rw [c.apply_symm_apply]
    exact MulAut.conjNormal_val.symm
  have hmap : (K.subgroupOf J).map f = alternatingGroup (Fin 7) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [show f k = (e (QuotientGroup.mk' (pCore 2 K) ⟨k.val, hk⟩)).val from
        hfK ⟨k.val, hk⟩]
      exact (e _).property
    · intro hx
      obtain ⟨q, hq⟩ := e.surjective ⟨x, hx⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) q
      refine ⟨inclusion le_sup_left k, k.property, ?_⟩
      rw [hfK, hk, hq]
  apply generation_of_seven_action (K.subgroupOf J) (T.subtype le_sup_right) _ f hmap
  rw [Sylow.coe_subtype, ← subgroupOf_sup le_sup_left le_sup_right]
  exact subgroupOf_self J

/-- The numeric bound used to exclude the A₇ seed in source 13.6.27. -/
theorem generationParameter_le_one_of_alternatingSeven_quotient
    (K : Subgroup G) (T : Sylow 2 G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    generationParameter (K ⊔ (T : Subgroup G) : Subgroup G) ≤ 1 :=
  generationParameter_le (by decide) (isEGenerated_one_of_alternatingSeven_quotient K T hn e)
end CFSG.Quasithin.ChapterE

module

public import Theory.SpecificGroups.Alternating.SevenSolvableGeneration
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.Alternating.Aut

/-!
# Solvable Sylow overgroups in groups with A₇ socle

If F*(G) is isomorphic to A₇, its centralizer is trivial. The conjugation
map therefore embeds G into Aut(A₇) = S₇, and sends the actual socle onto
the alternating subgroup. After conjugating the image of a Sylow two-subgroup,
pull back the two solvable centralizers from `SevenSolvableGeneration`.
Their even parts generate the socle, and G = LT makes their pullbacks
generate G. This handles the outer extensions without assuming G = A₇.

Source application: Aschbacher--Smith, *The Classification of Quasithin
Groups*, E.1.14(3), printed p.214. The generalized Fitting centralizer theorem
and the actual automorphism theorem for A₇ supply the faithful action;
no group-family tag or assumed local generation is used.
-/

public section

open Subgroup Equiv
open Theory.GroupTheory GroupTheory.AutAlternating
namespace alternatingGroup.SevenSolvableGeneration

variable {G : Type*} [Group G] [Finite G]

/-- The faithful permutation action of a group with A₇ as its generalized Fitting subgroup. -/
theorem exists_socle_embedding (L : Subgroup G)
    (hL : L = generalizedFitting G) (e : L ≃* alternatingGroup (Fin 7)) :
    ∃ f : G →* Perm (Fin 7), Function.Injective f ∧
      L.map f = alternatingGroup (Fin 7) := by
  let : L.Normal := hL ▸ inferInstance
  have hcL : centralizer (L : Set G) ≤ L := by
    rw [hL]
    exact centralizer_generalizedFitting_le G
  have hc : centralizer (L : Set G) = ⊥ := by
    apply bot_unique
    intro x hx
    rw [mem_bot]
    let l : L := ⟨x, hcL hx⟩
    have hl : e l ∈ center (alternatingGroup (Fin 7)) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hx z z.property)
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hl
    have : l = 1 := e.injective (hl.trans e.map_one.symm)
    exact congrArg Subtype.val this
  let c : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  let f : G →* Perm (Fin 7) :=
    c.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)
  have hf : Function.Injective f := c.symm.injective.comp
    ((MulAut.congr e).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot L hc))
  have hfl (l : L) : f l = (e l : Perm (Fin 7)) := by
    apply c.injective
    change c (c.symm ((MulAut.congr e) (MulAut.conjNormal (l : G)))) =
      MulAut.conjNormal (e l : Perm (Fin 7))
    rw [c.apply_symm_apply, MulAut.conjNormal_val, MulAut.congr_conj,
      MulAut.conjNormal_val]
  refine ⟨f, hf, ?_⟩
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [hfl ⟨l, hl⟩]
    exact (e ⟨l, hl⟩).property
  · intro hx
    obtain ⟨l, hl⟩ := e.surjective ⟨x, hx⟩
    exact ⟨l, l.property, (hfl l).trans (congrArg Subtype.val hl)⟩

/-- An A₇ socle and a Sylow two-subgroup generate two solvable overgroups. -/
theorem exists_solvable_overgroups (L : Subgroup G) (T : Sylow 2 G)
    (hL : L = generalizedFitting G) (hLT : L ⊔ (T : Subgroup G) = ⊤)
    (e : L ≃* alternatingGroup (Fin 7)) :
    ∃ P Q : Subgroup G, (T : Subgroup G) ≤ P ∧ (T : Subgroup G) ≤ Q ∧
      P ⊔ Q = ⊤ ∧ Group.IsSolvable P ∧ Group.IsSolvable Q := by
  obtain ⟨f₀, hf₀, hLf₀⟩ := exists_socle_embedding L hL e
  obtain ⟨g, hgP, hgQ⟩ := exists_conjugate_le_locals
    ((T : Subgroup G).map f₀) (T.isPGroup'.map f₀)
  let f : G →* Perm (Fin 7) := (MulAut.conj g).toMonoidHom.comp f₀
  have hf : Function.Injective f := (MulAut.conj g).injective.comp hf₀
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
  have hPsolv : Group.IsSolvable P :=
    Group.isSolvable_of_isSolvable_injective (f := f.subgroupComap leftLocal)
      (fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h)))
  have hQsolv : Group.IsSolvable Q :=
    Group.isSolvable_of_isSolvable_injective (f := f.subgroupComap rightLocal)
      (fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h)))
  have hA : alternatingGroup (Fin 7) ≤ f.range := by
    rw [← hLf]
    exact map_le_range f L
  have he : alternatingGroup (Fin 7) =
      (alternatingGroup (Fin 7) ⊓ leftLocal) ⊔
        (alternatingGroup (Fin 7) ⊓ rightLocal) := by
    have hh := congrArg (map (alternatingGroup (Fin 7)).subtype) even_locals_generate
    simpa only [Subgroup.map_sup, map_comap_eq, ← MonoidHom.range_eq_map, range_subtype] using hh.symm
  have hLPQ : L ≤ P ⊔ Q := by
    apply (map_le_map_iff_of_injective hf).mp
    rw [hLf, he]
    change _ ≤ ((leftLocal.comap f) ⊔ (rightLocal.comap f)).map f
    rw [Subgroup.map_sup, map_comap_eq, map_comap_eq]
    exact sup_le_sup (inf_le_inf_right _ hA) (inf_le_inf_right _ hA)
  refine ⟨P, Q, hTP, hTQ, ?_, hPsolv, hQsolv⟩
  apply top_unique
  rw [← hLT]
  exact sup_le hLPQ (hTP.trans le_sup_left)

end alternatingGroup.SevenSolvableGeneration

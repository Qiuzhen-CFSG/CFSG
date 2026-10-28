module
public import Theory.SpecificGroups.Alternating.SevenSolvableGeneration
public import Theory.Alternating.Aut
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Proper Sylow overgroups in a normal A₇ supplement

The actual automorphism theorem Aut(A₇)=S₇ gives an action of the ambient
group whose normal layer maps onto A₇. Conjugate the Sylow image into the
two concrete solvable local subgroups. Their pullbacks contain the original
Sylow, are proper because their images cannot contain A₇, and generate the
whole ambient group. Each pullback contains the action kernel, so neither
faithfulness nor a generalized-Fitting identification is needed.

Source: Aschbacher–Smith E.2.2, printed p.216; the two concrete local
subgroups are also used in E.1.14(3), printed p.214.
-/

public section
noncomputable section
open Subgroup Equiv
open GroupTheory.AutAlternating
namespace alternatingGroup.SevenSolvableGeneration
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem exists_normal_action (L : Subgroup G) [L.Normal] (e : L ≃* alternatingGroup (Fin 7)) :
    ∃ f : G →* Perm (Fin 7), L.map f = alternatingGroup (Fin 7) := by
  let c : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  let f : G →* Perm (Fin 7) :=
    c.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)
  have hfl (l : L) : f l = (e l : Perm (Fin 7)) := by
    apply c.injective
    change c (c.symm ((MulAut.congr e) (MulAut.conjNormal (l : G)))) =
      MulAut.conjNormal (e l : Perm (Fin 7))
    rw [c.apply_symm_apply,MulAut.conjNormal_val,MulAut.congr_conj,MulAut.conjNormal_val]
  refine ⟨f,?_⟩
  ext x
  constructor
  · rintro ⟨l,hl,rfl⟩
    rw [hfl ⟨l,hl⟩]
    exact (e ⟨l,hl⟩).property
  · intro hx
    obtain ⟨l,hl⟩ := e.surjective ⟨x,hx⟩
    exact ⟨l,l.property,(hfl l).trans (congrArg Subtype.val hl)⟩

omit [Finite G] in
theorem exists_proper_overgroups_of_normal_supplement (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (hLT : L ⊔ (T : Subgroup G) = ⊤) (e : L ≃* alternatingGroup (Fin 7)) :
    ∃ P Q : Subgroup G, (T : Subgroup G) ≤ P ∧ (T : Subgroup G) ≤ Q ∧
      P ⊔ Q = ⊤ ∧ P < ⊤ ∧ Q < ⊤ := by
  obtain ⟨f₀,hLf₀⟩ := exists_normal_action L e
  obtain ⟨g,hgP,hgQ⟩ := exists_conjugate_le_locals
    ((T : Subgroup G).map f₀) (T.isPGroup'.map f₀)
  let f : G →* Perm (Fin 7) := (MulAut.conj g).toMonoidHom.comp f₀
  have hLf : L.map f = alternatingGroup (Fin 7) := by
    rw [show L.map f = (L.map f₀).map (MulAut.conj g).toMonoidHom from (map_map _ _ _).symm,hLf₀]
    exact Normal.map_conj_eq _ g
  let P := leftLocal.comap f
  let Q := rightLocal.comap f
  have hTP : (T : Subgroup G) ≤ P := by
    apply map_le_iff_le_comap.mp
    simpa only [map_map] using hgP
  have hTQ : (T : Subgroup G) ≤ Q := by
    apply map_le_iff_le_comap.mp
    simpa only [map_map] using hgQ
  have hA : alternatingGroup (Fin 7) ≤ f.range := by
    rw [←hLf]
    exact map_le_range f L
  have he : alternatingGroup (Fin 7) =
      (alternatingGroup (Fin 7) ⊓ leftLocal) ⊔
        (alternatingGroup (Fin 7) ⊓ rightLocal) := by
    have hh := congrArg (map (alternatingGroup (Fin 7)).subtype) even_locals_generate
    simpa only [Subgroup.map_sup,map_comap_eq,←MonoidHom.range_eq_map,range_subtype] using hh.symm
  have hLPQ : L ≤ P ⊔ Q := by
    have hm : L.map f ≤ (P ⊔ Q).map f := by
      rw [hLf,he]
      change _ ≤ ((leftLocal.comap f) ⊔ (rightLocal.comap f)).map f
      rw [Subgroup.map_sup,map_comap_eq,map_comap_eq]
      exact sup_le_sup (inf_le_inf_right _ hA) (inf_le_inf_right _ hA)
    have hk : f.ker ≤ P ⊔ Q := by
      apply le_trans (show f.ker ≤ P from ?_) le_sup_left
      intro x hx
      change f x ∈ leftLocal
      rw [show f x = 1 from hx]
      exact one_mem _
    have hc := comap_mono (f := f) hm
    rw [comap_map_eq,comap_map_eq,sup_eq_left.mpr hk] at hc
    exact le_sup_left.trans hc
  have hproper (B : Subgroup (Perm (Fin 7))) [Group.IsSolvable B] : B.comap f < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro hh
    have hab : alternatingGroup (Fin 7) ≤ B := by
      rw [←hLf]
      apply map_le_iff_le_comap.mpr
      rw [hh]
      exact le_top
    let : Group.IsSolvable (alternatingGroup (Fin 7)) :=
      Group.isSolvable_of_isSolvable_injective (f := inclusion hab) (inclusion_injective hab)
    let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 7)) inferInstance
  refine ⟨P,Q,hTP,hTQ,?_,hproper leftLocal,hproper rightLocal⟩
  apply top_unique
  rw [←hLT]
  exact sup_le hLPQ (hTP.trans le_sup_left)

end alternatingGroup.SevenSolvableGeneration

module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionAmbient
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionGraphSylowModel
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.SourceExceptional

/-!
# Keeping graph-short fusion inside the final generation subgroup

The exceptional enlargement argument can be performed inside any subgroup
containing the marked Sylow T and a chosen graph-centralizer Sylow R. Sylow
conjugacy then stays in that subgroup. If the local short-class witnesses
stay in T, the resulting conjugator from f to t stays in the same subgroup.

The final theorem applies this to the literal join `i.range ∨ N_G(A₂)` used
in F.5.6, once R lies in the second factor. The original source hypotheses
already imply exceptionality. Only the explicit local conjugator table
remains as an earlier input, to be discharged by the dihedral-wreath model.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, F.4.37
and the generation step F.5.6, printed pp.293 and 303–304.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

theorem source_graph_short_conjugator_in_subgroup (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (K : Subgroup G)
    (hTK : Source.sylowImage c i ≤ K)
    (R : Sylow 2 (C c i)) (hR : Tf c i < (R : Subgroup (C c i)))
    (hRK : Rimage c i R ≤ K)
    (hlocal : ∀ x ∈ Source.sylowImage c i, orderOf x = 2 →
      IsConj (rootElement c i z) x ∨
      (∃ y ∈ Source.sylowImage c i, y * sourceMarkedShort c i * y⁻¹ = x) ∨
      Nat.card (Tcentralizer c i x) ≤ 32) :
    ∃ g ∈ K, g * Source.graphElement c i * g⁻¹ = sourceMarkedShort c i := by
  obtain ⟨S,hS⟩ := source_sylowImage_isSylow c i z h
  let SK := S.subtype (hS ▸ hTK)
  let L := Rimage c i R
  have hL : IsPGroup 2 L := R.isPGroup'.map _
  obtain ⟨P,hLP⟩ := (hL.comap_subtype (K := K)).exists_le_sylow
  change L.subgroupOf K ≤ (P : Subgroup K) at hLP
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq K P SK
  let a : G ≃* G := MulAut.conj g.val
  have hmapK : (P : Subgroup K).map (MulAut.conj g).toMonoidHom = (SK : Subgroup K) :=
    congrArg Sylow.toSubgroup hg
  have hLmap : L.map a.toMonoidHom ≤ Source.sylowImage c i := by
    rintro _ ⟨l,hl,rfl⟩
    have hlK : (⟨l,hRK hl⟩ : K) ∈ P := hLP hl
    have hm := hmapK ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hlK
    change g.val * l * g.val⁻¹ ∈ (S : Subgroup G) at hm
    exact hS ▸ hm
  have hfL : Source.graphElement c i ∈ L :=
    mem_map_of_mem (C c i).subtype
      (hR.le (show (⟨Source.graphElement c i,graph_mem_C c i⟩ : C c i) ∈ Tf c i from
        source_graph_mem_sylowImage c i))
  have hxT : a (Source.graphElement c i) ∈ Source.sylowImage c i :=
    hLmap (mem_map_of_mem a.toMonoidHom hfL)
  have hx2 : orderOf (a (Source.graphElement c i)) = 2 :=
    (orderOf_injective a.toMonoidHom a.injective _).trans
      (source_graph_order c i h.embedding_injective)
  have hfx : IsConj (Source.graphElement c i) (a (Source.graphElement c i)) :=
    isConj_iff.mpr ⟨g.val,rfl⟩
  rcases hlocal _ hxT hx2 with hz | ⟨y,hy,he⟩ | hsmall
  · exact False.elim (Source.graph_not_conjugate_root c i z h (hfx.trans hz.symm))
  · refine ⟨y⁻¹*g.val,K.mul_mem (K.inv_mem (hTK hy)) g.property,?_⟩
    calc
      _ = y⁻¹ * (a (Source.graphElement c i)) * y := by
        change (y⁻¹ * g.val) * Source.graphElement c i * (y⁻¹ * g.val)⁻¹ =
          y⁻¹ * (g.val * Source.graphElement c i * g.val⁻¹) * y
        group
      _ = y⁻¹ * (y * sourceMarkedShort c i * y⁻¹) * y := by rw [← he]
      _ = _ := by group
  · have hLC : L.map a.toMonoidHom ≤ Tcentralizer c i (a (Source.graphElement c i)) := by
      refine le_inf hLmap ?_
      rintro _ ⟨l,hl,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      have hh := mem_centralizer_singleton_iff.mp (Rimage_le_C c i R hl)
      exact (map_mul a l (Source.graphElement c i)).symm.trans
        ((congrArg a hh).trans (map_mul a (Source.graphElement c i) l))
    have hle := card_le_of_le hLC
    rw [card_map_of_injective a.injective] at hle
    have hLcard : Nat.card L = Nat.card R := card_map_of_injective (C c i).subtype_injective
    rw [hLcard] at hle
    have hRcard : 32 < Nat.card R := by
      rw [← source_Tf_card c i h.embedding_injective]
      by_contra! hsmall
      exact hR.ne (eq_of_le_of_card_ge hR.le hsmall)
    exact False.elim (hRcard.not_ge (hle.trans hsmall))


/-- Apply controlled graph fusion inside the exact join used in F.5.6. -/
theorem source_graph_short_conjugator_in_join (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
    (hRH : Rimage c i R ≤ H c i)
    (hlocal : ∀ x ∈ Source.sylowImage c i, orderOf x = 2 →
      IsConj (rootElement c i z) x ∨
      (∃ y ∈ Source.sylowImage c i, y * sourceMarkedShort c i * y⁻¹ = x) ∨
      Nat.card (Tcentralizer c i x) ≤ 32) :
    ∃ g ∈ i.range ⊔ H c i,
      g * Source.graphElement c i * g⁻¹ = sourceMarkedShort c i := by
  have hstrict : Tf c i < (R : Subgroup (C c i)) := lt_of_le_of_ne hR (by
    intro he
    exact source_exceptional c i z h ⟨R,he.symm⟩)
  exact source_graph_short_conjugator_in_subgroup c i z h (i.range ⊔ H c i)
    (((sylowImage_le_M c i false).trans (M_le_completion c i false)).trans le_sup_left)
    R hstrict (hRH.trans le_sup_right) hlocal

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal

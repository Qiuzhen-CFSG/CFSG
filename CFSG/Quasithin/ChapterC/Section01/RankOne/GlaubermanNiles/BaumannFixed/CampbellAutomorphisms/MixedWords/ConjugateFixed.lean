module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.Escape

/-!
# Distinct Sylow fixed layers meet in the center

An element outside the unique maximal overgroup of S gives two Sylow
conjugates generating H. Their fixed layers therefore intersect in the
ambient center. This is the literal fixed-layer intersection used in
Campbell II.6.4(d), printed p.32.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.sylow_sup_conjugate_of_outside_maximal
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S)
    (M : Subgroup H) (hM : S ≤ M ∧ M ⋖ ⊤) (g : H) (hg : g ∉ M) :
    S ⊔ S.map (MulAut.conj g).toMonoidHom=⊤ := by
  obtain ⟨T,hT,hmin⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  obtain ⟨d,_,hSd⟩ := h.exists_campbellEmbedding hB
  have hSd' : (d.sylow : Subgroup H)=S := hSd.trans (range_subtype S)
  obtain ⟨n,hn,k,_,_,_,hk,⟨m⟩⟩ := h.natural
  have hn : ¬S ≤ pCore 2 H := by
    intro hs
    have he : S=pCore 2 H := le_antisymm hs (hST ▸ pCore_isPGroup.le_sylow_of_normal T)
    apply (ChapterB.isMinimalParabolicOver_top_iff T).mp hmin |>.2
    rw [←hST,he]
    infer_instance
  obtain ⟨x,hx,hxQ⟩ := Set.not_subset.mp hn
  by_contra hne
  have hu : Order.HasUniqueMaximalOver S ⊤ := hST ▸ hmin.1
  have hNM := hu.le_maximal hM (show S ≤ S ⊔ S.map (MulAut.conj g).toMonoidHom from le_sup_left)
    (lt_top_iff_ne_top.mpr hne)
  apply h.campbell_maximal_separation hB m d hSd M
    (by rw [hSd']; exact hM) g x hg
    (by change x ∈ (d.sylow : Subgroup H); rw [hSd']; exact hx) hxQ
  exact hNM ((show S.map (MulAut.conj g).toMonoidHom ≤ S ⊔ S.map (MulAut.conj g).toMonoidHom from le_sup_right)
    (mem_map_of_mem (MulAut.conj g).toMonoidHom hx))

theorem InLocalClass.fixed_inf_conjugate_le_center
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S)
    (M : Subgroup H) (hM : S ≤ M ∧ M ⋖ ⊤) (g : H) (hg : g ∉ M) :
    (Campbell.V H ⊓ centralizer (S : Set H)) ⊓
      (Campbell.V H ⊓ centralizer (S : Set H)).map (MulAut.conj g).toMonoidHom ≤ center H := by
  intro z hz
  apply mem_center_iff.mpr
  intro y
  have hC : S ⊔ S.map (MulAut.conj g).toMonoidHom ≤ centralizer ({z} : Set H) := by
    apply sup_le
    · intro s hs
      exact mem_centralizer_singleton_iff.mpr (hz.1.2 s hs)
    · rintro s ⟨t,ht,rfl⟩
      obtain ⟨w,hw,rfl⟩ := hz.2
      apply mem_centralizer_singleton_iff.mpr
      exact map_mul (MulAut.conj g) t w ▸ map_mul (MulAut.conj g) w t ▸ congrArg (MulAut.conj g) (hw.2 t ht)
  have hy : y ∈ S ⊔ S.map (MulAut.conj g).toMonoidHom := by
    rw [h.sylow_sup_conjugate_of_outside_maximal S hB M hM g hg]
    trivial
  exact mem_centralizer_singleton_iff.mp (hC hy)
end CFSG.Quasithin.ChapterC.GlaubermanNiles

module
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.SignedThree
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.PSL25
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SylowNormalizerInvolutionImage
/-!
# From classical Sylow action to the literal C.5.12 marked centralizer

Let D be the actual normal classical component of H, S a full Sylow two-group,
and L≤D its S-normalized SL₂ constituent. If every automorphism of D
preserving S∩D preserves L, then N_H(S) preserves L and therefore the marked
P=S∩C_H(L). For PSL₂(25) it suffices that the stabilizer of S∩D in Aut(D)
is a two-group: Frattini and Sylow maximality make the full normalizer act
through S on D. No faithfulness of the ambient action is assumed.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup
open scoped Pointwise
namespace Theory.SpecificGroups.Classical.SylowMarkedSL2
variable {H : Type*} [Group H] [Finite H]
theorem normalizer_le_normalizer_centralizer_of_characteristic_component
    (D : Subgroup H) [D.Normal] (L : Subgroup H) (hLD : L ≤ D)
    (S : Sylow 2 H) (hSL : (S : Subgroup H) ≤ normalizer (L : Set H))
    (hmodel : ∀ (T : Sylow 2 D), (T : Subgroup D) ≤ normalizer (L.subgroupOf D : Set D) →
      ∀ a : MulAut D, (T : Subgroup D).map a.toMonoidHom = T →
        (L.subgroupOf D).map a.toMonoidHom = L.subgroupOf D) :
    normalizer (S : Set H) ≤ normalizer ((S : Subgroup H) ⊓ centralizer (L : Set H) : Set H) := by
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal D
  have hTL : (T : Subgroup D) ≤ normalizer (L.subgroupOf D : Set D) := by
    rw [hT,← subgroupOf_normalizer_eq hLD]
    exact comap_mono hSL
  have hnL : normalizer (S : Set H) ≤ normalizer (L : Set H) := by
    intro n hn
    let a : MulAut D := MulAut.conjNormal n
    have ha : (T : Subgroup D).map a.toMonoidHom = T := by
      rw [hT]
      ext d
      rw [mem_map_equiv]
      change (a.symm d).val ∈ S ↔ d.val ∈ S
      rw [MulAut.conjNormal_symm_apply]
      exact ((mem_normalizer_iff''.mp hn) d.val).symm
    have he := hmodel T hTL a ha
    rw [mem_normalizer_iff_map_conj_eq]
    have hm := congrArg (Subgroup.map D.subtype) he
    rw [map_map,map_subgroupOf_eq_of_le hLD] at hm
    have hf : D.subtype.comp a.toMonoidHom = (MulAut.conj n).toMonoidHom.comp D.subtype := by ext x; rfl
    rw [hf,← map_map,map_subgroupOf_eq_of_le hLD] at hm
    exact hm
  exact (le_inf le_rfl (hnL.trans (normalizer_le_normalizer_centralizer L))).trans inf_normalizer_le_normalizer_inf

theorem normalizer_le_normalizer_centralizer_of_two_group_action
    (D : Subgroup H) [D.Normal] (S : Sylow 2 H)
    (hmodel : ∀ T : Sylow 2 D,
      IsPGroup 2 (MulAction.stabilizer (MulAut D) (T : Subgroup D)))
    (L : Subgroup H) (hLD : L ≤ D) (hSL : (S : Subgroup H) ≤ normalizer (L : Set H)) :
    normalizer (S : Set H) ≤ normalizer ((S : Subgroup H) ⊓ centralizer (L : Set H) : Set H) := by
  let N := normalizer (S : Set H)
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal D
  let A := MulAction.stabilizer (MulAut D) (T : Subgroup D)
  let f : N →* MulAut D := (MulAut.conjNormal (H := D)).comp N.subtype
  have hfA : f.range ≤ A := by
    rintro _ ⟨n,rfl⟩
    change (T : Subgroup D).map (f n).toMonoidHom = T
    rw [hT]
    ext d
    rw [mem_map_equiv]
    change ((f n).symm d).val ∈ S ↔ d.val ∈ S
    change ((MulAut.conjNormal n.val).symm d).val ∈ S ↔ d.val ∈ S
    rw [MulAut.conjNormal_symm_apply]
    exact ((mem_normalizer_iff''.mp n.property) d.val).symm
  have hfr : IsPGroup 2 f.range := (hmodel T).to_le hfA
  let f' : N →* f.range := f.rangeRestrict
  let R := S.subtype (S : Subgroup H).le_normalizer
  have hRtop : (R : Subgroup N).map f' = ⊤ := by
    change (R.mapSurjective f.rangeRestrict_surjective : Subgroup f.range) = ⊤
    exact top_le_iff.mp ((hfr.to_subgroup ⊤).le_sylow_of_normal _)
  have hnL : N ≤ normalizer (L : Set H) := by
    intro n hn
    have hm : f' ⟨n,hn⟩ ∈ (R : Subgroup N).map f' := by rw [hRtop]; trivial
    obtain ⟨s,hs,hse⟩ := hm
    have hsS : s.val ∈ S := hs
    have he : f s = f ⟨n,hn⟩ := congrArg Subtype.val hse
    have hconj (l : D) : s.val*l.val*s.val⁻¹ = n*l.val*n⁻¹ :=
      congrArg Subtype.val (DFunLike.congr_fun he l)
    apply mem_normalizer_iff.mpr
    intro l
    constructor
    · intro hl
      rw [← hconj ⟨l,hLD hl⟩]
      exact (mem_normalizer_iff.mp (hSL hsS) l).mp hl
    · intro hl
      have hd : l ∈ D := by
        have hd' : n * l * n⁻¹ ∈ D := hLD hl
        have hh := (mem_normalizer_iff.mp (Subgroup.le_normalizer_of_normal (H := D) (K := ⊤) (show n ∈ (⊤ : Subgroup H) by trivial)) l).mpr hd'
        simpa only [mul_inv_cancel_left, mul_assoc, mul_inv_cancel_right] using hh
      rw [← hconj ⟨l,hd⟩] at hl
      exact (mem_normalizer_iff.mp (hSL hsS) l).mpr hl
  exact (le_inf le_rfl (hnL.trans (normalizer_le_normalizer_centralizer L))).trans inf_normalizer_le_normalizer_inf
end Theory.SpecificGroups.Classical.SylowMarkedSL2

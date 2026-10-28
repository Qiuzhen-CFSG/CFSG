module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.SylowAutomorphisms
public import Theory.SpecificGroups.SL2.SylowPointFixer
/-!
# Exact centralizers of nonfixed natural points

Every nonidentity element of a Sylow two-subgroup of SL₂ fixes exactly
the common Sylow fixed line. For the original Campbell module, fixed-point
lifting through its actual central kernel transfers this property without
a splitting assumption. Thus a point v∈V outside C_V(S) has C_S(v)=C_S(V).
For the original local marking this is precisely O₂(H), using the proved
Sylow intersection with the local kernel. The field and quotient map are
constructed internally from C.1.17 and Baumann fixedness.
Source: Campbell II.4.3 and II.6.3, printed pp.25,30–31.
-/

public section
open Subgroup
open scoped MatrixGroups
open Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}

theorem InLocalClass.campbell_point_centralizer (h : InLocalClass e) (hB : IsBaumannFixed B)
    (S : Sylow 2 H) (v : H) (hv : v ∈ Campbell.V H)
    (hvS : v ∉ centralizer (S : Set H)) :
    (S : Subgroup H) ⊓ centralizer ({v} : Set H) =
      (S : Subgroup H) ⊓ centralizer (Campbell.V H : Set H) := by
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  obtain ⟨q,f,hq,hk,hf,he⟩ := h.exists_campbell_projection hB m
  have hVm := h.campbellV_eq_moved hB m
  let w : moved e := ⟨v,hVm ▸ hv⟩
  apply le_antisymm
  · intro x hx
    have hxv : x*v=v*x := mem_centralizer_singleton_iff.mp hx.2
    have hxfix : movedConjugate e x w = w := by
      apply Subtype.ext
      change x*v*x⁻¹=v
      rw [hxv,mul_inv_cancel_right]
    have hqx : q x = 1 := by
      by_contra hnqx
      let P := S.mapSurjective (f := q) hq
      have hpv : q x • (f w).toAdd = (f w).toAdd := by
        change (q x).val.mulVec (f w).toAdd = (f w).toAdd
        rw [←he,hxfix]
      have hall := Matrix.SpecialLinearGroup.sylow_fixed_of_nonidentity_fixed P (q x)
        (mem_map_of_mem q hx.1) hnqx (f w).toAdd hpv
      apply hvS
      intro y hy
      have hfy : f (movedConjugate e y w)=f w := by
        apply Multiplicative.toAdd.injective
        exact (he y w).trans (hall (q y) (mem_map_of_mem q hy))
      have hwy := h.natural_projection_fixed_lift hB m q hq hk f hf he y w hfy
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hwy)
    refine ⟨hx.1,?_⟩
    rw [hVm]
    have hxk : x ∈ localKernel e := hk ▸ hqx
    exact (centralizer_le (moved_le_localV e)) hxk
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hv))

theorem InLocalClass.campbell_point_centralizer_eq_core (h : InLocalClass e) (hB : IsBaumannFixed B)
    (v : H) (hv : v ∈ Campbell.V H) (hvS : v ∉ centralizer (e.range : Set H)) :
    e.range ⊓ centralizer ({v} : Set H) = pCore 2 H := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  have hSet : (d.sylow : Set H)=(e.range : Set H) := congrArg (fun X : Subgroup H => (X:Set H)) hS
  have hp := h.campbell_point_centralizer hB d.sylow v hv (hSet ▸ hvS)
  rw [hS] at hp
  rw [hp,h.campbellV_eq_moved hB m]
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨_,_,_,_,_,_,_,hC⟩ := h.exists_faithful_natural_action m
  rw [hC,←hS]
  exact d.sylow_inf_eq_core _ h.core_le_localKernel h.kernel_noPartialComplement
end CFSG.Quasithin.ChapterC.GlaubermanNiles

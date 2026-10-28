module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.QuotientCubic
public import Theory.GroupTheory.SylowKernelQuotient
public import Theory.GroupTheory.PerfectQuotientGeneration

/-!
# Removing the actual central-cover kernel in C.1.24(c)

The kernel Sylow from B.2.10 is exactly O₂(G), so the remaining kernel
modulo O₂(G) is odd. The complementary two-group forces it into the
original component image. The actual map of that image onto A₆ is a
quasisimple covering, making this remaining kernel central there.
Perfectness then lifts full permutation image to generation of G.
The possible central cubic kernel is retained throughout.
Source: Aschbacher–Smith C.1.24(c), printed pp.130–131.
-/

public section
open Subgroup Theory.GroupTheory Equiv
namespace CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.TranspositionCubic
variable {G : Type*} [Group G] [Finite G]

/-- The actual residual action kernel is central in the original component
image modulo the two-core; it need not be a two-group. -/
theorem kernel_image_le_center_component (L T : Subgroup G) [L.Normal]
    [IsQuasisimple (L ⧸ pCore 2 L)] (q : G →* Sym)
    (hQ : pCore 2 G ≤ q.ker) (hLq : L.map q = alternatingGroup (Fin 6))
    (hT : IsPGroup 2 T) (hgen : L ⊔ T = ⊤)
    (P : Sylow 2 q.ker) (hP : (P : Subgroup q.ker).map q.ker.subtype = pCore 2 G) :
    q.ker.map (QuotientGroup.mk' (pCore 2 G)) ≤
      (center (L.map (QuotientGroup.mk' (pCore 2 G)))).map
        (L.map (QuotientGroup.mk' (pCore 2 G))).subtype := by
  let π := QuotientGroup.mk' (pCore 2 G)
  let qb := QuotientGroup.lift (pCore 2 G) q hQ
  let B := L.map π
  let eB : (L ⧸ pCore 2 L) ≃* B := (inferInstance : L.Normal).isSubnormal.quotientCoreImageEquiv 2
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eB
  have hBq : B.map qb = alternatingGroup (Fin 6) := by
    rw [map_map]
    exact hLq
  let f : B →* alternatingGroup (Fin 6) := (qb.comp B.subtype).codRestrict _
    (fun x => hBq ▸ mem_map_of_mem qb x.property)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : Sym) ∈ B.map qb := by rw [hBq]; exact y.property
    obtain ⟨x,hx,he⟩ := hy
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let := alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 6))
  let cover : Covering B (alternatingGroup (Fin 6)) := ⟨f,hf⟩
  have hk : f.ker = center B := cover.ker_eq_center_of_isSimple
  have hker := kernel_le_normal_sup_of_kernel_sylow q (pCore 2 G) L T P hP hT hgen
  have hDB : q.ker.map π ≤ B := by
    have hh := map_mono (f := π) hker
    have hQπ : (pCore 2 G).map π = ⊥ := (Subgroup.map_eq_bot_iff _).mpr
      (by rw [QuotientGroup.ker_mk'])
    rw [Subgroup.map_sup,hQπ,sup_bot_eq] at hh
    exact hh
  intro x hx
  refine ⟨⟨x,hDB hx⟩,?_,rfl⟩
  rw [←hk]
  apply Subtype.ext
  change qb x = 1
  obtain ⟨k,hk,he⟩ := hx
  rw [←he]
  exact hk

/-- A subgroup containing the original two-core and the full S₆ image
already equals G, using the genuine perfect component quotient. -/
theorem eq_top_of_full_symmetric_image (L T : Subgroup G) [L.Normal]
    [IsQuasisimple (L ⧸ pCore 2 L)] (q : G →* Sym)
    (hQ : pCore 2 G ≤ q.ker) (hLq : L.map q = alternatingGroup (Fin 6))
    (hT : IsPGroup 2 T) (hgen : L ⊔ T = ⊤)
    (P : Sylow 2 q.ker) (hP : (P : Subgroup q.ker).map q.ker.subtype = pCore 2 G)
    (K : Subgroup G) (hQK : pCore 2 G ≤ K) (hK : K.map q = ⊤) : K = ⊤ := by
  let B := L.map (QuotientGroup.mk' (pCore 2 G))
  let eB : (L ⧸ pCore 2 L) ≃* B := (inferInstance : L.Normal).isSubnormal.quotientCoreImageEquiv 2
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eB
  exact eq_top_of_perfect_quotient_image (pCore 2 G) q K hQK B
    (kernel_image_le_center_component L T q hQ hLq hT hgen P hP) hK

end CFSG.Quasithin.ChapterC.RankOne.SymmetricSix

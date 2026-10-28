module
public import Theory.GroupTheory.SylowNormalRestriction
open Subgroup
open scoped Pointwise
/-!
# Centralizer indices under a centralizing supplement

If L = FQ and Q centralizes z, the centralizers of z in F and L have the
same index. Pass through L/Q, retaining the literal inclusions. Separately,
an element fixed by an ambient Sylow has odd centralizer index in every
subgroup normalized by that Sylow, by Sylow restriction in its normalizer.

These standard index facts apply to the original fixed residual in
Aschbacher–Smith 4.4.3 and 4.4.14, printed pp.623–625.
-/
public noncomputable section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A centralizing normal supplement preserves the centralizer index. -/
theorem centralizer_relIndex_cover (L F Q : Subgroup G) (hFL : F ≤ L)
    (hQL : Q ≤ L) [(Q.subgroupOf L).Normal]
    (hcover : (L : Set G) = (F : Set G) * (Q : Set G)) (z : G)
    (hQz : Q ≤ centralizer ({z} : Set G)) :
    (centralizer ({z} : Set G)).relIndex F = (centralizer ({z} : Set G)).relIndex L := by
  let C := (centralizer ({z} : Set G)).subgroupOf L
  let N := Q.subgroupOf L
  let q := QuotientGroup.mk' N
  let f := q.comp (inclusion hFL)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨u,hu,v,hv,he⟩ := hcover ▸ (show (l : G) ∈ (L : Set G) from l.property)
    refine ⟨⟨u,hu⟩,?_⟩
    have hl : l = (inclusion hFL ⟨u,hu⟩) * (⟨v,hQL hv⟩ : L) := Subtype.ext he.symm
    rw [hl,map_mul]
    have hvq : q (⟨v,hQL hv⟩ : L) = 1 := (QuotientGroup.eq_one_iff _).mpr hv
    rw [hvq,mul_one]
    rfl
  have hC : (C.map q).comap q = C := by
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr (fun x hx => hQz hx)]
  have he : (C.map q).comap f = (centralizer ({z} : Set G)).subgroupOf F := by
    rw [show f = q.comp (inclusion hFL) from rfl,←comap_comap,hC]
    rfl
  change ((centralizer ({z} : Set G)).subgroupOf F).index = C.index
  calc
    _ = (C.map q).index := he ▸ (C.map q).index_comap_of_surjective hf
    _ = C.index := by
      have hh := (C.map q).index_comap_of_surjective (QuotientGroup.mk'_surjective N)
      rw [hC] at hh
      exact hh.symm

/-- A Sylow-fixed element has odd centralizer index in a normalized subgroup. -/
theorem sylow_fixed_centralizer_odd_index (T : Sylow 2 G) (L : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G)) (z : G)
    (hz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ¬ 2 ∣ (centralizer ({z} : Set G)).relIndex L := by
  let M := normalizer (L : Set G)
  let N := L.subgroupOf M
  let S := T.subtype hn
  obtain ⟨P,hP⟩ := S.exists_sylow_map_eq_inf_of_normal N
  let e : N ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hR : (R : Subgroup L) ≤ (centralizer ({z} : Set G)).subgroupOf L := by
    rintro l ⟨x,hx,rfl⟩
    have hp : (x : M) ∈ (S : Subgroup M) ⊓ N := hP ▸ mem_map_of_mem N.subtype hx
    exact hz hp.1
  exact fun hd => R.not_dvd_index (hd.trans (index_dvd_of_le hR))
end Subgroup

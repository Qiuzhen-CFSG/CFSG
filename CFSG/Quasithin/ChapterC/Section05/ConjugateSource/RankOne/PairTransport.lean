module

public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Setup

/-!
# Transporting the two-conjugate generation argument

A quotient conjugator lifts to LS and can be chosen in L because its
S-component preserves S. Pulling generation back through a homomorphism
with kernel the actual two-core, the supplied equality S = UˣQ replaces
both copies of S by their corresponding copies of Uˣ modulo Q.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.6,
printed pp.156–157 (PDF pp.167–168).
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
universe u v
variable {G : Type u} [Group G] {M : Type v} [Group M]

private theorem map_conj (f : G →* M) (B : Subgroup G) (g : G) :
    (B.map (MulAut.conj g).toMonoidHom).map f =
      (B.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

private theorem conjugator_in_left (L B : Subgroup G) (hn : B ≤ normalizer (L : Set G))
    {g : G} (hg : g ∈ L ⊔ B) : ∃ l ∈ L,
      B.map (MulAut.conj g).toMonoidHom = B.map (MulAut.conj l).toMonoidHom := by
  have hm : g ∈ (L : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L B hn]
    exact hg
  obtain ⟨l, hl, b, hb, rfl⟩ := hm
  refine ⟨l, hl, ?_⟩
  have he : (MulAut.conj (l * b)).toMonoidHom =
      (MulAut.conj l).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hb' : B.map (MulAut.conj b).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp (B.le_normalizer hb)
  rw [he, ← map_map, hb']

/-- A conjugator in LS may be chosen inside L: its S-component preserves S. -/
theorem choose_block_conjugator {F : Type*} [Field F] {R L : Subgroup G}
    (h : Setup R L F)
    (f : (L ⊔ S R : Subgroup G) →* M) (hf : Function.Surjective f)
    (hpair : ∃ g : M,
      ((S R).subgroupOf (L ⊔ S R)).map f ⊔
        (((S R).subgroupOf (L ⊔ S R)).map f).map (MulAut.conj g).toMonoidHom = ⊤) :
    ∃ y : (L ⊔ S R : Subgroup G), (y : G) ∈ L ∧
      ((S R).subgroupOf (L ⊔ S R)).map f ⊔
        (((S R).subgroupOf (L ⊔ S R)).map f).map
          (MulAut.conj (f y)).toMonoidHom = ⊤ := by
  obtain ⟨g, hg⟩ := hpair
  obtain ⟨t, rfl⟩ := hf g
  have hn : S R ≤ normalizer (L : Set G) := h.normalizes
  obtain ⟨y, hy, he⟩ := conjugator_in_left L (S R) hn t.property
  let y' : (L ⊔ S R : Subgroup G) := ⟨y, mem_sup_left hy⟩
  have hi : ((S R).subgroupOf (L ⊔ S R)).map (MulAut.conj t).toMonoidHom =
      ((S R).subgroupOf (L ⊔ S R)).map (MulAut.conj y').toMonoidHom := by
    apply map_injective (L ⊔ S R).subtype_injective
    rw [map_conj, map_conj, map_subgroupOf_eq_of_le le_sup_right]
    exact he
  refine ⟨y', hy, ?_⟩
  rw [← map_conj, ← hi, map_conj]
  exact hg

/-- Lift genuine quotient generation using the actual two-core as kernel.
The span premise replaces each copy of S by the corresponding copy of Uˣ. -/
theorem lift_quotient_pair {R L V : Subgroup G}
    (hspan : S R = V ⊔ Q R L)
    (f : (L ⊔ S R : Subgroup G) →* M)
    (hker : f.ker = (Q R L).subgroupOf (L ⊔ S R))
    {y : (L ⊔ S R : Subgroup G)}
    (hgen : ((S R).subgroupOf (L ⊔ S R)).map f ⊔
      (((S R).subgroupOf (L ⊔ S R)).map f).map
        (MulAut.conj (f y)).toMonoidHom = ⊤) :
    L ≤ (V ⊔ V.map (MulAut.conj (y : G)).toMonoidHom) ⊔ Q R L := by
  let T := L ⊔ S R
  have hv : V ≤ T := (hspan ▸ le_sup_left).trans le_sup_right
  have hq : Q R L ≤ T := pCoreIn_le 2 T
  have hs : ((S R).subgroupOf T).map f = (V.subgroupOf T).map f := by
    have hs' := congrArg (fun B : Subgroup G => B.subgroupOf T) hspan
    rw [subgroupOf_sup hv hq] at hs'
    rw [hs', Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff _).mpr (le_of_eq hker.symm), sup_bot_eq]
  rw [hs, ← map_conj, ← Subgroup.map_sup] at hgen
  have he := congrArg (Subgroup.comap f) hgen
  rw [comap_map_eq, comap_top, hker] at he
  have ht := congrArg (Subgroup.map T.subtype) he
  rw [Subgroup.map_sup, Subgroup.map_sup, map_conj,
    map_subgroupOf_eq_of_le hv, map_subgroupOf_eq_of_le hq,
    ← MonoidHom.range_eq_map, range_subtype] at ht
  exact (le_sup_left : L ≤ T).trans ht.ge

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne

end

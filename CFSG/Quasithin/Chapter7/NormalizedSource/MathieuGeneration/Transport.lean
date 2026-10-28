module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Transport
public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import Theory.GroupTheory.NormalizerQuotientOuterPair

/-!
# Transport of the literal Hall--Cartan action

An intrinsic parabolic witness is first restricted to H ∩ M and then
embedded in M, retaining the original ambient Sylow subgroup. For
M = N_G(L), quotient conjugation has its kernel in C_G(L/O₂(L)) and
its image contains every inner automorphism of L/O₂(L). Faithfulness
on the cyclic subgroup therefore transports the complete Cartan witness
to this actual image, including its Sylow and permutation clauses.

Source: Aschbacher--Smith, E.3.38 and the faithful Hall step of 7.3.4,
printed pp.240 and 699.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open ChapterB ChapterE.Section06.FixedPointBounds
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G]

/-- Place the Hall witness in M without replacing the prescribed Sylow.
The carrier of the original parabolic remains H throughout. -/
def overlapWitness {T : Sylow 2 G} {H M : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hTM : (T : Subgroup G) ≤ M)
    {hP : IsMinimalParabolicOver (T.subtype hTH) ⊤} {f : ℕ}
    (d : IntrinsicHallCartanData (T.subtype hTH) hP f)
    (he : minimalParabolicMax (T.subtype hTH) hP = M.subgroupOf H) :
    NPrimeWitness M f := by
  let J := M.subgroupOf H
  let g : J →* M := (H.subtype.comp J.subtype).codRestrict M (fun x => x.property)
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : M => (x : G)) hab
  have hB : d.witness.abelianGroup ≤ J := d.hall_le.trans_eq he
  have hS : (d.witness.sylow : Subgroup H) ≤ J := by
    rw [d.sylow_eq]
    exact (minimalParabolicMax_spec (T.subtype hTH) hP).2.trans_eq he
  let w := MarkedModels.restrictWitness d.witness J hB hS
  have hR : (w.sylow : Subgroup J).map g = (T.subtype hTM : Subgroup M) := by
    apply map_injective M.subtype_injective
    rw [map_map]
    change ((d.witness.sylow : Subgroup H).subgroupOf J).map
        (H.subtype.comp J.subtype) = ((T : Subgroup G).subgroupOf M).map M.subtype
    rw [← map_map, map_subgroupOf_eq_of_le hS, d.sylow_eq,
      map_subgroupOf_eq_of_le hTM]
    exact map_subgroupOf_eq_of_le hTH
  exact MarkedModels.embedWitness w g hg (T.subtype hTM) hR

theorem overlapWitness_cyclic_image {T : Sylow 2 G} {H M : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hTM : (T : Subgroup G) ≤ M)
    {hP : IsMinimalParabolicOver (T.subtype hTH) ⊤} {f : ℕ}
    (d : IntrinsicHallCartanData (T.subtype hTH) hP f)
    (he : minimalParabolicMax (T.subtype hTH) hP = M.subgroupOf H) :
    (overlapWitness hTH hTM d he).cyclicGroup.map M.subtype =
      d.witness.cyclicGroup.map H.subtype := by
  change ((d.witness.cyclicGroup.subgroupOf (M.subgroupOf H)).map _).map M.subtype = _
  rw [map_map]
  change (d.witness.cyclicGroup.subgroupOf (M.subgroupOf H)).map
    (H.subtype.comp (M.subgroupOf H).subtype) = _
  rw [← map_map, map_subgroupOf_eq_of_le (d.witness.cyclic_le.trans (he ▸ d.hall_le))]

/-- The kernel uses the intrinsic two-core of L; no ambient normality of L
is assumed. -/
theorem quotientAction_kernel_image_le (L : Subgroup G) :
    (normalizerPCoreQuotientAction L).ker.map (normalizer (L : Set G)).subtype ≤
      Chapter4.sectionCentralizer L := by
  apply (Chapter4.le_sectionCentralizer_iff _ _).mpr
  refine ⟨map_subtype_le _, commutator_le.mpr ?_⟩
  rintro _ ⟨b, hb, rfl⟩ l hl
  let l' : L := ⟨l, hl⟩
  let bl := L.normalizerMonoidHom b l'
  have hbl := DFunLike.congr_fun
    (show normalizerPCoreQuotientAction L b = 1 from hb)
      (QuotientGroup.mk' (pCore 2 L) l')
  change quotientAut (pCore 2 L) _ _ = _ at hbl
  rw [quotientAut_apply_mk] at hbl
  have hh : bl * l'⁻¹ ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 L) (bl * l'⁻¹) = 1
    rw [map_mul, map_inv]
    change QuotientGroup.mk' (pCore 2 L) bl = QuotientGroup.mk' (pCore 2 L) l' at hbl
    rw [hbl, mul_inv_cancel]
  exact ⟨bl * l'⁻¹, hh, rfl⟩

/-- The quotient-conjugation image includes all inner automorphisms, even
when L/O₂(L) has nontrivial center. -/
theorem inner_le_quotientAction_range (L : Subgroup G) :
    MulAut.innerSubgroup (L ⧸ pCore 2 L) ≤ (normalizerPCoreQuotientAction L).range := by
  rintro a ⟨x, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
  exact ⟨inclusion L.le_normalizer l, normalizerPCoreQuotientAction_inner L l⟩

/-- Only faithfulness on the cyclic Cartan subgroup is needed for the
parameter comparison; the actual Hall-faithfulness theorem supplies it. -/
theorem le_nPrime_quotientAction_of_faithful [Finite G] (L : Subgroup G) {f : ℕ}
    (w : NPrimeWitness (normalizer (L : Set G)) f)
    (hfaith : w.cyclicGroup.map (normalizer (L : Set G)).subtype ⊓
      Chapter4.sectionCentralizer L = ⊥) :
    f ≤ nPrime (normalizerPCoreQuotientAction L).range := by
  let a := normalizerPCoreQuotientAction L
  apply (w.map a.rangeRestrict a.rangeRestrict_surjective ?_).le_nPrime
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hxker : (x : normalizer (L : Set G)) ∈ a.ker :=
    congrArg Subtype.val (show a.rangeRestrict x = 1 from hx)
  have hxC := quotientAction_kernel_image_le L
    (mem_map_of_mem (normalizer (L : Set G)).subtype hxker)
  have hx1 : ((x : normalizer (L : Set G)) : G) = 1 :=
    mem_bot.mp (hfaith ▸ ⟨mem_map_of_mem _ x.property, hxC⟩)
  exact mem_bot.mpr (Subtype.ext (Subtype.ext hx1))

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

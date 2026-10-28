module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.LocalControl
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The actual core quotients in the degree-eight branch

The marked component map descends through `O₂(L)`. Quasisimplicity makes
its kernel central; the precise I.1.3 input on finite perfect central covers
of `A₈` then makes that kernel a two-group. Maximality of the two-core
identifies the kernel with `O₂(L)`. Since `I = LS`, the entire star kernel
is a two-group as well, hence equals `O₂(I)`.

The quotient equivalences commute with the original star map. Thus every
subgroup marking can be transported without changing the recognition
coordinates. This module does not construct the natural module. The
multiplier theorem remains an explicit universal source input, rather
than an assumed local centralizer or quotient identification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.1.3 and
the paragraph preceding 15.3.32, printed p.1132 (PDF p.1149).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
universe u
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule

/-- The exact consequence of the `A₈` multiplier calculation used here:
every finite perfect central cover of the actual alternating group of degree
eight has two-group kernel. No local quotient conclusion is built into it. -/
def EightCoverKernelTwo : Prop :=
  ∀ (H : Type u) [Group H] [Finite H]
    (f : PerfectCentralCovering.Cover H (alternatingGroup (Fin 8))),
    IsPGroup 2 f.toMonoidHom.ker

private theorem ker_eq_core {H K : Type*} [Group H] [Finite H] [Group K] [Nontrivial K]
    (f : H →* K) (hf : Function.Surjective f)
    [IsQuasisimple (H ⧸ pCore 2 H)] (hle : pCore 2 H ≤ f.ker)
    (hcover : ∀ e : PerfectCentralCovering.Cover (H ⧸ pCore 2 H) K,
      IsPGroup 2 e.toMonoidHom.ker) : f.ker = pCore 2 H := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let g := QuotientGroup.lift (pCore 2 H) f hle
  have hgf (x : H) : g (q x) = f x := rfl
  have hg : Function.Surjective g := by
    intro k
    obtain ⟨h, rfl⟩ := hf k
    exact ⟨q h, hgf h⟩
  have hc : g.ker ≤ center (H ⧸ pCore 2 H) := by
    rcases IsQuasisimple.normal_le_center_or_eq_top g.ker with hc | ht
    · exact hc
    · have htriv : ∀ k : K, k = 1 := by
        intro k
        obtain ⟨x, rfl⟩ := hg k
        exact (show x ∈ g.ker from ht ▸ mem_top x)
      exact (not_nontrivial_iff_subsingleton.mpr ⟨fun x y => (htriv x).trans (htriv y).symm⟩
        inferInstance).elim
  let e : PerfectCentralCovering.Cover (H ⧸ pCore 2 H) K :=
    { g with surjective := hg, isPerfect := inferInstance, ker_le_center := hc }
  have hqker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hpre : g.ker.comap q = f.ker := rfl
  have hp : IsPGroup 2 f.ker := hpre ▸ (hcover e).comap_of_ker_isPGroup q hqker
  exact le_antisymm (le_sSup ⟨inferInstance, hp⟩) hle

variable {G : Type u} [Group G]

/-- Restrict the supplied star marking to the actual component. -/
noncomputable def componentMap (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    c.L →* alternatingGroup (Fin 8) :=
  ((e.toMonoidHom.comp (d.starMap I)).comp (inclusion (component_le c))).codRestrict _ (by
    intro l
    rw [← hmark]
    exact mem_map_of_mem _ (mem_map_of_mem _ (show (⟨l, component_le c l.property⟩ : I) ∈
      c.L.subgroupOf I from l.property)))

/-- The marked subgroup equality makes the component map onto `A₈`. -/
theorem componentMap_surjective (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    Function.Surjective (componentMap d c e hmark) := by
  intro a
  have ha : (a : Equiv.Perm (Fin 8)) ∈ (d.starImage I c.L).map e.toMonoidHom :=
    SetLike.ext_iff.mp hmark.symm (a : Equiv.Perm (Fin 8)) |>.mp a.property
  obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := ha
  exact ⟨⟨i, hi⟩, Subtype.ext hb⟩

/-- The multiplier input and quasisimple core quotient identify the
component kernel. Normality is only required inside `I`. -/
theorem componentMap_ker [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hcover : EightCoverKernelTwo.{u}) :
    (componentMap d c e hmark).ker = pCore 2 c.L := by
  let _ := c.core_quotient_quasisimple
  apply ker_eq_core _ (componentMap_surjective d c e hmark) ?_ (hcover _)
  have hIL := (normal_subgroupOf_iff_le_normalizer (component_le c)).mp hnormal
  have hcore : c.L.pCoreIn 2 ≤ I.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 c.L)
      ((pCoreIn_le 2 c.L).trans (component_le c))
      (hIL.trans (normalizer_le_normalizer_characteristic_image c.L (pCore 2 c.L)))
  intro l hl
  have hmem := core_le_star_kernel d P hP (hcore (mem_map_of_mem _ hl))
  obtain ⟨i, hi, he⟩ := hmem
  change componentMap d c e hmark l = 1
  apply Subtype.ext
  change e (d.starMap I ⟨l, component_le c l.property⟩) = 1
  have hi' : d.starMap I ⟨l, component_le c l.property⟩ = 1 := by
    have hh : i = ⟨l, component_le c l.property⟩ := Subtype.ext he
    exact hh ▸ hi
  rw [hi', map_one]

private theorem isPGroup_of_supplement {H : Type*} [Group H]
    (N L S : Subgroup H) [L.Normal] (hLS : L ⊔ S = ⊤)
    (hS : IsPGroup 2 S) (hNL : IsPGroup 2 (N ⊓ L : Subgroup H)) : IsPGroup 2 N := by
  let q := QuotientGroup.mk' L
  have hL : L.map q = ⊥ := by
    exact (map_eq_bot_iff L).mpr (by rw [QuotientGroup.ker_mk'])
  have hSq : S.map q = ⊤ := by
    have h := congrArg (Subgroup.map q) hLS
    rw [Subgroup.map_sup, hL, bot_sup_eq, map_top_of_surjective q (QuotientGroup.mk'_surjective L)] at h
    exact h
  have hquot : IsPGroup 2 (H ⧸ L) := by
    have hp := hS.map q
    rw [hSq] at hp
    exact hp.of_equiv topEquiv
  intro n
  obtain ⟨k, hk⟩ := hquot (q n)
  have hnL : (n : H) ^ 2 ^ k ∈ L := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((n : H) ^ 2 ^ k) = 1
    simpa only [map_pow] using hk
  obtain ⟨j, hj⟩ := hNL ⟨(n : H) ^ 2 ^ k, N.pow_mem n.property _, hnL⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  change (n : H) ^ 2 ^ (k + j) = 1
  rw [pow_add, pow_mul]
  exact congrArg Subtype.val hj


/-- A two-group supplement extends the component kernel calculation to
all of `I`, identifying the denominator of the original star quotient. -/
theorem starMap_ker [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hcover : EightCoverKernelTwo.{u}) :
    (d.starMap I).ker = pCore 2 I := by
  let _ := hnormal
  have hLI := component_le c
  have hSI : d.S ≤ I := hI ▸ le_sup_right
  have hLS : c.L.subgroupOf I ⊔ d.S.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLI, map_subgroupOf_eq_of_le hSI,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hI.symm
  have hS : IsPGroup 2 (d.S.subgroupOf I) := by
    have hsub : d.S.subgroupOf I = (P : Subgroup I) := by
      apply map_injective I.subtype_injective
      rw [map_subgroupOf_eq_of_le hSI, hP]
    rw [hsub]
    exact P.isPGroup'
  have hkcomp := componentMap_ker d c hnormal P hP e hmark hcover
  have hNL : IsPGroup 2 ((d.starMap I).ker ⊓ c.L.subgroupOf I : Subgroup I) := by
    let f : ((d.starMap I).ker ⊓ c.L.subgroupOf I : Subgroup I) →*
        (componentMap d c e hmark).ker := {
      toFun x := ⟨⟨x.val, x.property.2⟩, by
        apply Subtype.ext
        change e (d.starMap I x.val) = 1
        rw [show d.starMap I x.val = 1 from x.property.1, map_one]⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : (componentMap d c e hmark).ker => ((z : c.L) : G)) h))
    have hp : IsPGroup 2 (componentMap d c e hmark).ker := by
      rw [hkcomp]
      exact pCore_isPGroup
    exact hp.of_injective f hf
  have hk : IsPGroup 2 (d.starMap I).ker :=
    isPGroup_of_supplement _ _ _ hLS hS hNL
  have hle : (d.starMap I).ker ≤ pCore 2 I := le_sSup ⟨inferInstance, hk⟩
  apply le_antisymm hle
  intro i hi
  have hm := core_le_star_kernel d P hP (mem_map_of_mem I.subtype hi)
  obtain ⟨j, hj, he⟩ := hm
  exact (Subtype.ext he : j = i) ▸ hj

/-- Identify the intrinsic core quotient with the original action quotient,
retaining its quotient map and hence its subgroup markings. -/
noncomputable def coreEquivStar [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hcover : EightCoverKernelTwo.{u}) : (I ⧸ pCore 2 I) ≃* d.Star I :=
  (QuotientGroup.quotientMulEquivOfEq
    (starMap_ker d c hnormal hI P hP e hmark hcover).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (d.starMap I) (QuotientGroup.mk'_surjective _))


/-- The component marking is exactly the restriction of the supplied marking. -/
@[simp] theorem componentMap_apply (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) (l : c.L) :
    (componentMap d c e hmark l : Equiv.Perm (Fin 8)) =
      e (d.starMap I ⟨l, component_le c l.property⟩) := rfl

/-- The core-quotient comparison commutes with the original star projection. -/
@[simp] theorem coreEquivStar_apply [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hcover : EightCoverKernelTwo.{u}) (i : I) :
    coreEquivStar d c hnormal hI P hP e hmark hcover (QuotientGroup.mk' (pCore 2 I) i) =
      d.starMap I i := rfl

/-- The intrinsic component quotient is the marked alternating group. -/
noncomputable def componentCoreEquivEight [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hcover : EightCoverKernelTwo.{u}) :
    (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 8) :=
  (QuotientGroup.quotientMulEquivOfEq
    (componentMap_ker d c hnormal P hP e hmark hcover).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (componentMap d c e hmark)
      (componentMap_surjective d c e hmark))

/-- The component quotient equivalence preserves the original marked map. -/
@[simp] theorem componentCoreEquivEight_apply [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hcover : EightCoverKernelTwo.{u}) (l : c.L) :
    componentCoreEquivEight d c hnormal P hP e hmark hcover
      (QuotientGroup.mk' (pCore 2 c.L) l) = componentMap d c e hmark l := rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule

end

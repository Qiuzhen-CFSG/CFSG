module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Local
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action

/-!
# The component quotient in the small-extension argument

The two-core of a relatively normal component centralizes U_I because it
lies in the common Sylow subgroup and is normalized by I. Thus the component
star map factors through L/O₂(L). When the MS classification establishes that
this quotient is simple, its nontrivial star image forces the induced map to
be an isomorphism. The isomorphism is compatible with the given quotient map.

This proves the quotient comparison in 15.3.31 conditional on the earlier
normality, Sylow, and classification conclusions, without identifying an
ambient quotient with a relative quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed p.1132 (PDF p.1149), proof of 15.3.31, first paragraph.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension

variable {G : Type*} [Group G]

/-- The restriction of the genuine star quotient map to the component, with codomain its image. -/
def componentMap (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I) :
    c.L →* d.starImage I c.L where
  toFun l := ⟨d.starMap I ⟨l, component_le c l.property⟩,
    mem_map.mpr ⟨⟨l, component_le c l.property⟩, l.property, rfl⟩⟩
  map_one' := Subtype.ext ((d.starMap I).map_one)
  map_mul' x y := Subtype.ext ((d.starMap I).map_mul
    (⟨x, component_le c x.property⟩ : I) (⟨y, component_le c y.property⟩ : I))

/-- Every element of the component star image has a lift in the component. -/
theorem componentMap_surjective (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) : Function.Surjective (componentMap d c) := by
  rintro ⟨q, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Relative normality and the common Sylow subgroup make O₂(L) centralize U_I.
The proof propagates centralization of Z through its I-conjugates. -/
theorem component_core_centralizes_span (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) :
    c.L.pCoreIn 2 ≤ centralizer (d.UI I : Set G) := by
  have hIL : I ≤ normalizer (c.L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (component_le c)).mp hnormal
  have hIQ := hIL.trans (normalizer_le_normalizer_characteristic_image c.L (pCore 2 c.L))
  have hcore : c.L.pCoreIn 2 ≤ I.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 c.L)
      ((pCoreIn_le 2 c.L).trans (component_le c)) hIQ
  have hQT : c.L.pCoreIn 2 ≤ (d.T : Subgroup G) :=
    (hcore.trans (show I.pCoreIn 2 ≤ d.S from hP ▸ pCoreIn_le_sylow I P)).trans inf_le_left
  apply le_centralizer_iff.mpr
  exact conjugateSpanBy_le
    ((centralInvolutions_le_centralizer_sylow d.T).trans (centralizer_le hQT))
    (hIQ.trans (normalizer_le_normalizer_centralizer _))

/-- The action of the component factors through its intrinsic two-core quotient. -/
theorem core_le_componentMap_ker (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hc : c.L.pCoreIn 2 ≤ centralizer (d.UI I : Set G)) :
    pCore 2 c.L ≤ (componentMap d c).ker := by
  intro x hx
  apply Subtype.ext
  change d.starMap I ⟨x, _⟩ = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  exact hc (mem_map.mpr ⟨x, hx, rfl⟩)

/-- Once the MS classification proves simplicity of L/O₂(L), the induced
surjection to L* is an isomorphism. Simplicity is an explicit remaining
classification input; nontriviality of L* follows from the component witness. -/
noncomputable def coreQuotientEquivStar (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)] :
    (c.L ⧸ pCore 2 c.L) ≃* d.starImage I c.L := by
  let f := QuotientGroup.lift (pCore 2 c.L) (componentMap d c)
    (core_le_componentMap_ker d c (component_core_centralizes_span d c hnormal P hP))
  have hf : Function.Surjective f :=
    QuotientGroup.lift_surjective_of_surjective _ _ (componentMap_surjective d c) _
  have hn : Nontrivial (d.starImage I c.L) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (component_star_ne_bot d c)
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rcases f.normal_ker.eq_bot_or_eq_top with h | h
    · exact h
    · have he : f = 1 := MonoidHom.ker_eq_top_iff.mp h
      obtain ⟨a, ha⟩ := exists_ne (1 : d.starImage I c.L)
      obtain ⟨x, rfl⟩ := hf a
      exact (ha (by rw [he]; rfl)).elim
  exact MulEquiv.ofBijective f ⟨hinj, hf⟩

/-- The quotient identification agrees with the original star map on every lift. -/
theorem coreQuotientEquivStar_apply (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)] (l : c.L) :
    coreQuotientEquivStar d c hnormal P hP (QuotientGroup.mk' (pCore 2 c.L) l) =
      componentMap d c l := rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension

end

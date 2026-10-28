module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.QuotientEscape
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSmallGenerationTorus
public import Theory.GroupTheory.NormalCentralQuotientAction.PerfectNormalizer

/-!
# The actual Cartan action on a normal containing quotient

The perfect residual lies in the given normal subgroup C of Y. The
embedded O₂(C) lies in O₂(Y), hence in the original full Sylow T, so
it normalizes O²(H). Perfect quotient-action lifting therefore identifies
the full inverse image of the residual-image normalizer. Apply this to
the original A ∩ Y: its image is cyclic and odd, the right Hall image
normalizes it, and escape makes it nontrivial and not contained in that
right Hall image. Normality is relative to Y throughout.

Source: Aschbacher--Smith, the automorphism-action reduction in 5.1.13,
printed p.636. The companion assembly constructs C as the normal Sylow
orbit of the original containing component; no model is assumed here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

/-- Normalization of the residual image in Aut(C/O₂(C)) lifts to the original residual. -/
theorem residual_action_normalizer {T : Sylow 2 G} {M H Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hgen : 1 < ChapterE.generationParameter H) (hHY : H ≤ Y)
    (C : Subgroup Y) [C.Normal] (hRC : (residual H).subgroupOf Y ≤ C) :
    (normalizer (((residual H).subgroupOf Y).map
      (normalQuotientAction C (pCore 2 C)) : Set (MulAut (C ⧸ pCore 2 C)))).comap
      (normalQuotientAction C (pCore 2 C)) =
        (normalizer (residual H : Set G)).subgroupOf Y := by
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hHY
  let := residual_perfect hG hTM hH hgen
  let : Group.IsPerfect ((residual H).subgroupOf Y) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRY).symm.toMonoidHom)
    (subgroupOfEquivOfLe hRY).symm.surjective
  let : Group.IsNilpotent (pCore 2 C) := pCore_isPGroup.isNilpotent
  have hn : (pCore 2 C).map C.subtype ≤ normalizer ((residual H).subgroupOf Y : Set Y) := by
    rw [←subgroupOf_normalizer_eq hRY]
    exact (pCoreIn_le_of_subnormal 2 (inferInstance : C.Normal).isSubnormal).trans
      ((pCore_isPGroup.le_sylow_of_normal (T.subtype (hH.1.1.2.trans hHY))).trans
        (comap_mono (hH.1.1.2.trans (le_normalizer_residual H))))
  rw [normalQuotientAction_perfect_normalizer C (pCore 2 C) _ hRC hn,
    ←subgroupOf_normalizer_eq hRY]

/-- The original escaping Cartan gives the nontrivial cyclic odd actor of the source sieve. -/
theorem cartan_action_escape
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) [C.Normal] (hRC : (residual H).subgroupOf Y ≤ C) :
    let f := normalQuotientAction C (pCore 2 C)
    let Dbar := (A.subgroupOf Y).map f
    let Bbar := (B.subgroupOf Y).map f
    IsCyclic Dbar ∧ Odd (Nat.card Dbar) ∧
      Bbar ≤ normalizer (Dbar : Set (MulAut (C ⧸ pCore 2 C))) ∧
      ¬ Dbar ≤ normalizer (((residual H).subgroupOf Y).map f : Set _) ∧
      Dbar ≠ ⊥ ∧ ¬ Dbar ≤ Bbar := by
  let f := normalQuotientAction C (pCore 2 C)
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have he : ¬ (A.subgroupOf Y).map f ≤
      normalizer (((residual H).subgroupOf Y).map f : Set _) := by
    intro hn
    have hn' := map_le_iff_le_comap.mp hn
    rw [residual_action_normalizer h.qtke h.sylow_normalizes hH hgen hY.2 C hRC] at hn'
    apply hescape
    intro x hx
    exact hn' (show (⟨x,hx.2⟩ : Y) ∈ A.subgroupOf Y from hx.1)
  have hBR : B.subgroupOf Y ≤ normalizer ((residual H).subgroupOf Y : Set Y) := by
    rw [←subgroupOf_normalizer_eq hRY]
    exact comap_mono ((c.right_le.trans inf_le_right).trans (le_normalizer_residual H))
  have hBR' := (map_mono (f := f) hBR).trans (le_normalizer_map f)
  have hBA : B.subgroupOf Y ≤ normalizer (A.subgroupOf Y : Set Y) := by
    intro b hb
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (c.right_normalizes_left hb) (a : G)
  obtain ⟨F,_,_,_,_,⟨e⟩⟩ := c.left_equiv_units h.linear h.sylow_normalizes
  let : IsCyclic A := isCyclic_of_injective e.toMonoidHom e.injective
  let j : A.subgroupOf Y →* A := {
    toFun x := ⟨x.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y heq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : A => (a : G)) heq
  let : IsCyclic (A.subgroupOf Y) := isCyclic_of_injective j hj
  have ho : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have ho' : Odd (Nat.card (A.subgroupOf Y)) :=
    ho.of_dvd_nat (card_dvd_of_injective j hj)
  refine ⟨isCyclic_of_surjective (f.subgroupMap (A.subgroupOf Y))
    (f.subgroupMap_surjective _),ho'.of_dvd_nat (card_map_dvd _ f),
    (map_mono hBA).trans (le_normalizer_map f),he,?_,?_⟩
  · intro hz
    exact he (hz ▸ bot_le)
  · intro hDB
    exact he (hDB.trans hBR')

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

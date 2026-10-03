module
public import Stellmacher.SectionNine.DistanceOneVstarThreeAction
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Mathlib.GroupTheory.Nilpotent

/-!
# The distance-one Vstar lies in the terminal residual

In the original ambient Section Nine context, the explicit distance-one
faithful and local conclusions imply that the exact Vstar is contained in
the terminal two-residual. This supplies the containment needed to turn
residual invariance of a selected subgroup of Vstar into normality inside
that residual.

Choose the actual order-three residual actor supplied by the proved Vstar
action theorem. Vstar has order32, so coprime action decomposes it into its
commutator with the cyclic actor and its actor centralizer. The commutator
lies in the terminal residual by residual normality, and the centralizer
lies in the order-two center of Vstar. Thus the intersection of Vstar with
the residual, together with the center of Vstar, generates Vstar.

A subgroup K of this two-group cannot be a proper supplement to its center.
The orders32 and2 first ensure K is nontrivial. Its center is then nontrivial
by the finite p-group center theorem. Since the center of K centralizes both
K and the center of Vstar, it is central in Vstar. The order-two center of
Vstar is therefore contained in K, so K is all of Vstar.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), p.48, the residual
normality step for the chosen elementary subgroup. The proof retains the
actual ambient residual and uses no assumed residual structure or action.
-/

open scoped Pointwise
namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven

private theorem eq_top_of_sup_center {V : Type*} [Group V] [Finite V]
    (hp : IsPGroup 2 V) (hcard : Nat.card V = 32)
    (hzcard : Nat.card (Subgroup.center V) = 2) (K : Subgroup V)
    (hgen : K ⊔ Subgroup.center V = ⊤) : K = ⊤ := by
  have hK : Nontrivial K := by
    by_contra hn
    let : Subsingleton K := not_nontrivial_iff_subsingleton.mp hn
    have ht : K = ⊥ := Subgroup.eq_bot_of_subsingleton K
    have hztop : Subgroup.center V = ⊤ := by simpa [ht] using hgen
    rw [hztop, Subgroup.card_top, hcard] at hzcard
    omega
  let := hK
  let : Nontrivial (Subgroup.center K) := (hp.to_subgroup K).center_nontrivial
  obtain ⟨z, hzne⟩ := exists_ne (1 : Subgroup.center K)
  have hzcentral : (z : V) ∈ Subgroup.center V := by
    apply Subgroup.mem_center_iff.mpr
    intro v
    have hle : K ⊔ Subgroup.center V ≤ Subgroup.centralizer ({(z : V)} : Set V) := by
      apply sup_le
      · intro k hk
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.property ⟨k, hk⟩)
      · intro k hk
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_center_iff.mp hk (z : V)).symm
    rw [hgen] at hle
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top v))
  have hzle : Subgroup.center V ≤ K := by
    obtain ⟨other, hother, hall⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center V)).mp hzcard
    have hzneq : (⟨(z : V), hzcentral⟩ : Subgroup.center V) ≠ 1 := by
      intro heq
      apply hzne
      exact Subtype.val_injective (Subtype.val_injective
        (congrArg (fun q : Subgroup.center V => (q : V)) heq))
    intro v hv
    by_cases heq : (⟨v, hv⟩ : Subgroup.center V) = 1
    · have hvone : v = 1 := congrArg Subtype.val heq
      simp [hvone]
    · have heqz := (hall _ heq).trans (hall _ hzneq).symm
      have hvz : v = (z : V) := congrArg Subtype.val heqz
      exact hvz.symm ▸ z.val.property
  rwa [sup_eq_left.mpr hzle] at hgen

universe u
/-- The actual terminal residual contains the exact Vstar in the
ambient-retaining distance-one configuration. -/
public theorem distance_one_vstar_le_terminal_residual
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext) :
    conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') ≤ EAt ctx.Γ ctx.criticalPath.a' := by
  classical
  let V := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  have hEV : E ≤ terminal := by
    simpa only [E, terminal, EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def,
      GAt, CosetGraphContext.stabilizer] using SevenSix.twoResidualIn_le terminal
  have hEn : terminal ≤ Subgroup.normalizer (E : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hEV).mp
    simpa only [E, terminal, EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def,
      GAt, CosetGraphContext.stabilizer] using SevenSix.twoResidualIn_normal terminal
  have hn := (distance_one_vstar_containments ctx.toLocalContext hlength).1
  change NormalIn V terminal at hn
  have hVn : terminal ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hn.1).mp hn.2
  have hVcard : Nat.card V = 32 := distance_one_vstar_card ctx.toLocalContext hlocal
  have hp : IsPGroup 2 V := IsPGroup.of_card (n := 5) hVcard
  let : Group.IsNilpotent V := hp.isNilpotent
  obtain ⟨hz, hzcard, ⟨actor, hactor, horder⟩, _⟩ :=
    distance_one_vstar_three_action ctx hlength hfaithful hlocal
  change CenterAmbient V = ZAt ctx.Γ ctx.criticalPath.a' at hz
  have hcentral := (distance_one_vstar_residual_centralizer
    ctx hlength hfaithful hlocal hz).2 actor hactor horder
  let C := Subgroup.zpowers actor
  have hCE : C ≤ E := Subgroup.zpowers_le.mpr hactor
  have hCT : C ≤ terminal := hCE.trans hEV
  have hCcard : Nat.card C = 3 := by rw [Nat.card_zpowers]; exact horder
  have hcop : Nat.Coprime (Nat.card C) (Nat.card V) := by
    rw [hCcard, hVcard]
    decide
  have hdecomp := Subgroup.eq_commutator_sup_centralizer_of_solvable_coprime
    V C (hCT.trans hVn) inferInstance hcop
  have hcommE : ⁅V, C⁆ ≤ E := by
    apply (Subgroup.commutator_mono le_rfl hCE).trans
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hn.1.trans hEn)
  have hfix : V ⊓ Subgroup.centralizer (C : Set G) ≤ CenterAmbient V := by
    intro v hv
    rw [hz]
    exact hcentral v hv.1 (Subgroup.mem_centralizer_iff.mp hv.2 actor
      (Subgroup.mem_zpowers actor))
  have hVZ : V = (V ⊓ E) ⊔ CenterAmbient V := by
    apply le_antisymm
    · apply hdecomp.le.trans
      exact sup_le (le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hCT.trans hVn)) hcommE |>.trans le_sup_left) (hfix.trans le_sup_right)
    · exact sup_le inf_le_left (Subgroup.map_subtype_le (Subgroup.center V))
  have hnative : (E.subgroupOf V) ⊔ Subgroup.center V = ⊤ := by
    apply Subgroup.map_injective V.subtype_injective
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, V.range_subtype,
      Subgroup.subgroupOf_map_subtype, inf_comm E V]
    change (V ⊓ E) ⊔ CenterAmbient V = V
    exact hVZ.symm
  have hzcardNative : Nat.card (Subgroup.center V) = 2 := by
    rw [← Subgroup.card_map_of_injective V.subtype_injective]
    change Nat.card (CenterAmbient V) = 2
    rw [hz]
    exact hzcard
  have htop := eq_top_of_sup_center hp hVcard hzcardNative (E.subgroupOf V) hnative
  intro v hv
  exact (show (⟨v, hv⟩ : V) ∈ E.subgroupOf V by rw [htop]; trivial)

end Stellmacher.SectionNine

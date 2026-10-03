module
public import Stellmacher.SectionNine.DistanceOneVstarFactorSwap
public import Theory.GroupTheory.WreathTwoSylowCentralizer

/-!
# The Sylow centralizer of the exact distance-one Vstar

The faithful and local distance-one conclusions place the centralizer of the
actual Vstar inside Vstar joined with the initial elementary center Z_a.
This supplies the Sylow geometry needed to exclude a terminal core that
preserves both quaternion factors, before selecting the elementary eight.

Project the initial vertex group onto its actual SL2(2) wreath C2 quotient.
The edge Sylow maps to a Sylow two-subgroup. Vstar has order32, and its
intersection with the kernel Z_a is exactly the order8 seed Z_a intersect Q_d,
so its quotient image has order4. The established dihedral Sylow centralizer
bound puts each centralizing element's image in that image of Vstar. Lifting
back through the actual quotient map gives membership in Vstar Z_a.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), pp.47–48. The proof
retains the original graph groups and exact conjugate closure; it imposes no
extra factor-action or Sylow-model assumption on the application.
-/

open scoped Pointwise
namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven

/-- In the actual first wreath quotient, the image of Vstar contains its
Sylow centralizer; lifting gives this precise ambient containment. -/
public theorem distance_one_vstar_sylow_centralizer_le_join
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx)
    (hlocal : DistanceOneLocalConclusion ctx) :
    let V := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    T ⊓ Subgroup.centralizer (V : Set G) ≤ V ⊔ ZAt ctx.Γ ctx.criticalPath.a := by
  classical
  let V := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  let first := GAt ctx.Γ ctx.criticalPath.a
  let Za := ZAt ctx.Γ ctx.criticalPath.a
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  change T ⊓ Subgroup.centralizer (V : Set G) ≤ V ⊔ Za
  have hseedcard := (distance_one_seed_data ctx hlength hfaithful hlocal).1
  have hcont := distance_one_vstar_containments ctx hlength
  have hVT : V ≤ T := hcont.2.2.1
  have hVfirst : V ≤ first := hcont.2.2.2.trans inf_le_left
  obtain ⟨hTfirst, sylow, hTsylow⟩ :=
    (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  obtain ⟨f, hf, hker⟩ := hlocal.1
  have hker' : f.ker = Za.subgroupOf first := by rw [hker, hlocal.2.2.2.1]
  have hseed : Za ⊓ Q ≤ V := by
    intro x hx
    exact Subgroup.subset_closure ⟨1, ⟨x, hx⟩, by simp⟩
  have hinf : Za ⊓ V = Za ⊓ Q :=
    le_antisymm (inf_le_inf_left Za hcont.2.1) (le_inf inf_le_left hseed)
  let V0 := V.subgroupOf first
  let imageV := V0.map f
  let imageT := sylow.mapSurjective hf
  have hV0card : Nat.card V0 = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVfirst).toEquiv]
    exact distance_one_vstar_card ctx hlocal
  have hkerVcard : Nat.card (f.ker ⊓ V0 : Subgroup first) = 8 := by
    rw [hker']
    change Nat.card ((Za ⊓ V).subgroupOf first) = 8
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show Za ⊓ V ≤ first from inf_le_right.trans hVfirst)).toEquiv, hinf]
    exact hseedcard
  have himagecard : Nat.card imageV = 4 := by
    have hh := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup first)
      (f.ker ⊓ V0) V0 bot_le inf_le_right
    simp only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right,
      Subgroup.relIndex_ker] at hh
    rw [hkerVcard, hV0card] at hh
    change 8 * Nat.card imageV = 32 at hh
    omega
  have hV0sylow : V0 ≤ (sylow : Subgroup first) := by
    intro x hx
    have hTx : (x : G) ∈ T := hVT hx
    rw [← hTsylow] at hTx
    obtain ⟨y, hy, hxy⟩ := hTx
    have heq : y = x := Subtype.ext hxy
    exact heq ▸ hy
  have himagele : imageV ≤ (imageT : Subgroup _) := Subgroup.map_mono hV0sylow
  have hbound := (wreath_two_sylow_centralizer_le_of_card_ge_four
    imageT imageV himagele (by rw [himagecard])).1
  intro x hx
  let xx : first := ⟨x, hTfirst hx.1⟩
  have hxImage : f xx ∈ (imageT : Subgroup _) := by
    apply Subgroup.mem_map_of_mem
    have hTx := hx.1
    rw [← hTsylow] at hTx
    obtain ⟨y, hy, hyx⟩ := hTx
    exact (show y = xx from Subtype.ext hyx) ▸ hy
  have hxcentral : f xx ∈ Subgroup.centralizer (imageV : Set _) := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    apply congrArg f
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 v hv)
  obtain ⟨v, hv, hvx⟩ := hbound ⟨hxImage, hxcentral⟩
  have hdiff : v⁻¹ * xx ∈ f.ker := by
    change f (v⁻¹ * xx) = 1
    rw [map_mul, map_inv, hvx, inv_mul_cancel]
  rw [hker'] at hdiff
  have hvV : (v : G) ∈ V := hv
  have hdZa : (v : G)⁻¹ * x ∈ Za := hdiff
  have hh := (V ⊔ Za).mul_mem (Subgroup.mem_sup_left hvV) (Subgroup.mem_sup_right hdZa)
  simpa using hh
end Stellmacher.SectionNine

module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.Local
public import Theory.Mathieu.M22.Properties.FixedHexads

/-!
# Reduction of the M₂₂ intersection to its hexad local subgroup

The literal inner action determines a unique involution of L. The supplied
Sylow subgroup of H meets the component L in a Sylow subgroup; transporting
it to M₂₂ places it in the centralizer of that involution and hence in its
fixed-hexad stabilizer. Subnormality is used inside H throughout.

The remaining concrete calculation must construct a characteristic-two local
overgroup containing S and the whole hexad stabilizer, and exclude escaping
chi-zero blocks in it. The exact block decomposition then forces that local
group into M. Ordinary maximality of the hexad stabilizer finishes the equality.
`mathieuTwentyTwo_intersection_of_hexadLocals` is only this conditional assembly:
its maximality and local-overgroup premises are still separate obligations.
No assumption that S normalizes L is made.

Source: Aschbacher–Smith, 1.1.5(3)(f) and 2.3.9(7)(f), combined manuscript
of 1 March 2004, printed pp.502 and 525–526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Sporadic.Mathieu
open scoped Pointwise
variable {G : Type*} [Group G]

private theorem center_eq_bot_of_m22 {L : Subgroup G} (e : L ≃* M22) :
    center L = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have he : e x ∈ center M22 := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a, rfl⟩ := e.surjective y
    simpa using congrArg e (mem_center_iff.mp hx a)
  rw [m22_center_eq_bot, mem_bot] at he
  exact e.injective (he.trans (map_one e).symm)

/-- The given inner action has a unique involution projection in the concrete M₂₂ case. -/
theorem mathieuTwentyTwo_projection
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    ∃! t : L, IsConjugationProjection L z t ∧ orderOf t = 2 :=
  h.exists_unique_projection (center_eq_bot_of_m22 e) α hα hinner

/-- The image of the actual component Sylow subgroup centralizes the projected
involution and preserves its fixed hexad. This uses only relative subnormality. -/
theorem mathieuTwentyTwo_projection_sylow
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22) {t : L}
    (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    m22FixedPoints (e t) ∈ m22Blocks ∧
    ∃ R : Sylow 2 M22,
      (R : Subgroup M22) =
        (((S : Subgroup H).map H.subtype).subgroupOf L).map e.toMonoidHom ∧
      e t ∈ (R : Subgroup M22) ∧
      (R : Subgroup M22) ≤ centralizer ({e t} : Set M22) ∧
      (R : Subgroup M22) ≤ MulAction.stabilizer M22 (m22FixedPoints (e t)) := by
  let := h.finite
  obtain ⟨P, hP⟩ := h.component_sylow
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hc : (R : Subgroup M22) ≤ centralizer ({e t} : Set M22) := by
    rintro x ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he := mem_centralizer_iff.mp (h.projection_centralizes_sylow ht P hP) y hy
    simpa using congrArg e he
  refine ⟨m22FixedPoints_mem_blocks (e t) (by simpa using ht2), R, ?_, ?_, hc,
    hc.trans (m22_centralizer_le_fixedPoints_stabilizer (e t))⟩
  · change (P : Subgroup L).map e.toMonoidHom = _
    rw [hP]
  · exact ⟨t, h.projection_mem_sylow ht ht2 P hP, rfl⟩

/-- A local overgroup needed for the block calculation. The containment is in
this auxiliary group; containment in M must be deduced from the block condition. -/
structure MathieuTwentyTwoHexadLocal (L S : Subgroup G) (e : L ≃* M22) (t : L) where
  localGroup : Subgroup G
  within : localGroup ≤ L ⊔ S
  even : localGroup ∈ Chapter1.HeOver G (S : Set G)
  contains : ((MulAction.stabilizer M22 (m22FixedPoints (e t))).comap
    e.toMonoidHom).map L.subtype ≤ localGroup

/-- The full block decomposition forces the hexad stabilizer into the intersection
once every allowed moved block of the local overgroup is already in M. -/
theorem MathieuTwentyTwoHexadLocal.stabilizer_le_intersection
    {L M S : Subgroup G} {e : L ≃* M22} {t : L}
    (d : MathieuTwentyTwoHexadLocal L S e t)
    (hblocks : LocalBlockGeneration L M S)
    (ho : BlockObstruction M S d.localGroup) :
    MulAction.stabilizer M22 (m22FixedPoints (e t)) ≤
      (M.subgroupOf L).map e.toMonoidHom := by
  have hKM : d.localGroup ≤ M := by
    by_contra hn
    obtain ⟨blocks⟩ := hblocks d.localGroup d.within d.even hn
    obtain ⟨B, ha, hm, hc⟩ := blocks.exists_escapingBlock hn
    exact hm (ho B ha hc)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  apply hKM
  apply d.contains
  refine ⟨e.symm x, ?_, rfl⟩
  change e (e.symm x) ∈ MulAction.stabilizer M22 (m22FixedPoints (e t))
  simpa using hx

/-- Conditional assembly of the concrete M₂₂ intersection. Both the ordinary
maximality and the local block-obstruction witnesses must be supplied. -/
theorem mathieuTwentyTwo_intersection_of_hexadLocals
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range)
    (hmax : ∀ B ∈ m22Blocks, IsCoatom (MulAction.stabilizer M22 B))
    (hloc : ∀ t : L, IsConjugationProjection L z t → orderOf t = 2 →
      ∃ d : MathieuTwentyTwoHexadLocal L ((S : Subgroup H).map H.subtype) e t,
        BlockObstruction M ((S : Subgroup H).map H.subtype) d.localGroup) :
    ∃ B ∈ m22Blocks,
      (M.subgroupOf L).map e.toMonoidHom = MulAction.stabilizer M22 B := by
  obtain ⟨t, ht, _⟩ := mathieuTwentyTwo_projection h e α hα hinner
  obtain ⟨d, hd⟩ := hloc t ht.1 ht.2
  have hB := (mathieuTwentyTwo_projection_sylow h e ht.1 ht.2).1
  have hp : (M.subgroupOf L).map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply h.outside
    apply subgroupOf_eq_top.mp
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa using he
  exact ⟨m22FixedPoints (e t), hB,
    ((hmax _ hB).le_iff_eq hp).mp (d.stabilizer_le_intersection h.blocks hd)⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement

end

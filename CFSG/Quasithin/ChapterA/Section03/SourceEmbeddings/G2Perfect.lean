module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import Theory.AtlasPort.LinearGroups.G2.PerfectSubgroups

/-!
# Odd-rank-two local components in binary G₂

A perfect subgroup of odd-prime rank at least two cannot lie in either
root parabolic of G₂. Adjoining the full Sylow intersection to a local
C-component therefore gives the containing component. C-component
minimality then gives equality. The smaller component need not be
quasisimple; this is the distinction needed for the marked radical in
the proof of 1.3.8.

Source: Aschbacher–Smith A.3.12, printed pp.47–48, and 1.3.8, p.513.
The concrete parabolic calculation is in `Atlas.G2.PerfectSubgroups`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

/-- Odd rank replaces the unavailable quasisimplicity premise on the
smaller local component in the binary G₂ containing branch. -/
theorem eq_of_g2_containing_component_of_odd_rank
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : 2 ≤ primeRank p B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (e : L ≃* Atlas.G2.Model F) : B = L := by
  let := hB.perfect
  let b := subgroupOfEquivOfLe (show B ≤ B ⊔ T from le_sup_left)
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := b.toMonoidHom) b.surjective
  obtain ⟨S, _, hlocal⟩ := exists_local_sylow_restriction T hB hBL hL.subnormal
  let J := B.subgroupOf L ⊔ (S : Subgroup L)
  let f : B →* Atlas.G2.Model F := e.toMonoidHom.comp (inclusion hBL)
  have hf : Function.Injective f := e.injective.comp (inclusion_injective hBL)
  have him : f.range ≤ J.map e.toMonoidHom := by
    rintro _ ⟨x, rfl⟩
    exact mem_map_of_mem e.toMonoidHom
      ((show B.subgroupOf L ≤ J from le_sup_left) x.property)
  have hj := Atlas.G2.PerfectSubgroups.perfect_odd_rank_two_sylow_overgroup_eq_top
    ho hr hF (S.mapSurjective e.surjective) (J.map e.toMonoidHom)
    (map_mono le_sup_right) f hf him
  have htop : J = ⊤ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using hj
  change ((B.subgroupOf L).subgroupOf J).IsCComponent at hlocal
  rw [htop] at hlocal
  have hC : (B.subgroupOf L).IsCComponent := by
    have h := hlocal.map_subtype (show (⊤ : Subgroup L).IsSubnormal from .top)
    simpa only [map_subgroupOf_eq_of_le le_top] using h
  exact le_antisymm hBL (subgroupOf_eq_top.mp (hL.eq_top_of_isCComponent hC))

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

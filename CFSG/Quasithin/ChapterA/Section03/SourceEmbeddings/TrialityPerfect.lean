module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import Theory.SpecificGroups.Triality.PerfectSylowOvergroups

/-!
# Odd-rank-two local components in the genuine binary triality carrier

The local component and the full Sylow intersection generate the containing
triality component: otherwise the perfect subgroup would lie in a root
parabolic of odd-prime rank at most one. C-component minimality then gives
equality. The smaller component need not be quasisimple.

Source: Aschbacher–Smith A.3.12, printed pp.47–48, used in 1.3.8, p.513.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

/-- A local C-component of odd-prime rank two cannot be properly contained
in a binary triality C-component, including the binary endpoint. -/
theorem eq_of_triality_containing_component_of_odd_rank
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : 2 ≤ primeRank p B)
    {n : ℕ} (hn : 0 < n) (e : L ≃* Triality.Standard.BinaryCarrier n hn) : B = L := by
  let := hB.perfect
  let b := subgroupOfEquivOfLe (show B ≤ B ⊔ T from le_sup_left)
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := b.toMonoidHom) b.surjective
  obtain ⟨S, _, hlocal⟩ := exists_local_sylow_restriction T hB hBL hL.subnormal
  let J := B.subgroupOf L ⊔ (S : Subgroup L)
  let f := e.toMonoidHom.comp (inclusion hBL)
  have him : f.range ≤ J.map e.toMonoidHom := by
    rintro _ ⟨x,rfl⟩
    exact mem_map_of_mem e.toMonoidHom
      ((show B.subgroupOf L ≤ J from le_sup_left) x.property)
  have hj := Triality.Standard.PerfectSylowOvergroups.eq_top_of_perfect_odd_rank_two
    n hn (S.mapSurjective e.surjective) (J.map e.toMonoidHom)
    (map_mono le_sup_right) f (e.injective.comp (inclusion_injective hBL)) him ho hr
  have htop : J = ⊤ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using hj
  change ((B.subgroupOf L).subgroupOf J).IsCComponent at hlocal
  rw [htop] at hlocal
  have hC : (B.subgroupOf L).IsCComponent := by
    have h := hlocal.map_subtype (show (⊤ : Subgroup L).IsSubnormal from .top)
    simpa only [map_subgroupOf_eq_of_le le_top] using h
  exact le_antisymm hBL (subgroupOf_eq_top.mp (hL.eq_top_of_isCComponent hC))

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

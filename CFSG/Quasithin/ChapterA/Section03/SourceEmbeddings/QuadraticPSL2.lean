module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import Theory.SpecificGroups.PSL2.QuadraticNonsolvableSylowOvergroups

/-!
# A.3.12 inside PSL₂ over a quadratic prime field

Intersect the original full Sylow with the containing component and adjoin
that intersection to the smaller local C-component. A proper smaller
component gives a proper nonsolvable join. Dickson and the full Sylow order
exclude all but the prime-field PSL₂ and PGL₂ models. Their nontrivial
perfect subnormal subgroups are precisely PSL₂(p), with p greater than three.

The resulting isomorphism is for the original smaller subgroup B, via its
actual inclusion in the join. The ambient two-core quotient application
preserves the maps used by 1.2.4 and C.5.12–13.

Source: Aschbacher–Smith A.3.12(8), printed pp.47–48; C.5.12–13, p.163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The proper quadratic-field branch constructs the prime-field model
for the original smaller local C-component. -/
theorem proper_quadraticPSL2_models
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hne : B ≠ L) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL L 2 (p ^ 2)) :
    3 < p ∧ ClassicalGroup.IsPSL B 2 p := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_subnormal L hL.subnormal
  let J := B ⊔ (S : Subgroup L).map L.subtype
  have hST : (S : Subgroup L).map L.subtype ≤ (T : Subgroup G) := by
    rw [hS, subgroupOf_map_subtype]
    exact inf_le_left
  have hJL : J ≤ L := sup_le hBL (map_subtype_le _)
  have hBJ : (B.subgroupOf J).IsCComponent :=
    hB.subgroupOf_of_le le_sup_left (sup_le le_sup_left (hST.trans le_sup_right))
  have hJne : J ≠ L := by
    intro he
    rw [he] at hBJ
    exact hne (le_antisymm hBL (subgroupOf_eq_top.mp (hL.eq_top_of_isCComponent hBJ)))
  let D := (J.subgroupOf L).map e.toMonoidHom
  let i : J ≃* D := (subgroupOfEquivOfLe hJL).symm.trans
    ((J.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective)
  have hDne : D ≠ ⊤ := by
    intro he
    have ht : J.subgroupOf L = ⊤ := by
      apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
      rw [map_top_of_surjective _ e.surjective]
      exact he
    exact hJne (le_antisymm hJL (subgroupOf_eq_top.mp ht))
  have hDns : ¬ Group.IsSolvable D := by
    intro hs
    let := hs
    let : Group.IsSolvable J :=
      Group.isSolvable_of_isSolvable_injective (f := i.toMonoidHom) i.injective
    exact hBJ.not_isSolvable inferInstance
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hSD : (S' : Subgroup _) ≤ D := map_mono (by
    intro s hs
    exact (show (S : Subgroup L).map L.subtype ≤ J from le_sup_right)
      (mem_map_of_mem L.subtype hs))
  have hDmodels := Theory.PSL2.quadratic_nonsolvable_proper_sylow_models
    ho hF S' D hSD hDne hDns
  obtain ⟨hgt, ⟨c⟩⟩ := Theory.PSL2.cComponent_prime_linear_model ho
    ((B.subgroupOf J).map i.toMonoidHom) (hBJ.map_equiv i) hDmodels
  let b : B ≃* BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField p 1) :=
    ((subgroupOfEquivOfLe (show B ≤ J from le_sup_left)).symm.trans
      ((B.subgroupOf J).equivMapOfInjective i.toMonoidHom i.injective)).trans c
  exact ⟨hgt, GaloisField p 1, inferInstance, inferInstance,
    by simpa using GaloisField.card p 1 (by decide), ⟨b⟩⟩

/-- The actual pair satisfies A.3.12(1) or the quadratic-field part of (8). -/
theorem embedding_of_quadraticPSL2
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL L 2 (p ^ 2)) : A312Embedding B L := by
  by_cases he : B = L
  · exact .one he
  obtain ⟨hgt, hsmall⟩ := proper_quadraticPSL2_models T hB hL hBL he hp ho hmodel
  exact .eight (.inl ⟨p, hp, ho, hgt, hsmall, hmodel⟩)

/-- The quadratic-field result on the exact images in G/O₂(G). -/
theorem twoCore_embedding_of_quadraticPSL2
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ Chapter1.L G T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL (L.map (QuotientGroup.mk' (pCore 2 G))) 2 (p ^ 2)) :
    A312Embedding (B.map (QuotientGroup.mk' (pCore 2 G)))
      (L.map (QuotientGroup.mk' (pCore 2 G))) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  apply embedding_of_quadraticPSL2
    (T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G)))
    ?_ (hL.map_quotient (pCore 2 G)) (map_mono hBL) hp ho hmodel
  simpa only [Sylow.coe_mapSurjective] using
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSubgroups
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectSubgroups

/-!
# Exhaustion inside binary rank-two containing components

A selected local C-component of odd prime rank at least two cannot lie in
one of the rank-one parabolic residuals of PSL₃ or Sp₄. The actual full Sylow
subgroup in a containing component therefore generates the entire containing
model together with it. The local C-component property then forces equality.
The final applications retain the literal images modulo the ambient two-core;
no quasisimplicity of the smaller quotient image is assumed.

Source: Aschbacher--Smith 1.2.8(4), in the actual diagram case of 14.2.9,
printed pp.506--507 and 983.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem local_perfect {T B : Subgroup G} (hB : B ∈ localCComponents T) :
    Group.IsPerfect B := by
  let := hB.perfect
  let e := subgroupOfEquivOfLe (show B ≤ B ⊔ T from le_sup_left)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

private theorem eq_of_join_full_sylow_eq_top
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (htop : ∀ S : Sylow 2 L, B.subgroupOf L ⊔ (S : Subgroup L) = ⊤) : B = L := by
  obtain ⟨S,_,hlocal⟩ := exists_local_sylow_restriction T hB hBL hL.subnormal
  change ((B.subgroupOf L).subgroupOf (B.subgroupOf L ⊔ (S : Subgroup L))).IsCComponent at hlocal
  rw [htop S] at hlocal
  have hC : (B.subgroupOf L).IsCComponent := by
    have h := hlocal.map_subtype (show (⊤ : Subgroup L).IsSubnormal from .top)
    simpa only [map_subgroupOf_eq_of_le le_top] using h
  exact le_antisymm hBL (subgroupOf_eq_top.mp (hL.eq_top_of_isCComponent hC))

theorem eq_of_linear_three_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : 2 ≤ primeRank p B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : L ≃* PSL(3,F)) : B = L := by
  let := local_perfect hB
  apply eq_of_join_full_sylow_eq_top T hB hL hBL
  intro S
  let J := B.subgroupOf L ⊔ (S : Subgroup L)
  let f : B →* PSL(3,F) := e.toMonoidHom.comp (inclusion hBL)
  have hf : Function.Injective f := e.injective.comp (inclusion_injective hBL)
  have him : f.range ≤ J.map e.toMonoidHom := by
    rintro _ ⟨b,rfl⟩
    exact mem_map_of_mem e.toMonoidHom
      ((show B.subgroupOf L ≤ J from le_sup_left) b.property)
  have hj := Matrix.PSL3.LinearThree.PerfectSubgroups.perfect_odd_rank_two_sylow_overgroup_eq_top
    F ho hr hn hF (S.mapSurjective e.surjective) (J.map e.toMonoidHom)
    (map_mono le_sup_right) f hf him
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using hj

theorem eq_of_symplectic_four_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : 2 ≤ primeRank p B)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : L ≃* Theory.SpecificGroups.SymplecticFour.Sp F) : B = L := by
  let := local_perfect hB
  apply eq_of_join_full_sylow_eq_top T hB hL hBL
  intro S
  let J := B.subgroupOf L ⊔ (S : Subgroup L)
  let f : B →* Theory.SpecificGroups.SymplecticFour.Sp F := e.toMonoidHom.comp (inclusion hBL)
  have hf : Function.Injective f := e.injective.comp (inclusion_injective hBL)
  have him : f.range ≤ J.map e.toMonoidHom := by
    rintro _ ⟨b,rfl⟩
    exact mem_map_of_mem e.toMonoidHom
      ((show B.subgroupOf L ≤ J from le_sup_left) b.property)
  have hj := Theory.SpecificGroups.SymplecticFour.perfect_odd_rank_two_sylow_overgroup_eq_top
    ho hr hF (S.mapSurjective e.surjective) (J.map e.toMonoidHom)
    (map_mono le_sup_right) f hf him
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using hj

theorem twoCore_images_eq_of_linear_three_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ Chapter1.L G T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hr : 2 ≤ primeRank p (B.map (QuotientGroup.mk' (pCore 2 G))))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : L.map (QuotientGroup.mk' (pCore 2 G)) ≃* PSL(3,F)) :
    B.map (QuotientGroup.mk' (pCore 2 G)) = L.map (QuotientGroup.mk' (pCore 2 G)) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  apply eq_of_linear_three_containing_component
    (T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G)))
    ?_ (hL.map_quotient (pCore 2 G)) (map_mono hBL) ho hr hn hF e
  simpa only [Sylow.coe_mapSurjective] using
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB

theorem twoCore_images_eq_of_symplectic_four_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ Chapter1.L G T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hr : 2 ≤ primeRank p (B.map (QuotientGroup.mk' (pCore 2 G))))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : L.map (QuotientGroup.mk' (pCore 2 G)) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    B.map (QuotientGroup.mk' (pCore 2 G)) = L.map (QuotientGroup.mk' (pCore 2 G)) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  apply eq_of_symplectic_four_containing_component
    (T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G)))
    ?_ (hL.map_quotient (pCore 2 G)) (map_mono hBL) ho hr hF e
  simpa only [Sylow.coe_mapSurjective] using
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

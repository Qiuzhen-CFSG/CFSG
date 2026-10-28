module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import Theory.SpecificGroups.SL3.BinaryPerfectSylowOvergroups

/-!
# Non-enlargement in the genuine binary SL₃ covers

The actual image of the smaller local component in SL₃ is perfect and has
the source odd-prime rank two. The full-Sylow overgroup theorem for the
cover makes its join with the Sylow intersection the whole containing
component. C-component minimality then gives equality.

Source: Aschbacher–Smith A.3.12, pp.47–48, used in 1.3.8, p.513.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

/-- The actual special linear cover cannot contain a proper marked local
C-component of p-rank two for p > 3. -/
theorem eq_of_binary_sl3_containing_component_of_large_odd_rank
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (ho : Odd p) (hr : 2 ≤ primeRank p B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) (e : L ≃* SL(3,F)) : B = L := by
  let := hL.perfect
  let : Group.IsPerfect SL(3,F) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let := hB.perfect
  let b := subgroupOfEquivOfLe (show B ≤ B ⊔ T from le_sup_left)
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := b.toMonoidHom) b.surjective
  obtain ⟨S, _, hlocal⟩ := exists_local_sylow_restriction T hB hBL hL.subnormal
  let J := B.subgroupOf L ⊔ (S : Subgroup L)
  let A := (B.subgroupOf L).map e.toMonoidHom
  let a := (subgroupOfEquivOfLe hBL).symm.trans (e.subgroupMap (B.subgroupOf L))
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := a.toMonoidHom) a.surjective
  have hra : 2 ≤ primeRank p A := (primeRank_equiv p a) ▸ hr
  have hj := Matrix.SL3.BinaryPerfectSylowOvergroups.eq_top_of_perfect_large_odd_rank_two
    F hp ho hn hF (S.mapSurjective e.surjective) (J.map e.toMonoidHom) A
    (map_mono le_sup_right) (map_mono le_sup_left) hra
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

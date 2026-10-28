module
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.Component
/-!
# The strict degree exclusion for the rank-one rows of G.9.3

The genuine binary SL₂ classifier gives degrees 2n (natural or Hermitian)
or 8 with n=3 (triple tensor), while the original actor has rank at most n.
Consequently the sharper isotropic bound dim I ≤ m+1 excludes every such
single-component row with n≥2. This is the rank-one part of the faithful-X
contradiction in Aschbacher--Smith G.11.7, printed pp.366–367.
-/
public section
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section09
universe u v
variable {G : Type u} [Group G] [Finite G]
 {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
 {C : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
 {A L : Subgroup G} {m : ℕ}
 {K : Type*} [Field K] [Finite K] [CharP K 2]
/-- An actual G.9 component with the isotropic degree bound is not a binary
SL₂ group. The original actor rank and genuine module alternatives suffice. -/
theorem ComponentHypothesis.not_rank_one_of_degree_le_rank_add_one
 (h : ComponentHypothesis C ρ A L L m)
 (hd : Module.finrank (ZMod 2) V ≤ m+1)
 (e : L ≃* SL(2,K)) (n : ℕ) (hn : 2 ≤ n) (hc : Nat.card K = 2^n) : False := by
  obtain ⟨hm,hcases⟩ := DefiningCharacteristic.rank_one_module_alternatives h e n hn hc
  rcases hcases with ⟨hdeg,_,_⟩ | ⟨s,hs,he,hdeg,_,_⟩ | ⟨he,hdeg,_,_⟩ <;> omega
end CFSG.Quasithin.ChapterG.Section09

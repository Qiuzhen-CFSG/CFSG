module
public import Theory.GroupTheory.QuasisimpleSylowOvergroup
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSubgroups
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectSubgroups
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Full-Sylow rigidity in the even rank-two targets

A quasisimple subgroup normalized by a full Sylow two-subgroup has no proper
enlargement to a binary PSL₃ central cover or binary Sp₄ when it has odd prime
rank two and two-group center. Restricting the target central quotient preserves
that odd rank; the actual image, together with the full target Sylow subgroup,
cannot lie in a proper parabolic. The central-supplement criterion then gives
equality in the original group. These are the even target rows of the source
non-enlargement argument, Aschbacher–Smith 2.5.6, printed p.554.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.EvenRankTwoSylowRigidity
variable {C F : Type*} [Group C] [Finite C] [IsQuasisimple C]
    [Field F] [Finite F]
variable (K : Subgroup C) [IsQuasisimple K] (hZ : IsPGroup 2 (center K))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : 2 ≤ primeRank p K)
    (P : Sylow 2 C) (hnorm : (P : Subgroup C) ≤ normalizer (K : Set C))

include hZ ho hr hnorm

theorem linear {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (e : C ⧸ center C ≃* PSL(3,F)) : K=⊤ := by
  let : CharP F 2 := SymplecticFour.EvenProjective.charTwo_of_card hF
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker ≤ center C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have him := odd_rank_subgroupMap_of_central_kernel f hk K hZ ho hr
  let : Group.IsPerfect (K.map f) := Group.IsPerfect.map f
  apply eq_top_of_central_image_sylow_overgroups K P hnorm f hf hk
  intro D hPD hKD
  apply Matrix.PSL3.LinearThree.PerfectSubgroups.perfect_odd_rank_two_sylow_overgroup_eq_top
    F ho him hn hF (P.mapSurjective hf) D hPD (K.map f).subtype (K.map f).subtype_injective
  simpa only [range_subtype] using hKD

theorem symplectic [CharP F 2] (hF : 2<Nat.card F)
    (e : C ≃* SymplecticFour.Sp F) : K=⊤ := by
  let f := e.toMonoidHom
  have hk : f.ker ≤ center C := by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact bot_le
  have him := odd_rank_subgroupMap_of_central_kernel f hk K hZ ho hr
  let : Group.IsPerfect (K.map f) := Group.IsPerfect.map f
  apply eq_top_of_central_image_sylow_overgroups K P hnorm f e.surjective hk
  intro D hPD hKD
  apply SymplecticFour.perfect_odd_rank_two_sylow_overgroup_eq_top
    ho him hF (P.mapSurjective e.surjective) D hPD (K.map f).subtype (K.map f).subtype_injective
  simpa only [range_subtype] using hKD

end Theory.SpecificGroups.Classical.EvenRankTwoSylowRigidity

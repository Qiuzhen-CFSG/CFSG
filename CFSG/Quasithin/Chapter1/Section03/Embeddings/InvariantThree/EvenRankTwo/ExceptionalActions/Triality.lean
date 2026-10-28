module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.ExceptionalActions.PowerAction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Automizer
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.ExceptionalActions.TrialityPlacement
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage

/-!
# The genuine triality pair action

The concrete Borel geometry kills the inner factor on every subgroup of the
descended coroot torus. Actual inner–coefficient coverage then makes each
automorphism preserving the positive Sylow subgroup and the complement act
by one power of two on the complement. Transport along the same equivalence
used for placement controls the full pair automizer, not just its inner part.
The cubic coefficient action retains the order-three graph contribution.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528),
and Notation A.2.5, printed p.33. Only the genuine Standard D₄ graph-field
carrier and its elementary central quotient occur here.
-/

public section
noncomputable section

open Subgroup
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.OuterOdd
open Triality.Standard.CartanAction
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions

/-- Every inner pair stabilizer centralizes a complement in the genuine torus. -/
theorem triality_inner_kernel (P : Parameters) (hp : P.prime = 2)
    (B : Subgroup (Carrier P)) (hB : B ≤ torus P) :
    normalizer (unipotent P) ⊓ normalizer B ≤ centralizer (B : Set (Carrier P)) := by
  rw [(borelGeometry P hp).normalizer_eq]
  exact borel_kernel P hp (borelGeometry P hp) B hB

private theorem map_eq_of_mem_iff {G : Type*} [Group G] (H : Subgroup G)
    (a : MulAut G) (ha : ∀ x, a x ∈ H ↔ x ∈ H) : H.map a.toMonoidHom = H := by
  ext x
  obtain ⟨y, rfl⟩ := a.surjective x
  change a.toMonoidHom y ∈ H.map a.toMonoidHom ↔ a y ∈ H
  rw [mem_map_iff_mem a.injective, ha]

private theorem map_congr_aut {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (a : MulAut G) (K : Subgroup G) :
    (K.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom =
      (K.map a.toMonoidHom).map e.toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [MulAut.congr_apply]

variable {Q : Type*} [Group Q] [IsSimpleGroup Q] [Group.IsPerfect Q]

/-- Coverage and Borel geometry are discharged. The same coordinates for S
and R give a uniform coefficient-power formula for each member of the full
pair automizer, without a restriction on the prime dividing R. -/
theorem triality_pair_power_of_equiv (S R : Subgroup Q)
    (P : Parameters) (f : ℕ) (hf : 0 < f) (hq : P.q = 2 ^ f)
    (e : Q ≃* Carrier P)
    (hS : S.map e.toMonoidHom = unipotent P)
    (hR : R.map e.toMonoidHom ≤ torus P) :
    ∀ b ∈ pairAutomizer S R, ∃ k : ℕ, ∀ r : R, b r = r ^ (2 ^ k) := by
  have hP := P.eq_binaryParameters_of_q_eq f hf hq
  subst P
  let : IsSimpleGroup (BinaryCarrier f hf) := e.symm.isSimpleGroup
  let : Group.IsPerfect (BinaryCarrier f hf) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  intro b hb
  obtain ⟨a, he⟩ := pairRestriction_surjective S R ⟨b, hb⟩
  have hab (r : R) : (b r : Q) = a.val r :=
    (congrArg (fun c : pairAutomizer S R => (c.val r : Q)) he).symm
  have haS := map_eq_of_mem_iff S a.val a.property.1
  have haR := map_eq_of_mem_iff R a.val a.property.2
  have hu : (unipotent (binaryParameters f hf)).map
      (MulAut.congr e a.val).toMonoidHom = unipotent (binaryParameters f hf) := by
    rw [← hS, map_congr_aut, haS]
  have hr : (R.map e.toMonoidHom).map (MulAut.congr e a.val).toMonoidHom =
      R.map e.toMonoidHom := by
    rw [map_congr_aut, haR]
  obtain ⟨k, hk⟩ := normalizer_power_of_coverage _ rfl
    (borelGeometry_binary f hf) (Coverage.binary_inner_coefficient f hf)
    (R.map e.toMonoidHom) hR (MulAut.congr e a.val) hr hu
  refine ⟨k, fun r => Subtype.ext (e.injective ?_)⟩
  change e (b r : Q) = e ((r : Q) ^ (2 ^ k))
  rw [hab, map_pow]
  simpa [MulAut.congr_apply] using hk (e r) (mem_map_of_mem e.toMonoidHom r.property)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions

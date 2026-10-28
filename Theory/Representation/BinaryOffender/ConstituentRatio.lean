module
public import Theory.Representation.BinaryOffender.FaithfulConstituentStabilizer
public import Theory.Representation.BinaryOffender.SmallRatioTransport
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.GroupTheory.PrimeRankHom

/-!
# Quadratic bounds on a constituent stabilizer

A subgroup disjoint from a normal subgroup with trivial centralizer embeds
in its outer automorphism group. Its elementary rank is therefore bounded
by that outer rank. An elementary quadratic actor preserving a subspace
retains its rank inside the subspace stabilizer, while fixed codimension
can only decrease on the subspace.

These are the outer-actor and subspace steps in the Clifford reduction of
Aschbacher–Smith B.4.2–5 and D.3.6–9.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
 (ρ : Representation (ZMod 2) G V)

omit ρ in
theorem rank_le_outer_rank_of_disjoint (K A : Subgroup G) [K.Normal]
 (hA : IsElementaryTwo A) (hc : centralizer (K : Set G) = ⊥) (hd : A ⊓ K = ⊥) :
 rank A ≤ primeRank 2 (MulAut.Outer K) := by
 let : IsElementaryAbelian 2 A := hA.2
 let : CommGroup A := IsMulCommutative.instCommGroup
 let f : A →* G ⧸ K := (QuotientGroup.mk' K).comp A.subtype
 have hf : Function.Injective f := by
   apply (MonoidHom.ker_eq_bot_iff f).mp
   apply bot_unique
   intro a ha
   have hak : (a:G) ∈ K := (QuotientGroup.eq_one_iff _).mp ha
   have ha1 : (a:G) = 1 := by
     have hh : (a:G) ∈ A ⊓ K := ⟨a.property,hak⟩
     rwa [hd, mem_bot] at hh
   exact Subtype.ext ha1
 exact primeRank_ge_of_elementary_embedding
   (fun a:A => elemPow_eq_one_of_isElementaryAbelian (a:G) a.property |> Subtype.ext)
   hA.card_eq_two_pow_rank
   ((MulAut.outerAction K).comp f) ((MulAut.outerAction_injective K hc).comp hf)

theorem quadraticRatio_stabilizer_le_two [FiniteDimensional (ZMod 2) V]
 (W : Submodule (ZMod 2) V) (A : Subgroup G) (hA : IsElementaryTwo A)
 (hq : IsQuadratic ρ A) (hd : fixedCodim ρ A ≤ 2 * rank A)
 (hs : A ≤ subspaceStabilizer ρ W) :
 quadraticRatio (stabilizerRepresentation ρ W) ≤ 2 := by
 let H := subspaceStabilizer ρ W
 let B := A.subgroupOf H
 let : IsElementaryAbelian 2 A := hA.2
 have hB : IsElementaryTwo B := by
   refine ⟨?_, IsElementaryAbelian.subgroupOf hs⟩
   intro hb
   have hm := map_subgroupOf_eq_of_le hs
   rw [show A.subgroupOf H = ⊥ from hb, Subgroup.map_bot] at hm
   exact hA.1 hm.symm
 have hmap : B.map H.subtype = A := map_subgroupOf_eq_of_le hs
 have hr : rank B = rank A := by
   rw [rank, rank, Nat.card_congr (subgroupOfEquivOfLe hs).toEquiv]
 let J : Subrepresentation (ρ.comp H.subtype) :=
   ⟨W,fun h _ hw => (h.property _).2 hw⟩
 have hb : fixedCodim (ρ.comp H.subtype) B = fixedCodim ρ A := by
   unfold fixedCodim
   rw [fixedSpace_comp_map,hmap]
 exact (quadraticRatio_le_two_iff (stabilizerRepresentation ρ W)).mpr
   ⟨B,hB,(fun a ha b hb v => Subtype.ext (hq a.val ha b.val hb v.val)),by
     change fixedCodim J.toRepresentation B ≤ _
     exact (fixedCodim_subrepresentation_le (ρ.comp H.subtype) J B).trans (by rwa [hb,hr])⟩
end Representation.BinaryOffender

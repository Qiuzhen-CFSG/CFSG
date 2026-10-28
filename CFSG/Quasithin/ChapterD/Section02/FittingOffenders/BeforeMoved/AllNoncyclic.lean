module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.BeforeMoved.Source
public import CFSG.Quasithin.ChapterD.Section02.StarredConjugacy
public import Theory.GroupTheory.Fitting.NormalSylowFactorization
/-!
# The original all-noncyclic starred family has an odd kernel

For each original noncyclic starred actor, the source support argument puts
its normal closure inside the preimage of O₂(G/F(G)). Joining the original
family does the same for Jhat. Thus Jhat∩F(G) is an odd normal kernel and
supplements the intersection with every supplied Sylow two-subgroup.

No passage to a moved submodule occurs in this argument. In particular the
hypothesis quantifies over every original starred actor; existence of one
noncyclic actor is not substituted for it.
Source: Aschbacher–Smith D.2.14--19 and 15.1.2, printed pp.184--188, 1084.
-/
public section
namespace CFSG.Quasithin.ChapterD.BeforeMoved
open Subgroup Representation.BinaryOffender Theory.GroupTheory
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
  {H : Type*} [Group H] [Finite H] {C : GroupClass} (hH : IsSQTK C H)
  (f : H →* G) (honto : Function.Surjective f)
  (hf : Function.Injective ρ)
  (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥)
  (hnoncyclic : ∀ A ∈ QhatStar ρ, 1 < rank A)

include hH f honto hf hF hcore hnoncyclic in
/-- Joining the original noncyclic minimum actors gives a two-group image
modulo the Fitting subgroup. -/
theorem source_Jhat_le_twoCore_preimage :
    Jhat ρ ≤ (pCore 2 (G ⧸ fittingSubgroup G)).comap
      (QuotientGroup.mk' (fittingSubgroup G)) := by
  apply sSup_le
  intro A hA
  exact Subgroup.le_normalClosure.trans
    (source_normalClosure_le_twoCore_preimage ρ hH f honto hf hA
      (hnoncyclic A hA) hF hcore)

include hH f honto hf hF hcore hnoncyclic in
/-- The odd kernel is the literal intersection with the ambient Fitting
subgroup; it supplements the given Sylow intersection in Jhat. -/
theorem source_Jhat_odd_factorization (S : Sylow 2 G) :
    let K := Jhat ρ
    let P := K ⊓ fittingSubgroup G
    P.Normal ∧ Odd (Nat.card P) ∧
      K = P ⊔ (K ⊓ (S : Subgroup G)) ∧
      P.subgroupOf K ≤ fittingSubgroup K := by
  let K := Jhat ρ
  let P := K ⊓ fittingSubgroup G
  let : K.Normal := Jhat_normal ρ
  have hi : IsPGroup 2 (K.map (QuotientGroup.mk' (fittingSubgroup G))) :=
    pCore_isPGroup.to_le (map_le_iff_le_comap.mpr
      (source_Jhat_le_twoCore_preimage ρ hH f honto hf hF hcore hnoncyclic))
  exact ⟨inferInstance,
    (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot hcore).of_dvd_nat
      (card_dvd_of_le (show P ≤ fittingSubgroup G from inf_le_right)),
    eq_inf_sup_inf_sylow_of_quotient_image_isPGroup K (fittingSubgroup G) S hi,
    inf_fitting_subgroupOf_le K⟩
end CFSG.Quasithin.ChapterD.BeforeMoved

module
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Normal central subgroups in a group with trivial prime core

A normal subgroup A of a group with O_p(G)=1 that centralizes an overgroup K
is abelian and has order prime to p. Its inclusion in K therefore factors
through O_{p'}(Z(K)). This supplies the odd-central conclusion in
Aschbacher--Smith 14.1.17(3).
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem normal_le_primeTo_center_of_centralizes
    (A K : Subgroup G) [A.Normal]
    (hcore : pCore p G = ⊥) (hAK : A ≤ K) (hcentral : A ≤ centralizer (K : Set G)) :
    A ≤ (pPrimeCore p (center K)).map (K.subtype.comp (center K).subtype) := by
  let : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext
    ((hcentral a.property) b (hAK b.property)).symm⟩⟩
  have hAc : pCore p A = ⊥ := by
    rw [pCore_eq_comap_of_normal, hcore]
    exact (MonoidHom.ker_eq_bot_iff A.subtype).mpr A.subtype_injective
  have hodd : ¬ p ∣ Nat.card A := by
    have h := PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot hAc
      (⊤ : Subgroup A) (by rw [center_eq_top])
    simpa only [card_top] using h
  let f : A →* center K := (inclusion hAK).codRestrict (center K) (fun a => by
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext ((hcentral a.property) k k.property))
  have hf : Function.Injective f := fun a b h =>
    (inclusion_injective hAK) (congrArg Subtype.val h)
  have hcard : Nat.card f.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hle : f.range ≤ pPrimeCore p (center K) := le_sSup ⟨inferInstance, by
    rw [hcard]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hodd⟩
  intro a ha
  exact ⟨f ⟨a,ha⟩,hle ⟨⟨a,ha⟩,rfl⟩,rfl⟩

end Theory.GroupTheory

module

public import Theory.GroupTheory.PerfectCentralCover

/-!
# Central kernels and abelian Sylow preimages

A finite perfect group with an abelian Sylow p-subgroup has no central
p-torsion: a central subgroup of order p lies in every Sylow subgroup,
and central Sylow transfer places it in that subgroup's derived subgroup.
Consequently a perfect central cover whose preimage of one Sylow subgroup
is abelian has kernel of order prime to p.

This is the transfer step in the defining-characteristic multiplier
calculation for PSL₂, Aschbacher–Smith I.1.3(1) and GLS3 §6.1.
-/

open scoped IsMulCommutative

namespace PerfectCentralCovering

variable {E G : Type*} [Group E] [Finite E] [Group.IsPerfect E] [Group G]

/-- One abelian Sylow subgroup excludes that prime from any central kernel
of a finite perfect group. -/
public theorem not_dvd_card_kernel_of_abelian_sylow
    {p : ℕ} [Fact p.Prime] (f : E →* G)
    (hker : f.ker ≤ Subgroup.center E)
    (P : Sylow p E) (hP : IsMulCommutative P) :
    ¬ p ∣ Nat.card f.ker := by
  intro hp
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hp
  have hzE : orderOf (z : E) = p := (Subgroup.orderOf_coe z).trans hz
  let Z : Subgroup E := Subgroup.zpowers (z : E)
  have hZ : Z ≤ Subgroup.center E := Subgroup.zpowers_le.mpr (hker z.property)
  let : Z.Normal := ⟨fun n hn g => by
    have hc := Subgroup.mem_center_iff.mp (hZ hn) g
    simpa only [hc, mul_assoc, mul_inv_cancel, mul_one] using hn⟩
  have hZp : IsPGroup p Z := IsPGroup.of_card (n := 1)
    (by simpa only [Z, Nat.card_zpowers, pow_one] using hzE)
  have hzP : (z : E) ∈ (P : Subgroup E) :=
    hZp.le_sylow_of_normal P (Subgroup.mem_zpowers _)
  have hzD := Subgroup.center_inf_commutator_inf_sylow_le_commutator P
    ⟨⟨hker z.property, Group.IsPerfect.mem_commutator⟩, hzP⟩
  rw [Subgroup.commutator_self_eq_bot_iff.mpr hP] at hzD
  have hzone : (z : E) = 1 := Subgroup.mem_bot.mp hzD
  exact (Fact.out : p.Prime).ne_one (hzE.symm.trans (orderOf_eq_one_iff.mpr hzone))

/-- An abelian Sylow preimage excludes the Sylow prime from a perfect
central extension kernel. -/
public theorem not_dvd_card_kernel_of_abelian_sylow_preimage
    [Finite G] {p : ℕ} [Fact p.Prime] (f : E →* G)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center E)
    (Q : Sylow p G) (hQ : IsMulCommutative ((Q : Subgroup G).comap f)) :
    ¬ p ∣ Nat.card f.ker := by
  obtain ⟨P, hPQ⟩ := Sylow.mapSurjective_surjective hf p Q
  have hle : (P : Subgroup E) ≤ (Q : Subgroup G).comap f := by
    apply Subgroup.map_le_iff_le_comap.mp
    rw [← Sylow.coe_mapSurjective hf, hPQ]
  have hP : IsMulCommutative P := by
    let : IsMulCommutative ((Q : Subgroup G).comap f) := hQ
    exact ⟨⟨fun a b => Subtype.ext (congrArg (fun t : (Q : Subgroup G).comap f => (t : E))
      (mul_comm (⟨a, hle a.property⟩ : (Q : Subgroup G).comap f)
        (⟨b, hle b.property⟩ : (Q : Subgroup G).comap f)))⟩⟩
  exact not_dvd_card_kernel_of_abelian_sylow f hker P hP

end PerfectCentralCovering

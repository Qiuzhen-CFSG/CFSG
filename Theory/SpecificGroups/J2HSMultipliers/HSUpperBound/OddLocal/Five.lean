module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.GroupTheory.PerfectCentralCoverSimultaneousInversion

/-!
# The five-primary HS central-kernel exclusion

The existing nonabelian order-125 subgroup is Sylow by the certified HS order.
A word in the defining generators simultaneously inverts its two order-five
generators and fixes their central commutator. The general simultaneous-inversion
argument then excludes five from every finite perfect central kernel.

The intentional `import all` permits finite checks on the existing private packed
permutations without changing their public boundary. GAP supplies candidate words
only. All identities, including the left-action commutator convention, are checked
in Lean's kernel. Retained data and reproduction instructions are in `source/`.
Sources: Aschbacher–Smith I.1.3(1), printed p.407; GLS3 §6.1 and Table 5.3m;
ATLAS HSG1-p100B0 (provenance in the imported carrier's source directory).
-/

namespace Theory.SpecificGroups.J2HSMultipliers.HS.Five
open Sporadic.LeechRelated.HS Subgroup
open Sporadic.LeechRelated.HS.FiveSubgroup
open scoped commutatorElement

private def rMap (i : Fin 100) : Fin 100 :=
  ⟨(3329796298177913978717995273742067314730585540455411848050923705642222344748267960729206279428937654238465485439305521975965510354693735230856011448444517829994984234914405595298910604886455689880257540800544785 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private def rInvMap (i : Fin 100) : Fin 100 :=
  ⟨(1259064236549339949566533289172127641274840464949239356850303739109902190656926224600282106529363744431693196657970777791359048328368828857643857552742394842566650748242096572491171595619111868154276297183298049 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem rLeft : ∀ i, rInvMap (rMap i) = i := by
  apply allFin
  decide +kernel
private def rPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm rMap rInvMap rLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin rLeft)
private def rWord : Carrier := (b⁻¹ ^ 2) * a * b * a * (b⁻¹ ^ 3) * a⁻¹ * b⁻¹ * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * b * a * (b ^ 2) * a * (b ^ 3) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * b⁻¹
private theorem rPerm_eq_word : rPerm = (rWord : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def r : Carrier := ⟨rPerm, rPerm_eq_word.symm ▸ rWord.property⟩

private theorem x_pow : x ^ 5 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem y_pow : y ^ 5 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem x_commute_commutator : x * ⁅x, y⁆ = ⁅x, y⁆ * x := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem y_commute_commutator : y * ⁅x, y⁆ = ⁅x, y⁆ * y := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem r_inverts_x : r * x * r⁻¹ = x⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem r_inverts_y : r * y * r⁻¹ = y⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem r_commute_commutator : r * ⁅x, y⁆ = ⁅x, y⁆ * r := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem commutator_ne_one : ⁅x, y⁆ ≠ 1 := by
  intro h
  exact xy_ne_yx (commutatorElement_eq_one_iff_mul_comm.mp h)

/-- A marked Sylow pair and its certified ambient inverter. -/
public theorem exists_configuration :
    ∃ (Q : Sylow 5 Carrier) (x y r : Carrier),
      closure ({x, y} : Set Carrier) = (Q : Subgroup Carrier) ∧
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧
      Commute x ⁅x, y⁆ ∧ Commute y ⁅x, y⁆ ∧
      r * x * r⁻¹ = x⁻¹ ∧ r * y * r⁻¹ = y⁻¹ ∧ Commute r ⁅x, y⁆ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hi : ¬ 5 ∣ subgroup.index := by
    have h := subgroup.card_mul_index
    rw [card_subgroup, NormalizerIndex.card_carrier] at h
    have he : subgroup.index = 354816 := by omega
    rw [he]
    decide
  exact ⟨subgroup_isPGroup.toSylow hi, x, y, r,
    rfl, x_pow, y_pow, commutator_ne_one, x_commute_commutator,
    y_commute_commutator, r_inverts_x, r_inverts_y, r_commute_commutator⟩

/-- Apply the marked local configuration to an arbitrary finite perfect central cover. -/
public theorem not_dvd_card_kernel
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬ 5 ∣ Nat.card f.ker := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨Q, x, y, r, hQ, hx, hy, hz, hxz, hyz, hrx, hry, hrz⟩ := exists_configuration
  exact PerfectCentralCovering.not_dvd_card_kernel_of_simultaneous_inversion
    f hf hk (by decide : Nat.Coprime 5 2) Q x y r hQ hx hy hz hxz hyz hrx hry hrz

end Theory.SpecificGroups.J2HSMultipliers.HS.Five

module
public import Theory.Frattini.PGroup
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.ThreeSubgroups
/-!
# An abelian seed controlling a Frattini action

For mutually normalizing subgroups N and U, with U abelian, [N,U] lies
in N intersect U and [[N,U],U] is trivial. Any subgroup fixing U also
has its commutator with N centralizing U, by the three-subgroups lemma.

If [N,U] lies in a seed E inside U, conjugation by U on N/Φ(N) has
all displacements in the literal image of E and fixes that image pointwise.
For a finite two-group N, N intersect U is in the kernel of this action.
No splitting of N, elementary structure of N, or faithfulness is assumed.

These elementary commutator and Burnside-basis reductions are used on
the retained kernel in Aschbacher--Smith 5.1.13, printed pp.635--638,
refs/quasithin.pdf; the actual application is LocalBinaryQuadratic.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Subgroup.FrattiniSeed
variable {G : Type*} [Group G]

/-- Mutual normalization confines the commutator to the intersection;
fixing the abelian subgroup forces the rotated commutator to centralize it. -/
theorem commutator_control (N U B : Subgroup G)
    (hn : N ≤ normalizer (U : Set G))
    (hu : U ≤ normalizer (N : Set G))
    (ha : IsMulCommutative U)
    (hb : B ≤ centralizer (U : Set G)) :
    ⁅N,U⁆ ≤ N ⊓ U ∧ ⁅⁅N,U⁆,U⁆ = ⊥ ∧ ⁅N,B⁆ ≤ centralizer (U : Set G) := by
  have hNU : ⁅N,U⁆ ≤ U := le_normalizer_iff_commutator_le_right.mp hn
  have hUN : ⁅N,U⁆ ≤ N := le_normalizer_iff_commutator_le_left.mp hu
  have hz : ⁅⁅N,U⁆,U⁆ = ⊥ := bot_unique
    ((commutator_mono hNU le_rfl).trans_eq (commutator_self_eq_bot_iff.mpr ha))
  refine ⟨le_inf hUN hNU,hz,commutator_eq_bot_iff_le_centralizer.mp ?_⟩
  apply commutator_commutator_eq_bot_of_rotate
  · rw [commutator_eq_bot_iff_le_centralizer.mpr hb,commutator_bot_left]
  · rw [commutator_comm U N]
    exact bot_unique ((commutator_mono hNU le_rfl).trans_eq
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hb)))

/-- The ambient conjugation action with its displacement confined to a fixed seed. -/
theorem quotient_seed_action (N U E : Subgroup G)
    (hEU : E ≤ U)
    (hu : U ≤ normalizer (N : Set G))
    (ha : IsMulCommutative U) (hc : ⁅N,U⁆ ≤ E) :
    ∃ a : U →* MulAut N,
      (∀ (u : U) (v : N), ((a u v : N) : G) =
        (u : G) * (v : G) * (u : G)⁻¹) ∧
      let d := (quotientAut (frattini N)).comp a
      let q := QuotientGroup.mk' (frattini N)
      let V := (E.subgroupOf N).map q
      (∀ (u : U) (v : N ⧸ frattini N), d u v * v⁻¹ ∈ V) ∧
      (∀ (u : U) (v : V), d u v = v) ∧
      (∀ (u w : U) (v : N ⧸ frattini N),
        d u (d w v * v⁻¹) = d w v * v⁻¹) := by
  let a : U →* MulAut N := N.normalizerMonoidHom.comp
    (U.subtype.codRestrict (normalizer (N : Set G)) (fun u => hu u.property))
  let d := (quotientAut (frattini N)).comp a
  let q := QuotientGroup.mk' (frattini N)
  let V := (E.subgroupOf N).map q
  have hact (u : U) (v : N) : ((a u v : N) : G) =
      (u : G) * (v : G) * (u : G)⁻¹ := rfl
  have hdisp (u : U) (v : N ⧸ frattini N) : d u v * v⁻¹ ∈ V := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini N) v
    change quotientAut (frattini N) (a u) (q x) * (q x)⁻¹ ∈ V
    rw [quotientAut_apply_mk,←map_inv,←map_mul]
    apply mem_map_of_mem
    change ((a u x : N) : G) * (x : G)⁻¹ ∈ E
    rw [hact]
    exact hc ((commutator_comm U N) ▸ commutator_mem_commutator u.property x.property)
  have hfix (u : U) (v : V) : d u (v : N ⧸ frattini N) = v := by
    obtain ⟨x,hx,hxv⟩ := v.property
    change q x = (v : N ⧸ frattini N) at hxv
    rw [←hxv]
    change quotientAut (frattini N) (a u) (q x) = q x
    rw [quotientAut_apply_mk]
    congr 1
    apply Subtype.ext
    rw [hact]
    exact mul_inv_eq_iff_eq_mul.mpr
      (congrArg (fun y : U => (y : G)) (ha.is_comm.comm u ⟨x,hEU hx⟩))
  exact ⟨a,hact,hdisp,hfix,fun u w v => hfix u ⟨_,hdisp w v⟩⟩
/-- Elements lying in N act internally, hence trivially on N/Φ(N). -/
theorem frattini_conjugation_kernel (N U : Subgroup G) [Finite N]
    (hN : IsPGroup 2 N) (a : U →* MulAut N)
    (ha : ∀ (u : U) (v : N), ((a u v : N) : G) =
      (u : G) * (v : G) * (u : G)⁻¹) :
    N.subgroupOf U ≤ ((quotientAut (frattini N)).comp a).ker := by
  let : Fact (IsPGroup 2 N) := ⟨hN⟩
  let : IsElementaryAbelian 2 (N ⧸ frattini N) := isElementaryAbelian_quotient_frattini
  intro u hu
  apply MulEquiv.ext
  intro v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini N) v
  change quotientAut (frattini N) (a u) (QuotientGroup.mk' (frattini N) x) =
    QuotientGroup.mk' (frattini N) x
  rw [quotientAut_apply_mk]
  have he : a u x = (⟨u,hu⟩ : N) * x * (⟨u,hu⟩ : N)⁻¹ := Subtype.ext (ha u x)
  rw [he,map_mul,map_mul,map_inv,mul_right_comm,mul_inv_cancel,one_mul]

end Subgroup.FrattiniSeed

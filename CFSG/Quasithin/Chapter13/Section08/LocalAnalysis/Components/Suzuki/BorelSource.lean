module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Quotient
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource.Setup
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource.Geometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource.Pair
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.LiftTransport
public import Theory.GroupTheory.SylowNormalizerCommutingFamily


/-!
# The source Suzuki Borel argument in both component orbits

From the precise earlier source inputs, the intrinsic orbit construction
produces an invariant Borel in K₀* = ⟨(K*)^(T*)⟩. Its lift inside K₀ is
solvable; the universal exclusion of 13.8.13 therefore places it in M.
The identity L₁ = θ(H ∩ M) gives the reverse normalization. Three-freeness
then gives the source bound [O²(B₀),L₁] ≤ L₁ ∩ O²(B₀) ≤ O₂(L₁).

The same mutual normalization already controls the whole B₀/O₂(B₀)
action. Thus the concrete detector applies directly to B₀*, with no need
to identify O²(B₀) with O₂(B₀). Exact core and residual image comparisons
are proved separately. The whole two-perfect {2,3}-actor centralizes K₀*;
generation then proves normality of L₁* in H*, and its cardinality is
2^r 3^s. Marked coordinates for the swapped orbit are re-exported.

This proves the Borel and group-action step of Aschbacher–Smith 13.8.16
from the specified earlier facts, printed pp.952–953 (combined manuscript
of 1 March 2004). The natural-module argument and final contradiction
belong to the parent source-theorem assembly.
-/

@[expose] public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource
variable {G : Type*} [Group G] [Finite G]
variable {H K L₁ T G₁ M : Subgroup G} {m : ℕ}

namespace InvariantBorel
variable (b : InvariantBorel H K L₁ T m)

omit [Finite G] in
theorem detects (hm : 0 < m) : DetectsThreeAutomorphisms
    (b.borel.subgroupOf (Source.starImage H (conjugateSpanBy K T))) :=
  (suzukiBorel_pi_detectsThreeAutomorphisms m b.factors hm b.factors_one_or_two).of_mulEquiv
    b.equiv b.borel_map

omit [Finite G] in
theorem three_free (hm : 0 < m) : ¬ 3 ∣ Nat.card b.borel := by
  have horbit : ¬ 3 ∣ Nat.card (Source.starImage H (conjugateSpanBy K T)) := by
    rw [Nat.card_congr b.equiv.toEquiv, Nat.card_fun]
    exact fun hd => suzukiMatrixGroup_three_free m hm (Nat.prime_three.dvd_of_dvd_pow hd)
  exact fun hd => horbit (hd.trans (card_dvd_of_le b.le_orbit))

omit [Finite G] in
theorem solvable (hm : 0 < m) : Group.IsSolvable b.borel := by
  let : Group.IsSolvable (SuzukiBorelSubgroup m) := suzukiBorelSubgroup_isSolvable m hm
  let : Group.IsSolvable (Fin b.factors → SuzukiBorelSubgroup m) :=
    Group.isSolvable_finite_pi (fun _ : Fin b.factors => SuzukiBorelSubgroup m)
  let D := pi Set.univ (fun _ : Fin b.factors => SuzukiBorelSubgroup m)
  let j : D →* (Fin b.factors → SuzukiBorelSubgroup m) := {
    toFun := fun x i => ⟨x.val i, x.property i (Set.mem_univ i)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg (fun f => (f i : SuzukiMatrixGroup m)) h
  let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective hj
  let e := ((subgroupOfEquivOfLe b.le_orbit).symm.trans
    (b.equiv.subgroupMap (b.borel.subgroupOf (Source.starImage H (conjugateSpanBy K T))))).trans
      (MulEquiv.subgroupCongr b.borel_map)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end InvariantBorel

private theorem three_free_of_starImage (B : Subgroup G) (hBH : B ≤ H)
    (hb : ¬ 3 ∣ Nat.card (Source.starImage H B)) : ¬ 3 ∣ Nat.card B := by
  let f := Swapped.LinearTwo.orbitStarMap H B hBH
  let j : f.ker →* pCore 2 H :=
    ((inclusion hBH).comp f.ker.subtype).codRestrict _ (by
      intro x
      exact (QuotientGroup.eq_one_iff _).mp x.property)
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 H => ((z : H) : G)) h
  have hp : IsPGroup 2 f.ker := pCore_isPGroup.of_injective j hj
  obtain ⟨r, hr⟩ := hp.exists_card_eq
  have hc := f.ker.card_mul_index
  rw [index_ker, Swapped.LinearTwo.orbitStarMap_range, hr] at hc
  intro hd
  rw [← hc] at hd
  rcases Nat.prime_three.dvd_mul.mp hd with h | h
  · exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  · exact hb h

variable (d : Earlier H K L₁ T G₁ M m) (b : InvariantBorel H K L₁ T m)

def lift : Subgroup G := Swapped.LinearTwo.borelLift H (conjugateSpanBy K T) d.orbit_le b.borel

def residual : Subgroup G := (pResidual 2 (lift d b)).map (lift d b).subtype

omit [Finite G] in
theorem lift_le : lift d b ≤ conjugateSpanBy K T := Swapped.LinearTwo.borelLift_le _ _ _ _

omit [Finite G] in
theorem lift_starImage : Source.starImage H (lift d b) = b.borel :=
  Swapped.LinearTwo.borelLift_starImage _ _ _ _ b.le_orbit

omit [Finite G] in
theorem lift_normalized : L₁ ⊔ T ≤ normalizer (lift d b : Set G) :=
  Swapped.LinearTwo.borelLift_normalized _ _ _ d.orbit_le d.base_le _
    b.orbit_normalized b.normalized

theorem lift_le_M : lift d b ≤ M := by
  let : Group.IsSolvable b.borel := b.solvable d.parameter_pos
  apply borel_le_of_solvable_exclusion L₁ T G₁ M (lift d b) d.solvable_exclusion
    (Swapped.LinearTwo.borelLift_solvable _ _ _ _) d.base_solvable (lift_normalized d b)
  · exact ((lift_le d b).trans d.orbit_le).trans d.overgroup_le
  · exact d.base_le.trans d.overgroup_le

omit [Finite G] in
theorem residual_le_lift : residual d b ≤ lift d b := map_subtype_le _

omit [Finite G] in
theorem residual_normalized : L₁ ⊔ T ≤ normalizer (residual d b : Set G) :=
  (lift_normalized d b).trans (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

theorem residual_starImage : Source.starImage H (residual d b) =
    (pResidual 2 b.borel).map b.borel.subtype := by
  rw [residual, starImage_twoResidual H (lift d b) ((lift_le d b).trans d.orbit_le), lift_starImage]

theorem lift_star_twoCore : Source.starImage H ((lift d b).pCoreIn 2) = b.borel.pCoreIn 2 := by
  rw [starImage_twoCore H (lift d b) ((lift_le d b).trans d.orbit_le), lift_starImage]

theorem residual_commutator :
    ⁅residual d b, L₁⁆ ≤ L₁ ⊓ residual d b ∧ L₁ ⊓ residual d b ≤ L₁.pCoreIn 2 := by
  have hBN : residual d b ≤ normalizer (L₁ : Set G) :=
    (le_inf ((residual_le_lift d b).trans ((lift_le d b).trans d.orbit_le))
      ((residual_le_lift d b).trans (lift_le_M d b))).trans d.intersection_normalizes
  have hLB : L₁ ≤ normalizer (residual d b : Set G) := le_sup_left.trans (residual_normalized d b)
  have ht : ¬ 3 ∣ Nat.card (lift d b) := three_free_of_starImage _
    ((lift_le d b).trans d.orbit_le) (by rw [lift_starImage]; exact b.three_free d.parameter_pos)
  refine ⟨le_inf (le_normalizer_iff_commutator_le_right.mp hBN)
    (le_normalizer_iff_commutator_le_left.mp hLB), ?_⟩
  exact le_twoCore_of_three_free inf_le_left d.three_quotient
    (fun hd => ht (hd.trans (card_dvd_of_le (inf_le_right.trans (residual_le_lift d b)))))

include d b in
theorem star_centralizes :
    Source.starImage H L₁ ≤ centralizer (Source.starImage H (conjugateSpanBy K T) : Set _) := by
  have hLH : L₁ ≤ H := le_sup_left.trans d.base_le
  have hLB : Source.starImage H L₁ ≤ normalizer (b.borel : Set _) :=
    (map_mono (subgroupOf_mono H (show L₁ ≤ L₁ ⊔ T from le_sup_left))).trans b.normalized
  have hBL : b.borel ≤ normalizer (Source.starImage H L₁ : Set _) := by
    rw [← lift_starImage d b]
    exact starImage_normalizes H L₁ (lift d b)
      ((le_inf ((lift_le d b).trans d.orbit_le) (lift_le_M d b)).trans d.intersection_normalizes)
  apply centralizes_of_mutual_normalization b.le_orbit (b.detects d.parameter_pos)
    (starImage_twoPerfect H L₁ hLH d.twoPerfect)
    (starImage_three_quotient H L₁ hLH d.three_quotient)
  · exact starImage_normalizes H (conjugateSpanBy K T) L₁ (le_sup_left.trans b.orbit_normalized)
  · exact b.three_free d.parameter_pos
  · exact hLB
  · exact hBL

include d b in
theorem star_normal : (Source.starImage H L₁).Normal := by
  have hLH : L₁ ≤ H := le_sup_left.trans d.base_le
  have hTH : T ≤ H := le_sup_right.trans d.base_le
  have hgen : Source.starImage H (conjugateSpanBy K T) ⊔
      (Source.starImage H L₁ ⊔ Source.starImage H T) = ⊤ := by
    rw [← Swapped.LinearTwo.starImage_sup H L₁ T hLH hTH,
      ← Swapped.LinearTwo.starImage_sup H (conjugateSpanBy K T) (L₁ ⊔ T) d.orbit_le d.base_le,
      ← d.generated, Source.starImage, subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  exact sup_le ((le_centralizer_iff.mp (star_centralizes d b)).trans (Subgroup.centralizer_le_normalizer _))
    (sup_le (Source.starImage H L₁).le_normalizer
      (starImage_normalizes H L₁ T d.sylow_normalizes))

include d in
theorem star_card : ∃ r s : ℕ, Nat.card (Source.starImage H L₁) = 2 ^ r * 3 ^ s :=
  starImage_card H L₁ (le_sup_left.trans d.base_le) d.three_quotient

/-- The source Borel step, with the invariant Borel constructed from the
specified earlier inputs and with the two-residual kept distinct from the core. -/
theorem source_borel_outputs (d : Earlier H K L₁ T G₁ M m) :
    ∃ b : InvariantBorel H K L₁ T m,
      lift d b ≤ conjugateSpanBy K T ∧ lift d b ≤ M ∧
      L₁ ⊔ T ≤ normalizer (lift d b : Set G) ∧
      Source.starImage H (lift d b) = b.borel ∧
      Source.starImage H (residual d b) = (pResidual 2 b.borel).map b.borel.subtype ∧
      (⁅residual d b, L₁⁆ ≤ L₁ ⊓ residual d b ∧ L₁ ⊓ residual d b ≤ L₁.pCoreIn 2) ∧
      Source.starImage H L₁ ≤ centralizer (Source.starImage H (conjugateSpanBy K T) : Set _) ∧
      (Source.starImage H L₁).Normal ∧
      ∃ r s : ℕ, Nat.card (Source.starImage H L₁) = 2 ^ r * 3 ^ s := by
  obtain ⟨b⟩ := exists_invariantBorel d
  exact ⟨b, lift_le d b, lift_le_M d b, lift_normalized d b, lift_starImage d b,
    residual_starImage d b, residual_commutator d b, star_centralizes d b,
    star_normal d b, star_card d⟩

/-- The three group-action inputs consumed by the natural-section argument,
with no Borel or quotient-action premise. Both orbit cases are retained. -/
theorem source_group_action (d : Earlier H K L₁ T G₁ M m) :
    Source.starImage H L₁ ≤ centralizer (Source.starImage H (conjugateSpanBy K T) : Set _) ∧
      (Source.starImage H L₁).Normal ∧
      ∃ r s : ℕ, Nat.card (Source.starImage H L₁) = 2 ^ r * 3 ^ s := by
  obtain ⟨b⟩ := exists_invariantBorel d
  exact ⟨star_centralizes d b, star_normal d b, star_card d⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource

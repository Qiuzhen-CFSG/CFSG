module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.Centralizer
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The original span and its point-local action

The two abelian factors centralize their intersection, and the derived group
of their span lies in their mutual commutator. The original marked coordinates
show that the point-local preimage fixes the span modulo the intersection.
This includes both the point radical and the embedded Levi subgroup.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
variable {F G : Type*} [Field F] [Group G]
variable {κ : G →* Sp F} {A B : Subgroup G} (s : MarkedPair κ A B)

include s in
private theorem natural_commutative : IsMulCommutative A :=
  IsMulCommutative.of_comm (fun x y => s.natural.injective (by
    rw [map_mul,map_mul,mul_comm]))

include s in
/-- Both original abelian factors centralize their common intersection. -/
theorem span_centralizes_intersection : A ⊔ B ≤ centralizer ((A ⊓ B : Subgroup G) : Set G) := by
  let : IsMulCommutative A := natural_commutative s
  let : IsMulCommutative B := s.opposite_commutative
  apply sup_le
  · exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le inf_le_left)
  · exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le inf_le_right)

include s in
/-- The derived group of the original span lies in its critical commutator. -/
theorem span_commutator_le_critical : ⁅A ⊔ B,A ⊔ B⁆ ≤ ⁅A,B⁆ := by
  have hA : ⁅A,A⁆ ≤ ⁅A,B⁆ :=
    (commutator_self_eq_bot_iff.mpr (natural_commutative s)).le.trans bot_le
  have hB : ⁅B,B⁆ ≤ ⁅A,B⁆ :=
    (commutator_self_eq_bot_iff.mpr s.opposite_commutative).le.trans bot_le
  have hn : A ⊔ B ≤ normalizer ((⁅A,B⁆ : Subgroup G) : Set G) :=
    sup_le (normalizer_commutator_ge_left A B) (normalizer_commutator_ge_right A B)
  apply commutator_sup_le_of_relative_normal (A ⊔ B) A B (A ⊔ B) ⁅A,B⁆
    hn le_sup_left le_sup_right
  · rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal (A ⊔ B) A B A ⁅A,B⁆
      hn le_sup_left le_sup_right hA (commutator_comm B A).le
  · rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal (A ⊔ B) A B B ⁅A,B⁆
      hn le_sup_left le_sup_right le_rfl hB

include s in
/-- The original point parabolic normalizes the span. -/
theorem span_normalized : (stabilizer (point F)).comap κ ≤
    normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  let : A.Normal := s.kernel ▸ inferInstance
  exact (le_inf le_normalizer_of_normal s.opposite_normalized).trans
    (normalizer_inf_normalizer_le_normalizer_sup A B)

include s in
/-- The original point parabolic normalizes the intersection. -/
theorem intersection_normalized : (stabilizer (point F)).comap κ ≤
    normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  let : A.Normal := s.kernel ▸ inferInstance
  exact (le_inf le_normalizer_of_normal s.opposite_normalized).trans
    inf_normalizer_le_normalizer_inf

include s in
/-- The point-local factor acts trivially on the original span modulo its intersection. -/
theorem pointLocal_span_fixed_mod_intersection [Finite G]
    (g : G) (hg : κ g ∈ pointLocal) (x y : (A ⊔ B : Subgroup G))
    (hy : (y : G) = g*x*g⁻¹) : y / x ∈ (A ⊓ B).subgroupOf (A ⊔ B) := by
  obtain ⟨c,_,_,hc⟩ := s.coordinates
  have hgP : κ g ∈ stabilizer (point F) := pointLocal_le hg
  have hchar : determinantCharacter (point F) ⟨κ g,hgP⟩ = 1 := by
    change (⟨κ g,hgP⟩ : stabilizer (point F)) ∈ (determinantCharacter (point F)).ker
    rw [←determinantKernel_subgroupOf]
    exact hg
  have he : c.map y = c.map x := by
    apply Multiplicative.toAdd.injective
    simpa only [hchar,Units.val_one,one_pow,one_mul,inv_one,Prod.mk.eta] using hc g hgP x y hy
  have hmem : y / x ∈ c.map.ker := by
    change c.map (y / x) = 1
    rw [map_div,he,div_self']
  rw [c.kernel] at hmem
  exact hmem

include s in
/-- The original point core moves the span only into the common intersection. -/
theorem pointCore_span_commutator_le_intersection [Finite G] :
    ⁅A ⊔ B,pointRadicalAmbient.comap κ⁆ ≤ A ⊓ B := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro g hg x hx
  have hgL : κ g ∈ pointLocal := by
    obtain ⟨u,_,hu⟩ := hg
    rw [←hu]
    exact u.property
  have hgP : κ g ∈ stabilizer (point F) := pointLocal_le hgL
  let x₀ : (A ⊔ B : Subgroup G) := ⟨x,hx⟩
  let y₀ : (A ⊔ B : Subgroup G) :=
    ⟨g*x*g⁻¹,(mem_normalizer_iff.mp (span_normalized s hgP) x).mp hx⟩
  have hh := pointLocal_span_fixed_mod_intersection s g hgL x₀ y₀ rfl
  change g*x*g⁻¹ / x ∈ A ⊓ B at hh
  simpa only [div_eq_mul_inv,commutatorElement_def] using hh

include s in
/-- Every lift of the literal point Levi acts trivially on the original span quotient. -/
theorem levi_span_fixed_mod_intersection [Finite G]
    (L : Matrix.SpecialLinearGroup (Fin 2) F) (g : G)
    (hg : κ g = (pointLevi L).val) (x y : (A ⊔ B : Subgroup G))
    (hy : (y : G) = g*x*g⁻¹) : y / x ∈ (A ⊓ B).subgroupOf (A ⊔ B) := by
  apply pointLocal_span_fixed_mod_intersection s g _ x y hy
  rw [hg]
  exact (pointLevi L).property

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison

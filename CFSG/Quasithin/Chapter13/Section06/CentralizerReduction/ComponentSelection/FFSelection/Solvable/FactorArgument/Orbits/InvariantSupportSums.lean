module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Orbits.InvariantSupportSums.CubicAction

/-!
# Invariant subgroups are sums of the actual supports

Each cubic residual acts transitively on the nonidentity elements of its
own U_i and fixes all other supports. Taking a commutator with a cubic
actor therefore extracts a nonzero vector from any nonzero coordinate of
an X-invariant subgroup B. Invariance then puts the whole U_i in B.
Reassembling a vector with the specified internal product proves that B
is exactly the sum of the supports it contains.

The final application discharges the local support-decomposition premise
of the existing irreducibility theorem for X T_v. Factor transitivity and
the construction of the decomposition retain their separate source owners.
All subgroups, quotient lifts and conjugations are the original ones.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 13.6.13, printed p.929.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.NormalS3Decomposition
variable {G : Type*} [Group G] {z v : G} {X : Subgroup (Gstar z v)}
variable (d : NormalS3Decomposition z v X)

/-- The coordinate product agrees with the specified internal-space equivalence. -/
theorem supportProductMap_eq_space :
    d.supportProductMap = (movedSubgroup z v d.H).subtype.comp d.space.toMonoidHom := by
  apply MonoidHom.pi_ext
  intro i a
  exact (d.supportProductMap_single i a).trans (d.space_single i a).symm

/-- A factor commutator extracts just its own coordinate in the actual product. -/
theorem supportProductMap_commutator_coordinate [IsElementaryAbelian 2 (Uv z v)]
    (i : Fin d.count) (g : Gv v) (hg : starMk z v g ∈ d.factor i)
    (x : ∀ j, d.support j) :
    ⁅d.supportProductMap x, (g : G)⁆ = ⁅(x i : G), (g : G)⁆ := by
  let W := movedSubgroup z v d.H
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (movedSubgroup_le_Uv z v d.H)
  let c := conjugationAction W (Gv v) d.movedSubgroup_normalized g
  let delta : W →* W := MonoidHom.id W * c.toMonoidHom⁻¹
  let f : (∀ j, d.support j) →* G := W.subtype.comp (delta.comp d.space.toMonoidHom)
  let p := MonoidHom.mulSingle (fun j => d.support j) i
  let q := Pi.evalMonoidHom (fun j => d.support j) i
  have hf (y : ∀ j, d.support j) :
      f y = ⁅d.supportProductMap y, (g : G)⁆ := by
    rw [d.supportProductMap_eq_space]
    change (d.space y : G) * ((g : G) * (d.space y : G) * (g : G)⁻¹)⁻¹ = ⁅(d.space y : G), (g : G)⁆
    simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
  have he : f = f.comp (p.comp q) := by
    apply MonoidHom.pi_ext
    intro j a
    rw [hf]
    change _ = f (Pi.mulSingle i (Pi.mulSingle (M := fun j => d.support j) j a i))
    rw [hf, d.supportProductMap_single, d.supportProductMap_single]
    by_cases hji : j = i
    · subst j; simp
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm hji)]
      change ⁅(a : G), (g : G)⁆ = ⁅(1 : G), (g : G)⁆
      rw [commutatorElement_one_left]
      apply (mem_bot (G := G)).mp
      rw [← d.support_cross_commutator hji]
      exact commutator_mem_commutator a.property
        (mem_map.mpr ⟨g, hg, rfl⟩)
  calc
    ⁅d.supportProductMap x, (g : G)⁆ = f x := (hf x).symm
    _ = f (Pi.mulSingle i (x i)) := DFunLike.congr_fun he x
    _ = ⁅(x i : G), (g : G)⁆ := by rw [hf, d.supportProductMap_single]

private theorem cubic_lift (i : Fin d.count) (a : pResidual 2 (d.factor i)) :
    ∃ g : Gv v, ∃ _hg : starMk z v g ∈ d.factor i,
      (g : G) ∈ starPreimage z v X ∧
      ∀ w : d.support i, (d.supportCubicAction i a w : G) = (g : G) * w * (g : G)⁻¹ := by
  obtain ⟨g, hg⟩ := starMk_surjective z v (a.val : Gstar z v)
  have hgf : starMk z v g ∈ d.factor i := hg ▸ a.val.property
  have he : a.val = (⟨starMk z v g, hgf⟩ : d.factor i) := Subtype.ext hg.symm
  refine ⟨g, hgf, ?_, ?_⟩
  · apply mem_map.mpr
    refine ⟨g, ?_, rfl⟩
    change starMk z v g ∈ X
    rw [hg]
    exact d.factorResidual_le_X i (mem_map_of_mem (d.factor i).subtype a.property)
  · intro w
    change (d.supportAction i a.val w : G) = _
    rw [he, d.supportAction_mk]

variable [Finite G] [IsElementaryAbelian 2 (Uv z v)]

/-- A nonzero intersection with an X-invariant subgroup contains the whole support. -/
theorem support_le_of_invariant_mem (B : Subgroup G)
    (hB : starPreimage z v X ≤ normalizer (B : Set G))
    (i : Fin d.count) (w : d.support i) (hw : (w : G) ∈ B) (hw1 : w ≠ 1) :
    d.support i ≤ B := by
  intro y hy
  by_cases hy1 : y = 1
  · exact hy1 ▸ B.one_mem
  obtain ⟨a, ha⟩ := d.supportCubicAction_transitive i w ⟨y, hy⟩ hw1
    (fun he => hy1 (congrArg Subtype.val he))
  obtain ⟨g, hg, hgX, hact⟩ := d.cubic_lift i a
  have hc := (mem_normalizer_iff.mp (hB hgX) w).mp hw
  rw [← hact, ha] at hc
  exact hc

/-- If a coordinate of a vector in B is nonzero, its whole support lies in B. -/
theorem support_le_of_invariant_coordinate (B : Subgroup G)
    (hB : starPreimage z v X ≤ normalizer (B : Set G))
    (x : ∀ i, d.support i) (hx : d.supportProductMap x ∈ B)
    (i : Fin d.count) (hi : x i ≠ 1) : d.support i ≤ B := by
  obtain ⟨a, ha⟩ := d.supportCubicAction_moves i (x i) hi
  obtain ⟨g, hg, hgX, hact⟩ := d.cubic_lift i a
  have hgp : (g : G) ∈ starPreimage z v (d.factor i) := mem_map.mpr ⟨g, hg, rfl⟩
  have hm : ⁅(x i : G), (g : G)⁆ ∈ d.support i :=
    commutator_mem_commutator (d.support_le i (x i).property) hgp
  have hn : ⁅(x i : G), (g : G)⁆ ≠ 1 := by
    intro he
    apply ha
    apply Subtype.ext
    rw [hact]
    have hc := commutatorElement_eq_one_iff_mul_comm.mp he
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  apply d.support_le_of_invariant_mem B hB i ⟨_, hm⟩ _
    (fun he => hn (congrArg Subtype.val he))
  change ⁅(x i : G), (g : G)⁆ ∈ B
  rw [← d.supportProductMap_commutator_coordinate i g hg x]
  exact (le_normalizer_iff_commutator_le_left.mp hB)
    (commutator_mem_commutator hx hgX)

/-- Every X-invariant subgroup of U_H is the sum of the literal supports it contains. -/
theorem invariantSupportSums : d.InvariantSupportSums := by
  intro B hBW hB
  change B = ⨆ i : Fin d.count, ⨆ (_ : d.support i ≤ B), d.support i
  apply le_antisymm
  swap
  · apply iSup_le
    intro i
    exact iSup_le fun hi => hi
  intro b hb
  let x := d.space.symm ⟨b, hBW hb⟩
  have hx : d.supportProductMap x = b := by
    rw [d.supportProductMap_eq_space]
    exact congrArg Subtype.val (d.space.apply_symm_apply ⟨b, hBW hb⟩)
  let C : Subgroup G := ⨆ i : Fin d.count, ⨆ (_ : d.support i ≤ B), d.support i
  have hxi (i : Fin d.count) : (x i : G) ∈ C := by
    by_cases hi : x i = 1
    · exact (congrArg Subtype.val hi).symm ▸ C.one_mem
    · exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem
        (d.support_le_of_invariant_coordinate B hB x (hx ▸ hb) i hi) (x i).property)
  let : ∀ i, IsElementaryAbelian 2 (d.support i) := fun i =>
    IsElementaryAbelian.of_le ((d.support_le i).trans (movedSubgroup_le_Uv z v d.H))
  have hm : x ∈ C.comap d.supportProductMap := by
    rw [← Finset.univ_prod_mulSingle x]
    apply Subgroup.prod_mem
    intro i _
    change d.supportProductMap (Pi.mulSingle i (x i)) ∈ C
    rw [d.supportProductMap_single]
    exact hxi i
  exact hx ▸ hm

/-- Application to the existing source irreducibility API, with the support premise discharged. -/
theorem irreducible_of_factorsTransitive (T : Subgroup G) (htrans : d.FactorsTransitive T) :
    IrreducibleOn (starPreimage z v X ⊔ Tv T v) (movedSubgroup z v d.H) :=
  d.irreducible_of_invariantSupportSums T htrans d.invariantSupportSums

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.NormalS3Decomposition

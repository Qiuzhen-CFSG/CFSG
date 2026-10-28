module

public import CFSG.Quasithin.ChapterD.Section02.QuadraticOrbit
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# Cubic stabilizers and a common actor's codimension budget

For a moved member of an independent summand orbit, the stabilizer in a
cubic actor acts quadratically on that member. If the stabilizer acts
nontrivially, a nonzero first displacement and vanishing third displacement
force the actor orbit to consist of two summands.

On two disjoint invariant summands, fixed vectors split and fixed
codimensions add within the ambient bound. When the same elementary actor
is faithful on both summands, a bound of twice its rank forces an offender
on at least one. No independent ranks are assigned to the two images.

These are local steps in D.2.9 and D.3.5; the central-stabilizer branch,
starred-actor invariance, and the model exclusions remain separate steps.
The actual chosen-seed application is in `SeedAlternativesMovedActor`.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
D.2.9(1--2), printed pp.180--181, and D.3.5(2), pp.195--196.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

/-- D.2.9(2): an actor stabilizing a summand acts quadratically there when
a cubic overgroup carries that summand to a disjoint translate. -/
theorem cubic_stabilizer_quadratic
    (I : Submodule (ZMod 2) W) {A B : Subgroup H}
    (hc : IsCubic ρ A) (hBA : B ≤ A) (hBI : B ≤ subspaceStabilizer ρ I)
    {a : H} (ha : a ∈ A) (hdis : Disjoint I (I.map (ρ a))) :
    IsQuadratic (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I B) := by
  rintro b ⟨b,hb,rfl⟩ c ⟨c,hcB,rfl⟩ v
  apply Subtype.ext
  change ρ b (ρ c v.val - v.val) = ρ c v.val - v.val
  let w := ρ b (ρ c v.val - v.val) - (ρ c v.val - v.val)
  have hv : ρ c v.val - v.val ∈ I :=
    I.sub_mem ((hBI hcB v.val).2 v.property) v.property
  have hw : w ∈ I := I.sub_mem ((hBI hb _).2 hv) hv
  have he : ρ a w = w := sub_eq_zero.mp (hc a ha b (hBA hb) c (hBA hcB) v.val)
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp hdis w hw ⟨w,hw,he⟩)

open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous

/-- The noncentral stabilizer case of D.2.9(1). A nonzero displacement
inside one summand forces the cubic actor to permute only it and its mate. -/
theorem cubic_orbit_eq_self_or_moving_of_noncentral_stabilizer
    (I : Submodule (ZMod 2) W) (A : Subgroup H) [IsMulCommutative A]
    (hc : IsCubic ρ A) (hind : sSupIndep (subspaceOrbit ρ A I))
    {a b : H} (ha : a ∈ A) (ha2 : a * a = 1)
    (haI : I.map (ρ a) ≠ I) (hb : b ∈ A)
    (hbs : b ∈ subspaceStabilizer ρ I)
    (hn : ∃ v ∈ I, ρ b v ≠ v) {c : H} (hcA : c ∈ A) :
    I.map (ρ c) = I ∨ I.map (ρ c) = I.map (ρ a) := by
  classical
  by_contra hnot
  have hcI : I.map (ρ c) ≠ I := fun h => hnot (Or.inl h)
  have hcaI : I.map (ρ (c * a)) ≠ I := by
    intro he
    apply hnot
    right
    have hh := congrArg (fun J : Submodule (ZMod 2) W => J.map (ρ a)) he
    have hac : a * c = c * a := congrArg Subtype.val
      (mul_comm (⟨a,ha⟩ : A) ⟨c,hcA⟩)
    rw [← subspace_map_mul,
      show a * (c * a) = c by rw [← mul_assoc, hac, mul_assoc, ha2, mul_one]] at hh
    exact hh
  have hImem : I ∈ subspaceOrbit ρ A I := by
    refine ⟨1, ?_⟩
    simp only [Subgroup.coe_one, map_one, Module.End.one_eq_id, Submodule.map_id]
  let R := sSup (subspaceOrbit ρ A I \ {I})
  have hrest (d : H) (hd : d ∈ A) (hne : I.map (ρ d) ≠ I) : I.map (ρ d) ≤ R :=
    le_sSup ⟨⟨⟨d,hd⟩,rfl⟩,hne⟩
  obtain ⟨v,hv,hbv⟩ := hn
  let w := ρ b v - v
  have hw : w ∈ I := I.sub_mem ((hbs v).2 hv) hv
  have hwa : ρ a w ∈ R := hrest a ha haI ⟨w,hw,rfl⟩
  have hwc : ρ c w ∈ R := hrest c hcA hcI ⟨w,hw,rfl⟩
  have hwca : ρ (c*a) w ∈ R := hrest (c*a) (A.mul_mem hcA ha) hcaI ⟨w,hw,rfl⟩
  have he : ρ c (ρ a w - w) = ρ a w - w :=
    sub_eq_zero.mp (hc c hcA a ha b hb v)
  rw [map_sub, ← Module.End.mul_apply, ← map_mul] at he
  have hwrest : w ∈ R := by
    have hwEq : w = ρ a w + ρ c w - ρ (c*a) w := by
      calc
        w = ρ a w - (ρ a w - w) := (sub_sub_cancel _ _).symm
        _ = ρ a w - (ρ (c*a) w - ρ c w) := by rw [he]
        _ = _ := by abel
    rw [hwEq]
    exact R.sub_mem (R.add_mem hwa hwc) hwca
  exact hbv (sub_eq_zero.mp (Submodule.disjoint_def.mp (hind hImem) w hw hwrest))

/-- In the same branch the entire actor orbit is the literal sum of two
translates, before imposing any numerical ratio bound. -/
theorem cubic_orbitSpan_eq_pair_of_noncentral_stabilizer
    (I : Submodule (ZMod 2) W) (A : Subgroup H) [IsMulCommutative A]
    (hc : IsCubic ρ A) (hind : sSupIndep (subspaceOrbit ρ A I))
    {a b : H} (ha : a ∈ A) (ha2 : a * a = 1)
    (haI : I.map (ρ a) ≠ I) (hb : b ∈ A)
    (hbs : b ∈ subspaceStabilizer ρ I)
    (hn : ∃ v ∈ I, ρ b v ≠ v) :
    orbitSpan ρ A I = I ⊔ I.map (ρ a) := by
  apply le_antisymm
  · apply iSup_le
    intro c
    rcases cubic_orbit_eq_self_or_moving_of_noncentral_stabilizer
      ρ I A hc hind ha ha2 haI hb hbs hn c.property with he | he
    · rw [he]; exact le_sup_left
    · rw [he]; exact le_sup_right
  · exact sup_le (le_orbitSpan ρ A I) (le_iSup (fun c : A => I.map (ρ c)) ⟨a,ha⟩)

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

/-- Fixed vectors split over two invariant disjoint summands, for the same actor. -/
theorem fixedSpace_inf_disjoint_sup (I J : Submodule (ZMod 2) W) (A : Subgroup H)
    (hI : A ≤ subspaceStabilizer ρ I) (hJ : A ≤ subspaceStabilizer ρ J)
    (hd : Disjoint I J) :
    (I ⊔ J) ⊓ fixedSpace ρ A = (I ⊓ fixedSpace ρ A) ⊔ (J ⊓ fixedSpace ρ A) := by
  apply le_antisymm
  · rintro v ⟨hv,hf⟩
    obtain ⟨i,hi,j,hj,rfl⟩ := Submodule.mem_sup.mp hv
    have hfi : i ∈ fixedSpace ρ A := by
      intro a
      change ρ a i = i
      have he := hf a
      change ρ a (i+j) = i+j at he
      rw [map_add] at he
      have hij : ρ a i - i = j - ρ a j := by
        calc
          ρ a i - i = (ρ a i + ρ a j) - (i + ρ a j) := by abel
          _ = j - ρ a j := by rw [he]; abel
      apply sub_eq_zero.mp
      apply Submodule.disjoint_def.mp hd
      · exact I.sub_mem ((hI a.property i).2 hi) hi
      · rw [hij]
        exact J.sub_mem hj ((hJ a.property j).2 hj)
    have hfj : j ∈ fixedSpace ρ A := by
      intro a
      have he := hf a
      change ρ a (i+j) = i+j at he
      have hei : ρ a i = i := hfi a
      rw [map_add, hei] at he
      exact add_left_cancel he
    exact Submodule.mem_sup.mpr ⟨i,⟨hi,hfi⟩,j,⟨hj,hfj⟩,rfl⟩
  · exact sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)

/-- Fixed codimensions on disjoint invariant summands add within the original
ambient budget. The same subgroup A occurs in all three terms. -/
theorem common_actor_fixedCodim_pair_le [FiniteDimensional (ZMod 2) W]
    (I J : Submodule (ZMod 2) W) (A : Subgroup H)
    (hI : A ≤ subspaceStabilizer ρ I) (hJ : A ≤ subspaceStabilizer ρ J)
    (hd : Disjoint I J) :
    fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) +
      fixedCodim (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J A) ≤
      fixedCodim ρ A := by
  have hi := fixedCodim_add_finrank (subspaceImageRepresentation ρ I)
    (restrictedSubgroup ρ I A)
  have hj := fixedCodim_add_finrank (subspaceImageRepresentation ρ J)
    (restrictedSubgroup ρ J A)
  rw [(restrictedFixedSpaceEquiv ρ I A hI).finrank_eq] at hi
  rw [(restrictedFixedSpaceEquiv ρ J A hJ).finrank_eq] at hj
  have hs := I.finrank_sup_add_finrank_inf_eq J
  rw [hd.eq_bot, finrank_bot, add_zero] at hs
  have hf := (I ⊓ fixedSpace ρ A).finrank_sup_add_finrank_inf_eq (J ⊓ fixedSpace ρ A)
  have hd' : Disjoint (I ⊓ fixedSpace ρ A) (J ⊓ fixedSpace ρ A) :=
    hd.mono inf_le_left inf_le_left
  rw [hd'.eq_bot, finrank_bot, add_zero, ← fixedSpace_inf_disjoint_sup ρ I J A hI hJ hd] at hf
  have hsum := (I ⊔ J).finrank_sup_add_finrank_inf_eq (fixedSpace ρ A)
  have htop := (I ⊔ J ⊔ fixedSpace ρ A).finrank_le
  have hw := fixedCodim_add_finrank ρ A
  omega

/-- At most one of two faithful invariant summands can exceed the FF threshold
when their common elementary actor has fixed codimension at most twice its rank. -/
theorem common_actor_offends_one_of_pair [Finite H] [FiniteDimensional (ZMod 2) W]
    (I J : Submodule (ZMod 2) W) {A : Subgroup H} (hA : IsElementaryTwo A)
    (hI : A ≤ subspaceStabilizer ρ I) (hJ : A ≤ subspaceStabilizer ρ J)
    (hd : Disjoint I J) (hkI : subspaceKernel ρ I A = ⊥)
    (hkJ : subspaceKernel ρ J A = ⊥) (hc : fixedCodim ρ A ≤ 2 * rank A) :
    IsOffender (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) ∨
      IsOffender (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J A) := by
  let : IsElementaryAbelian 2 A := hA.2
  have hfaith (U : Submodule (ZMod 2) W) (hk : subspaceKernel ρ U A = ⊥) :
      ¬ U ≤ fixedSpace ρ A := by
    intro hf
    apply hA.1
    apply bot_unique
    intro a ha
    exact hk.le ⟨ha,fun v hv => hf hv ⟨a,ha⟩⟩
  have hIe := hA.restrictedSubgroup ρ I hI (hfaith I hkI)
  have hJe := hA.restrictedSubgroup ρ J hJ (hfaith J hkJ)
  have hrI := rank_subspaceKernel_add_image ρ I A hI (IsElementaryAbelian.isPGroup 2 A)
  have hrJ := rank_subspaceKernel_add_image ρ J A hJ (IsElementaryAbelian.isPGroup 2 A)
  rw [hkI, Representation.BinaryOffender.rank_bot, zero_add] at hrI
  rw [hkJ, Representation.BinaryOffender.rank_bot, zero_add] at hrJ
  have hsum := common_actor_fixedCodim_pair_le ρ I J A hI hJ hd
  by_cases h : fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) ≤ rank A
  · exact Or.inl ⟨hIe,by rw [hrI]; exact h⟩
  · exact Or.inr ⟨hJe, by rw [hrJ]; omega⟩

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

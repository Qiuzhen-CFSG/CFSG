module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PlacedModels
public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry
public import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# Excluding odd G₂ by the actual octonion sign weights

In odd characteristic, the simultaneous sign-weight spaces are orthogonal
for the nondegenerate polar norm. Each nonzero weight space therefore
contains a vector of nonzero norm. Right multiplication by that vector
shows that the occurring characters are closed under multiplication.
They form a subgroup of the character group with at most eight members.
Faithfulness embeds the elementary actor in its dual, giving two-rank
at most three for the actual split-octonion group.

The projected covering residual has elementary rank at least six, so the
odd G₂ row is impossible. The actual B-model sieve and Source Hall-kernel
application retain all remaining full covering quotients.
Source: Aschbacher--Smith, the rank inspection in 4.4.3, printed p.622.
The octonion coordinates and norm identities come from the licensed ATLAS
port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Atlas.SplitOctonion

variable {F A : Type*} [Field F] [Group A] [IsElementaryAbelian 2 A]

private def octonionAction (j : A →* Atlas.G2.Model F) : Representation F A (Carrier F) where
  toFun a := (j a).val.toLinearMap
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul]; rfl

omit [IsElementaryAbelian 2 A] in
private theorem octonionAction_apply (j : A →* Atlas.G2.Model F) (a : A) (x : Carrier F) :
    octonionAction j a x = (j a).val x := rfl

private theorem sign_pow (a : A) : a ^ 2 = 1 :=
  Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 A) a

private theorem weight_orthogonal (j : A →* Atlas.G2.Model F)
    {χ ψ : A →* Fˣ} (hχψ : χ ≠ ψ)
    {x y : Carrier F} (hx : x ∈ (octonionAction j).characterWeightSpace χ)
    (hy : y ∈ (octonionAction j).characterWeightSpace ψ) : normPolar x y = 0 := by
  have hex : ∃ a, χ a ≠ ψ a := by
    by_contra! h
    exact hχψ (MonoidHom.ext h)
  obtain ⟨a,ha⟩ := hex
  have hx' : (j a).val x = (χ a : F) • x := by
    exact (show ∀ b, (j b).val x = (χ b : F) • x by
      simpa only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, octonionAction_apply] using hx) a
  have hy' : (j a).val y = (ψ a : F) • y := by
    exact (show ∀ b, (j b).val y = (ψ b : F) • y by
      simpa only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, octonionAction_apply] using hy) a
  have haa : (j a).val ((j a).val y) = y := by
    change (j a * j a).val y = y
    rw [←map_mul,←pow_two,sign_pow,map_one]
    rfl
  have he := automorphism_normPolar (j a) x ((j a).val y)
  rw [haa,hx',hy'] at he
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at he
  by_contra hz
  exact ha (Units.ext (mul_right_cancel₀ hz he))

private theorem weight_has_nonzero_norm (j : A →* Atlas.G2.Model F)
    (h2 : (2 : F) ≠ 0) (χ : (octonionAction j).CharacterWeight) :
    ∃ x ∈ (octonionAction j).characterWeightSpace χ.val, norm x ≠ 0 := by
  classical
  by_contra! hn
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot χ.property
  apply hx0
  apply normPolar_nondegenerate
  have hk : (octonionAction j).characterWeightSpace χ.val ≤ (normPolar x).ker := by
    intro y hy
    have hh := norm_add x y
    rw [hn x hx,hn y hy,hn (x+y) (Submodule.add_mem _ hx hy)] at hh
    change normPolar x y = 0
    linear_combination -hh
  have htop : (⊤ : Submodule F (Carrier F)) ≤ (normPolar x).ker := by
    rw [← (octonionAction j).iSup_characterWeightSpace_eq_top_of_involutive sign_pow h2]
    refine iSup_le fun ψ => ?_
    by_cases he : χ.val = ψ.val
    · simpa only [←he] using hk
    · intro y hy
      exact weight_orthogonal j he hx hy
  intro y
  exact htop (Submodule.mem_top : y ∈ (⊤ : Submodule F (Carrier F)))

omit [IsElementaryAbelian 2 A] in
private theorem weight_mul (j : A →* Atlas.G2.Model F)
    {χ ψ : A →* Fˣ} {x y : Carrier F}
    (hx : x ∈ (octonionAction j).characterWeightSpace χ)
    (hy : y ∈ (octonionAction j).characterWeightSpace ψ) :
    mul x y ∈ (octonionAction j).characterWeightSpace (χ * ψ) := by
  simp only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  intro a
  have hx' : (j a).val x = (χ a : F) • x := (show ∀ b, (j b).val x = (χ b : F) • x by
    simpa only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, octonionAction_apply] using hx) a
  have hy' : (j a).val y = (ψ a : F) • y := (show ∀ b, (j b).val y = (ψ b : F) • y by
    simpa only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, octonionAction_apply] using hy) a
  change (j a).val (mul x y) = _
  rw [automorphism_mul,hx',hy',smul_mul,Atlas.SplitOctonion.mul_smul,smul_smul]
  rfl

private def weightSubgroup (j : A →* Atlas.G2.Model F) (h2 : (2 : F) ≠ 0) :
    Subgroup (A →* Fˣ) where
  carrier := {χ | (octonionAction j).characterWeightSpace χ ≠ ⊥}
  one_mem' := by
    intro he
    have hu : unit ∈ (octonionAction j).characterWeightSpace 1 := by
      simp only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
      intro a
      simpa only [MonoidHom.one_apply,Units.val_one,one_smul,octonionAction_apply] using automorphism_unit (j a)
    rw [he,Submodule.mem_bot] at hu
    exact unit_ne_zero hu
  mul_mem' := by
    intro χ ψ hχ hψ
    obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
    obtain ⟨y,hy,hny⟩ := weight_has_nonzero_norm j h2 ⟨ψ,hψ⟩
    intro he
    have hh := weight_mul j hx hy
    rw [he,Submodule.mem_bot] at hh
    have hh' : rightMulEquiv y hny x = rightMulEquiv y hny 0 := by
      simpa only [rightMulEquiv_apply,map_zero] using hh
    exact hx0 ((rightMulEquiv y hny).injective hh')
  inv_mem' := by
    intro χ hχ
    have he : χ⁻¹ = χ := by
      apply MonoidHom.ext
      intro a
      change (χ a)⁻¹ = χ a
      apply inv_eq_of_mul_eq_one_left
      rw [←map_mul,←pow_two,sign_pow,map_one]
    rwa [he]

private theorem octonion_elementary_card_le_eight [Finite A]
    (j : A →* Atlas.G2.Model F) (hj : Function.Injective j) (h2 : (2 : F) ≠ 0) :
    Nat.card A ≤ 8 := by
  classical
  let ρ := octonionAction j
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply hj
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    have hh := LinearMap.congr_fun hab x
    simpa only [ρ,octonionAction_apply] using hh
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have horder : (Nat.card A : F) ≠ 0 := by rw [hk,Nat.cast_pow]; exact pow_ne_zero _ h2
  let H := weightSubgroup j h2
  let : Finite H := (ρ.characterWeight_card_le horder).1
  let ev : A → (H →* Fˣ) := fun a =>
    { toFun := fun χ => χ.val a
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hev : Function.Injective ev := by
    intro a b hab
    apply ρ.eq_of_characterWeight_values_of_involutive hρ sign_pow h2
    intro χ
    exact congrArg (fun f : H →* Fˣ => f χ) hab
  have hexp : Monoid.exponent H ∣ 2 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro χ
    apply Subtype.ext
    apply MonoidHom.ext
    intro a
    change χ.val a ^ 2 = 1
    rw [←map_pow,sign_pow,map_one]
  let : HasEnoughRootsOfUnity F 2 :=
    ⟨⟨-1, IsPrimitiveRoot.neg_one (ringChar F) (by
      intro he
      have hz := ringChar.spec F
      rw [he] at hz
      exact h2 ((hz 2).mpr (dvd_refl 2)))⟩,rootsOfUnity.isCyclic F 2⟩
  let : HasEnoughRootsOfUnity F (Monoid.exponent H) := HasEnoughRootsOfUnity.of_dvd F hexp
  have hb := Nat.card_le_card_of_injective ev hev
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity H F] at hb
  let e : H ≃ ρ.CharacterWeight :=
    { toFun := fun χ => ⟨χ.val,χ.property⟩
      invFun := fun χ => ⟨χ.val,χ.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e] at hb
  exact hb.trans (by simpa only [Atlas.G2.carrier_finrank] using
    (ρ.characterWeight_card_le horder).2)

/-- The genuine split-octonion model in odd characteristic has two-rank at most three. -/
theorem odd_g2_twoRank_le_three {q : ℕ} (ho : Odd q)
    {Q : Type*} [Group Q] [Finite Q] (hm : ClassificationModels.IsG2At Q q) :
    primeRank 2 Q ≤ 3 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [primeRank_congr 2 e]
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro A hA
  let := hA
  exact octonion_elementary_card_le_eight A.subtype A.subtype_injective
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho (by simpa using hF))


open CFSG.Quasithin.Chapter12.Section02
open ClassificationModels

/-- The remaining placed models after the octonion rank exclusion. The
  full projective parameters and Fermat/Mersenne restrictions are retained. -/
def RemainingPlacedModelsWithoutG2 (Q : Type*) [Group Q] : Prop :=
  (Nonempty (Q ≃* Janko4.Model) ∨ Nonempty (Q ≃* Rudvalis.Model)) ∨
  (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSp Q 2 p) ∨
  (∃ r : ℕ, r.Prime ∧ (∃ k : ℕ, r = 2 ^ (2 ^ k) + 1) ∧ ClassicalGroup.IsPSL Q 4 r) ∨
  (∃ s : ℕ, s.Prime ∧ (∃ b : ℕ, s + 1 = 2 ^ b) ∧ ClassicalGroup.IsPSU Q 4 s)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {Q : Type*} [Group Q] [Finite Q]
include D S

/-- The actual rank-six elementary image of the covering residual excludes
  every odd G₂ row, without a Sylow-containment hypothesis. -/
theorem NaturalCoverImage.not_odd_g2 (h : NaturalCoverImage D Q)
    {q : ℕ} (ho : Odd q) (hm : IsG2At Q q) : False := by
  have hlo := h.twoRank_ge_six D S
  have hup := odd_g2_twoRank_le_three ho hm
  omega

/-- Apply the octonion bound to the actual B-model image of the placed residual. -/
theorem NaturalCoverImage.theoremB_models_without_g2 (h : NaturalCoverImage D Q)
    (hm : ChapterA.Section02.IsTheoremBModel Q) : RemainingPlacedModelsWithoutG2 Q := by
  rcases h.theoremB_models D S hm with hs | ho
  · exact Or.inl hs
  rcases ho with hp | ⟨p,_,ho,hm⟩ | hl | hu
  · exact Or.inr (Or.inl hp)
  · exact (h.not_odd_g2 D S ho hm).elim
  · exact Or.inr (Or.inr (Or.inl hl))
  · exact Or.inr (Or.inr (Or.inr hu))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

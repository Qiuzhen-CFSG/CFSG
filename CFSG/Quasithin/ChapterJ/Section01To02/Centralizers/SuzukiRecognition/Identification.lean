module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.RecognitionInput
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Identification.ModelSelection
public import BenderSuzuki.SE.Final
public import Theory.GroupAction.FourGroupOddCenter

/-!
# Recognition of the J.2.9 residual as Sz(8)

The residual geometry supplies a literal Sylow subgroup, the square-one
subgroup and uniform involution centralizers. Strong embedding restricts to
the involution-generated subgroup, where involution conjugacy shows that the
ambient quotient is a two-group. Two-perfectness eliminates this quotient;
the four-group fixed-point argument eliminates the odd core. Theorem SE then
recognizes the whole group as a concrete Bender model. Its Sylow and center
orders select Sz(8).

The intrinsic recognition theorem has no additional simplicity or SQTK
premise. Its application to the literal subgroup `Choices.Ls` retains only
the earlier J.2.3/J.2.7 geometry and local non-core witness, whose construction
belongs to the parent J.2.9 assembly.

Source: Aschbacher--Smith, J.2.9, printed p.438 (PDF p.449).
-/

public section

open Subgroup
open BenderSuzuki.PFchapter1section1

namespace CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition

variable {X : Type*} [Group X] [Finite X]

/-- The exact residual contract gives Theorem SE for its normalizer.

The `IsPPerfect` premise is retained in this boundary because it is part of
the source residual contract; the TI and strong-embedding deduction itself
uses only the literal square-one, centralizer and proper-normalizer clauses.
-/
theorem theoremSE_of_residual_contract
    (hperfect : IsPPerfect 2 X)
    (P : Sylow 2 X) (hPcard : Nat.card P = 64)
    (V : Subgroup X) (hVcard : Nat.card V = 8)
    (hV : ∀ x : X, x ∈ V ↔ x ∈ (P : Subgroup X) ∧ x ^ 2 = 1)
    (hC : ∀ v : X, v ∈ V → v ≠ 1 →
      centralizer ({v} : Set X) = (P : Subgroup X))
    (hproper : normalizer (V : Set X) ≠ ⊤) :
    BenderSuzuki.TheoremSEConclusion (normalizer (V : Set X)) := by
  let _ := hperfect
  let _ := hPcard
  let _ := hVcard
  have hM : BenderSuzuki.IsStronglyEmbedded (normalizer (V : Set X)) :=
    CFSG.Quasithin.ChapterJ.Centralizers.stronglyEmbedded_of_uniform_centralizers
      P V hV hC hproper
  exact BenderSuzuki.theorem_SE (normalizer (V : Set X)) hM

/-! The order-eight square-one subgroup already rules out the rank-zero
branch in Theorem SE.  This is kept as a separate boundary because it is
independent of the later model and odd-kernel calculations. -/

theorem residual_involutionCore_rank_two
    (V : Subgroup X) (hVcard : Nat.card V = 8)
    (hV : ∀ x : X, x ∈ V → x ^ 2 = 1) :
    TwoRankAtLeastTwo (BenderSuzuki.involutionCore X) := by
  have hsqV : ∀ x : V, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    exact hV (x : X) x.property
  let _ : IsMulCommutative V :=
    BenderSuzuki.PFchapter1section1.isMulCommutative_of_forall_sq_one hsqV
  obtain ⟨E, hEcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := V) 2
      (show 2 ^ 2 ∣ Nat.card V by rw [hVcard]; norm_num)
  let A : Subgroup X := E.map V.subtype
  have hAcard : Nat.card A = 4 := by
    dsimp [A]
    rw [Subgroup.card_map_of_injective V.subtype_injective]
    simpa using hEcard
  have hAcore : A ≤ BenderSuzuki.involutionCore X := by
    intro x hx
    rw [BenderSuzuki.involutionCore_eq_closure]
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hySq : (y : X) ^ 2 = 1 := by
      simpa [pow_two] using congrArg (fun z : V => (z : X)) (hsqV y)
    by_cases hyOne : (y : X) = 1
    · change (y : X) ∈ Subgroup.closure (BenderSuzuki.involutionsSet X)
      rw [hyOne]
      exact Subgroup.one_mem _
    · apply Subgroup.subset_closure
      exact ⟨hyOne, hySq⟩
  let Ecore : Subgroup (BenderSuzuki.involutionCore X) :=
    A.subgroupOf (BenderSuzuki.involutionCore X)
  have hEcorecard : Nat.card Ecore = 4 := by
    rw [natCard_subgroupOf_eq A (BenderSuzuki.involutionCore X) hAcore]
    exact hAcard
  refine ⟨Ecore, hEcorecard, ?_⟩
  intro x
  have hxAcore : (x : BenderSuzuki.involutionCore X) ∈ Ecore := x.property
  change ((x : BenderSuzuki.involutionCore X) : X) ∈ A at hxAcore
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hxAcore
  apply Subtype.ext
  apply Subtype.ext
  change ((x : BenderSuzuki.involutionCore X) : X) ^ 2 = 1
  rw [← hxy]
  change ((y : V) : X) ^ 2 = 1
  simpa [pow_two] using congrArg (fun z : V => (z : X)) (hsqV y)

theorem residual_four_subgroup
    (V : Subgroup X) (hVcard : Nat.card V = 8)
    (hV : ∀ x : X, x ∈ V → x ^ 2 = 1) :
    ∃ A : Subgroup X, Nat.card A = 4 ∧ A ≤ V ∧
      ∀ x : A, x ^ 2 = 1 := by
  have hsqV : ∀ x : V, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    exact hV (x : X) x.property
  let _ : IsMulCommutative V :=
    BenderSuzuki.PFchapter1section1.isMulCommutative_of_forall_sq_one hsqV
  obtain ⟨E, hEcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := V) 2
      (show 2 ^ 2 ∣ Nat.card V by rw [hVcard]; norm_num)
  let A : Subgroup X := E.map V.subtype
  have hAcard : Nat.card A = 4 := by
    dsimp [A]
    rw [Subgroup.card_map_of_injective V.subtype_injective]
    simpa using hEcard
  have hAV : A ≤ V := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.property
  refine ⟨A, hAcard, hAV, ?_⟩
  intro x
  rcases Subgroup.mem_map.mp x.property with ⟨y, hy, hxy⟩
  apply Subtype.ext
  change (x : X) ^ 2 = 1
  rw [← hxy]
  simpa [pow_two] using congrArg (fun z : V => (z : X)) (hsqV y)

theorem twoPrimeCore_eq_bot_of_residual_contract
    (P : Sylow 2 X) (V : Subgroup X) (hVcard : Nat.card V = 8)
    (hV : ∀ x : X, x ∈ V ↔ x ∈ (P : Subgroup X) ∧ x ^ 2 = 1)
    (hC : ∀ v : X, v ∈ V → v ≠ 1 →
      centralizer ({v} : Set X) = (P : Subgroup X)) :
    BenderSuzuki.twoPrimeCore X = ⊥ := by
  by_contra hObot
  let O : Subgroup X := BenderSuzuki.twoPrimeCore X
  have hOne : O ≠ ⊥ := by simpa [O] using hObot
  let : Nontrivial O := (Subgroup.nontrivial_iff_ne_bot O).mpr hOne
  obtain ⟨A, hAcard, hAV, hAsq⟩ :=
    residual_four_subgroup V hVcard (fun x hx => (hV x).mp hx |>.2)
  let : IsElementaryAbelian 2 A := {
    toIsMulCommutative :=
      BenderSuzuki.PFchapter1section1.isMulCommutative_of_forall_sq_one hAsq
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hAsq }
  let : MulDistribMulAction A O :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A O le_normalizer_of_normal
  let rho : A →* MulAut O := MulDistribMulAction.toMulAut A O
  obtain ⟨t, ht1, x, hx1, hfix⟩ :=
    Theory.GroupAction.exists_nontrivial_fixed_of_elementaryFour hAcard rho
  have htV : (t : X) ∈ V := hAV t.property
  have htne : (t : X) ≠ 1 := by
    intro ht
    apply ht1
    exact Subtype.ext ht
  have hfix' : ((t : X) * (x : X) * (t : X)⁻¹) = (x : X) := by
    change ((t : A) • x : O) = x at hfix
    have h := congrArg (fun z : O => (z : X)) hfix
    simpa only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using h
  have htx : (t : X) * (x : X) = (x : X) * (t : X) := by
    calc
      (t : X) * (x : X) =
          ((t : X) * (x : X) * (t : X)⁻¹) * (t : X) := by simp [mul_assoc]
      _ = (x : X) * (t : X) := by rw [hfix']
  have hxP : (x : X) ∈ (P : Subgroup X) := by
    rw [← hC (t : X) htV htne]
    exact Subgroup.mem_centralizer_singleton_iff.mpr htx.symm
  have hOcop : (2 : ℕ).Coprime (Nat.card O) := by
    simpa [O, BenderSuzuki.twoPrimeCore] using
      (pPrimeCore_coprime_card (p := 2) (G := X))
  have hcop : (orderOf (x : X)).Coprime (Nat.card O) := by
    have htmp := P.isPGroup'.orderOf_coprime hOcop (⟨x, hxP⟩ : P)
    rw [← Subgroup.orderOf_coe] at htmp
    exact htmp
  have hdiv : orderOf (x : X) ∣ Nat.card O := by
    exact Subgroup.orderOf_dvd_natCard O x.property
  have hxo : orderOf (x : X) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdiv
  apply hx1
  apply Subtype.ext
  exact orderOf_eq_one_iff.mp (by simpa only [Subgroup.orderOf_coe] using hxo)

/-! The rank alternative in Theorem SE is therefore discharged for the
residual contract itself. -/

theorem theoremSEBender_of_residual_contract
    (hperfect : IsPPerfect 2 X)
    (P : Sylow 2 X) (hPcard : Nat.card P = 64)
    (V : Subgroup X) (hVcard : Nat.card V = 8)
    (hV : ∀ x : X, x ∈ V ↔ x ∈ (P : Subgroup X) ∧ x ^ 2 = 1)
    (hC : ∀ v : X, v ∈ V → v ≠ 1 →
      centralizer ({v} : Set X) = (P : Subgroup X))
    (hproper : normalizer (V : Set X) ≠ ⊤) :
    BenderSuzuki.TheoremSEBenderConclusion (normalizer (V : Set X)) := by
  have hSE := theoremSE_of_residual_contract
    hperfect P hPcard V hVcard hV hC hproper
  have hrank : TwoRankAtLeastTwo (BenderSuzuki.involutionCore X) :=
    residual_involutionCore_rank_two V hVcard (fun x hx => (hV x).mp hx |>.2)
  exact hSE.resolve_left (fun h => h hrank)

end CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition

namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices

open ChapterI.Section06To08

variable {G : Type*} [Group G] [Finite G]
variable {d : LocalSetup G} (c : Choices d)

/-- Apply the preceding boundary to the literal residual subgroup `Lₛ`.

The subgroup and square-one set are kept in their source forms
`S₁.subgroupOf Lₛ` and `V.subgroupOf Lₛ`; no model isomorphism is hidden in
this wrapper.  The remaining arguments are exactly the outputs of
`residual_recognition_inputs` together with the two order calculations.
-/
theorem theoremSE_of_residual_inputs
    (hperfect : IsPPerfect 2 c.Ls)
    (P : Sylow 2 c.Ls) (hP : (P : Subgroup c.Ls) = c.S1.subgroupOf c.Ls)
    (hPcard : Nat.card P = 64)
    (hVcard : Nat.card d.V = 8)
    (hVL : d.V ≤ c.Ls)
    (hV : ∀ x : c.Ls, x ∈ d.V.subgroupOf c.Ls ↔
      x ∈ c.S1.subgroupOf c.Ls ∧ x ^ 2 = 1)
    (hC : ∀ x : c.Ls, x ∈ d.V.subgroupOf c.Ls → x ≠ 1 →
      centralizer ({x} : Set c.Ls) = c.S1.subgroupOf c.Ls)
    (hproper : normalizer (d.V.subgroupOf c.Ls : Set c.Ls) ≠ ⊤) :
    BenderSuzuki.TheoremSEConclusion
      (normalizer (d.V.subgroupOf c.Ls : Set c.Ls)) := by
  apply CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition.theoremSE_of_residual_contract
    hperfect P hPcard
    (d.V.subgroupOf c.Ls) (by
      rw [natCard_subgroupOf_eq d.V c.Ls hVL]
      exact hVcard)
  · intro x
    simpa only [hP] using hV x
  · intro x hx hx1
    rw [hC x hx hx1, hP]
  · exact hproper

theorem theoremSEBender_of_residual_inputs
    (hperfect : IsPPerfect 2 c.Ls)
    (P : Sylow 2 c.Ls) (hP : (P : Subgroup c.Ls) = c.S1.subgroupOf c.Ls)
    (hPcard : Nat.card P = 64)
    (hVcard : Nat.card d.V = 8)
    (hVL : d.V ≤ c.Ls)
    (hV : ∀ x : c.Ls, x ∈ d.V.subgroupOf c.Ls ↔
      x ∈ c.S1.subgroupOf c.Ls ∧ x ^ 2 = 1)
    (hC : ∀ x : c.Ls, x ∈ d.V.subgroupOf c.Ls → x ≠ 1 →
      centralizer ({x} : Set c.Ls) = c.S1.subgroupOf c.Ls)
    (hproper : normalizer (d.V.subgroupOf c.Ls : Set c.Ls) ≠ ⊤) :
    BenderSuzuki.TheoremSEBenderConclusion
      (normalizer (d.V.subgroupOf c.Ls : Set c.Ls)) := by
  apply CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition.theoremSEBender_of_residual_contract
    hperfect P hPcard
    (d.V.subgroupOf c.Ls) (by
      rw [natCard_subgroupOf_eq d.V c.Ls hVL]
      exact hVcard)
  · intro x
    simpa only [hP] using hV x
  · intro x hx hx1
    rw [hC x hx hx1, hP]
  · exact hproper

theorem twoPrimeCore_eq_bot_of_residual_inputs
    (P : Sylow 2 c.Ls) (hP : (P : Subgroup c.Ls) = c.S1.subgroupOf c.Ls)
    (hVcard : Nat.card d.V = 8)
    (hVL : d.V ≤ c.Ls)
    (hV : ∀ x : c.Ls, x ∈ d.V.subgroupOf c.Ls ↔
      x ∈ c.S1.subgroupOf c.Ls ∧ x ^ 2 = 1)
    (hC : ∀ x : c.Ls, x ∈ d.V.subgroupOf c.Ls → x ≠ 1 →
      centralizer ({x} : Set c.Ls) = c.S1.subgroupOf c.Ls) :
    BenderSuzuki.twoPrimeCore c.Ls = ⊥ := by
  apply CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition.twoPrimeCore_eq_bot_of_residual_contract
    P (d.V.subgroupOf c.Ls) (by
      rw [natCard_subgroupOf_eq d.V c.Ls hVL]
      exact hVcard)
  · intro x
    simpa only [hP] using hV x
  · intro x hx hx1
    rw [hC x hx hx1, hP]

end CFSG.Quasithin.ChapterJ.Centralizers.Choices

open Subgroup BenderSuzuki BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition
variable {X : Type*} [Group X] [Finite X]

/-- Conjugacy inside the involution core makes its quotient a two-group;
two-perfectness then eliminates the quotient. This discharges the extension
part of the source recognition without an outer-automorphism hypothesis. -/
theorem involutionCore_eq_top_of_residual_contract
    (hperfect : IsPPerfect 2 X)
    (P : Sylow 2 X) (V : Subgroup X) (hVcard : Nat.card V = 8)
    (hV : ∀ x : X, x ∈ V ↔ x ∈ (P : Subgroup X) ∧ x ^ 2 = 1)
    (hC : ∀ v : X, v ∈ V → v ≠ 1 →
      centralizer ({v} : Set X) = (P : Subgroup X))
    (hproper : normalizer (V : Set X) ≠ ⊤) :
    involutionCore X = ⊤ := by
  have hM : IsStronglyEmbedded (normalizer (V : Set X)) :=
    CFSG.Quasithin.ChapterJ.Centralizers.stronglyEmbedded_of_uniform_centralizers
      P V hV hC hproper
  let L := involutionCore X
  have hML := hM.comap_involutionCore
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v, hv⟩ := exists_ne (1 : V)
  have hvI : IsInvolution (v : X) :=
    ⟨fun he => hv (Subtype.ext he), ((hV v).mp v.property).2⟩
  have hvL : (v : X) ∈ L := Subgroup.subset_closure hvI
  let q : X →* X ⧸ L := QuotientGroup.mk' L
  have hsurj : Function.Surjective (q.comp (P : Subgroup X).subtype) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective L y
    let w := rightConjugateElem (v : X) x
    have hwI : IsInvolution w := isInvolution_rightConjugateElem hvI
    have hwL : w ∈ L := Subgroup.subset_closure hwI
    obtain ⟨g, hg⟩ := hML.involutions_conjugate
      (IsInvolution.subtype hvI hvL) (IsInvolution.subtype hwI hwL)
    have hg' : (g : X)⁻¹ * (v : X) * (g : X) = x⁻¹ * (v : X) * x :=
      congrArg (fun z : L => (z : X)) hg
    have hxP : x * (g : X)⁻¹ ∈ (P : Subgroup X) := by
      rw [← hC v v.property hvI.ne_one]
      apply mem_centralizer_singleton_iff.mpr
      calc
        (x * (g : X)⁻¹) * (v : X) =
            x * ((g : X)⁻¹ * (v : X) * (g : X)) * (g : X)⁻¹ := by group
        _ = x * (x⁻¹ * (v : X) * x) * (g : X)⁻¹ := by rw [hg']
        _ = (v : X) * (x * (g : X)⁻¹) := by group
    refine ⟨⟨x * (g : X)⁻¹, hxP⟩, ?_⟩
    change q (x * (g : X)⁻¹) = q x
    have hgq : q (g : X) = 1 := (QuotientGroup.eq_one_iff (g : X)).mpr g.property
    rw [map_mul, map_inv, hgq, inv_one, mul_one]
  exact hperfect L inferInstance (P.isPGroup'.of_surjective _ hsurj)

end CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition
open Subgroup BenderSuzuki
namespace CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition
variable {X : Type*} [Group X] [Finite X]

/-- The odd core and the possible extension in Theorem SE both vanish under
this residual contract. Thus the whole group, rather than just a section,
belongs to one of the three concrete Bender families. -/
theorem benderGroup_of_residual_contract
    (hperfect : IsPPerfect 2 X)
    (P : Sylow 2 X) (hPcard : Nat.card P = 64)
    (V : Subgroup X) (hVcard : Nat.card V = 8)
    (hV : ∀ x : X, x ∈ V ↔ x ∈ (P : Subgroup X) ∧ x ^ 2 = 1)
    (hC : ∀ v : X, v ∈ V → v ≠ 1 →
      centralizer ({v} : Set X) = (P : Subgroup X))
    (hproper : normalizer (V : Set X) ≠ ⊤) :
    IsSimpleBenderGroup X := by
  have hSE := theoremSEBender_of_residual_contract
    hperfect P hPcard V hVcard hV hC hproper
  have hLtop := involutionCore_eq_top_of_residual_contract
    hperfect P V hVcard hV hC hproper
  have hO := twoPrimeCore_eq_bot_of_residual_contract P V hVcard hV hC
  let L := involutionCore X
  let e : L ≃* X := (MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv
  have hcoremap : (twoPrimeCore L).map e.toMonoidHom = ⊥ := by
    rw [← hO]
    exact pPrimeCore_map_iso (p := 2) e
  have hcore : twoPrimeCore L = ⊥ :=
    ((twoPrimeCore L).map_eq_bot_iff_of_injective e.injective).mp hcoremap
  let q : (L ⧸ twoPrimeCore L) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  exact hSE.1.map_mulEquiv (q.trans e)

/-- Recognition of Sz(8) from the intrinsic geometry supplied by J.2.9.
No ambient SQTK or simplicity hypothesis is needed. -/
theorem suzuki_of_residual_contract
    (hperfect : IsPPerfect 2 X)
    (P : Sylow 2 X) (hPcard : Nat.card P = 64)
    (V : Subgroup X) (hVcard : Nat.card V = 8)
    (hV : ∀ x : X, x ∈ V ↔ x ∈ (P : Subgroup X) ∧ x ^ 2 = 1)
    (hC : ∀ v : X, v ∈ V → v ≠ 1 →
      centralizer ({v} : Set X) = (P : Subgroup X))
    (hproper : normalizer (V : Set X) ≠ ⊤) :
    Nonempty (X ≃* MatrixGroups.SuzukiMatrixGroup 1) :=
  suzuki_of_bender_residual_geometry
    (benderGroup_of_residual_contract hperfect P hPcard V hVcard hV hC hproper)
    P hPcard V hVcard hV hC

end CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition

namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalSetup G} (c : Choices d)

/-- Apply the intrinsic recognition theorem to the literal Sylow and V in Lₛ. -/
theorem suzuki_of_residual_inputs
    (P : Sylow 2 c.Ls) (hP : (P : Subgroup c.Ls) = c.S1.subgroupOf c.Ls)
    (hPcard : Nat.card P = 64)
    (hVL : d.V ≤ c.Ls)
    (hV : ∀ x : c.Ls, x ∈ d.V.subgroupOf c.Ls ↔
      x ∈ c.S1.subgroupOf c.Ls ∧ x ^ 2 = 1)
    (hC : ∀ x : c.Ls, x ∈ d.V.subgroupOf c.Ls → x ≠ 1 →
      centralizer ({x} : Set c.Ls) = c.S1.subgroupOf c.Ls)
    (hproper : normalizer (d.V.subgroupOf c.Ls : Set c.Ls) ≠ ⊤) :
    Nonempty (c.Ls ≃* MatrixGroups.SuzukiMatrixGroup 1) := by
  apply SuzukiRecognition.suzuki_of_residual_contract c.Ls_isPPerfect P hPcard
    (d.V.subgroupOf c.Ls) (by
      rw [natCard_subgroupOf_eq d.V c.Ls hVL]
      exact d.ru1.card_V)
  · intro x
    simpa only [hP] using hV x
  · intro x hx hx1
    rw [hC x hx hx1, hP]
  · exact hproper

/-- The recognition part of J.2.9(1), from the preceding J.2.3/J.2.7
witnesses and the explicit local non-core witness. The parent theorem retains
construction of those witnesses and the centralizer product and outer action. -/
theorem Ls_suzuki_of_local_geometry [IsElementaryAbelian 2 c.S0]
    (P : Sylow 2 c.Gs) (hP : (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs)
    (e : P ≃* c.S0 × c.S1)
    (he : ∀ x : P, ((x : c.Gs) : G) = ((e x).1 : G) * ((e x).2 : G))
    (hS0 : Nat.card c.S0 = 4) (hTs : Nat.card c.Ts = 256)
    (hsuzuki : IsSuzukiTwoGroup c.S1) (htrans : c.B7TransitiveOnV)
    (hCL : d.L ⊓ c.Gs = c.Ts ⊔ c.B7)
    (hH : centralizer ({c.z} : Set G) = d.toTypeRuSetup.H)
    (hHs : d.toTypeRuSetup.H ⊓ c.Gs = c.Ts)
    (hzV : c.z ∈ d.V) (hz1 : c.z ≠ 1)
    (hsfusion : ∀ t ∈ d.toTypeRuSetup.H, IsConj c.s t →
      ∃ h ∈ d.toTypeRuSetup.H, h * c.s * h⁻¹ = t)
    {t v : G} (hst : IsConj c.s t) (hv : v ∈ centralizer ({t} : Set G))
    (hzv : IsConj c.z v) (hvn : v ∉ (centralizer ({t} : Set G)).pCoreIn 2) :
    Nonempty (c.Ls ≃* MatrixGroups.SuzukiMatrixGroup 1) := by
  obtain ⟨_, _, _, Q, hQ, hV, hC, hproper, _⟩ :=
    c.residual_recognition_inputs P hP e he hsuzuki htrans hCL hH hHs
      hzV hz1 hsfusion hst hv hzv hvn
  have hQcard : Nat.card Q = 64 := by
    rw [hQ, natCard_subgroupOf_eq c.S1 c.Ls c.S1_le_Ls]
    exact c.S1_card_of_local_product P hP e hS0 hTs
  exact c.suzuki_of_residual_inputs Q hQ hQcard
    ((c.V_le_S1 hsuzuki.2.1 htrans).trans c.S1_le_Ls) hV hC hproper

end CFSG.Quasithin.ChapterJ.Centralizers.Choices

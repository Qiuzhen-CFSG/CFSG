module

public import Theory.SpecificGroups.SU3.ComparatorModel
public import BenderSuzuki.SE.Models
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.GroupTheory.RankOneSylowExtension.Overgroups
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms.Unconditional

/-!
# Model and Borel inputs for the unitary upper E-bound

The literal shared PSU₃ carrier is identified inside its original PGL.
The concrete Bender model proves nonabelianness, and the rank-one Sylow
calculation constructs `B = N_G(S ∩ L)` for every ambient Sylow subgroup.
The quotient `G/L` is a two-group, so the original supplement hypothesis
works for every S. Finally, faithful conjugation gives the correct bound
f+1 on elementary subgroups in an extension, while the inner rank is f.

These are inputs to the local E-member construction, not the completed
upper E-generation theorem. Source: Aschbacher–Smith E.1.14(1), p.214;
F.1.3(1), pp.259–260; and the automorphism rank table on p.356.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper.UnitaryLocal
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.Converse
open CFSG.Quasithin.ChapterF.Source Theory.GroupTheory
open scoped IsMulCommutative

/-- The actual model supplies the nonabelianness needed by simple-socle assembly. -/
theorem nonabelian {G : Type*} [Group G] [Finite G]
    {f : ℕ} (hf : 2 ≤ f) (e : G ≃* PSU3Model f) : ¬ IsMulCommutative G := by
  let : NeZero f := ⟨by omega⟩
  have hmodel : BenderSuzuki.IsSimpleBenderGroup G :=
    .isPSU3 ⟨f, hf, UField f, inferInstance, inferInstance, uform f,
      uform_form f, card_UField f (by omega), card_fixed_UField f (by omega),
      ⟨e.trans (MulEquiv.subgroupCongr (psu3Model_eq_projective f))⟩⟩
  intro h
  let := h
  exact hmodel.not_commutative (fun x y => mul_comm x y)

/-- The full intrinsic rank-one Borel theorem on the source carrier. -/
theorem intrinsic_facts {G : Type*} [Group G] [Finite G]
    {f : ℕ} (hf : 2 ≤ f) (e : G ≃* PSU3Model f) (T : Sylow 2 G) :
    RankOneSylowFacts T := by
  let : NeZero f := ⟨by omega⟩
  apply rankOneSylowFacts_of_equiv T (e.trans (MulEquiv.subgroupCongr (psu3Model_eq_projective f)))
  exact rankOneSylowFacts_psu3 (uform f) f (by omega)
    (card_UField f (by omega)) (uconj_apply f) _

variable {G : Type*} [Group G] [Finite G]

/-- The literal normalizer of `S ∩ L` is proper and contains every proper
overgroup of S in the ambient extension. -/
theorem borel_properties (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (T₀ S : Sylow 2 G) (hgen : L ⊔ (T₀ : Subgroup G) = ⊤) :
    normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ≠ ⊤ ∧
    (S : Subgroup G) ≤ normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
    ∀ M : Subgroup G, (S : Subgroup G) ≤ M → M ≠ ⊤ →
      M ≤ normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  have hquot := isPGroup_quotient_of_sup_eq_top L (T₀ : Subgroup G) T₀.isPGroup' hgen
  have hgenS : L ⊔ (S : Subgroup G) = ⊤ := by
    rw [sup_comm]
    exact S.sup_eq_top_of_quotient_isPGroup L hquot
  exact RankOneSylowExtension.ambient_normalizer_properties L S hgenS
    (fun P => (intrinsic_facts hf e P).proper.ne)
    (fun P M hPM hM => (intrinsic_facts hf e P).unique_maximal M hPM
      (lt_top_iff_ne_top.mpr hM))

/-- Every ambient Sylow has a proper subgroup containing all its proper overgroups. -/
theorem model_borel (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (T₀ S : Sylow 2 G) (hgen : L ⊔ (T₀ : Subgroup G) = ⊤) :
    ∃ B : Subgroup G, B ≠ ⊤ ∧ (S : Subgroup G) ≤ B ∧
      ∀ M : Subgroup G, (S : Subgroup G) ≤ M → M ≠ ⊤ → M ≤ B :=
  ⟨_, borel_properties L hf e T₀ S hgen⟩

/-- The exact intrinsic two-rank of the genuine PSU₃ model. -/
theorem inner_rank {G : Type*} [Group G] [Finite G]
    {f : ℕ} (hf : 2 ≤ f) (e : G ≃* PSU3Model f) : primeRank 2 G = f := by
  let : NeZero f := ⟨by omega⟩
  rw [primeRank_equiv 2 (e.trans (MulEquiv.subgroupCongr (psu3Model_eq_projective f)))]
  exact HermitianForm.EvenTwoRank.two_rank (uform f) (by omega)
    (card_UField f (by omega)) (uconj_apply f)

/-- The outer extension can add one elementary generator. -/
theorem ambient_elementary_rank (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3Model f)
    (hC : centralizer (L : Set G) = ⊥)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) : Group.rank A ≤ f + 1 := by
  let : NeZero f := ⟨by omega⟩
  let : IsElementaryAbelian 2 A := hA
  let j := (MulAut.congr (e.trans (MulEquiv.subgroupCongr (psu3Model_eq_projective f)))).toMonoidHom.comp
    (MulAut.conjNormal : G →* MulAut L)
  have hj : Function.Injective j := (MulAut.congr _).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot L hC)
  exact (A.rank_le_primeRank 2 hA.isPGroup).trans
    ((primeRank_le_of_injective 2 j hj).trans
      (HermitianForm.EvenTwoRank.automorphism_two_rank_le (uform f) hf
        (card_UField f (by omega)) (uconj_apply f)))

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper.UnitaryLocal

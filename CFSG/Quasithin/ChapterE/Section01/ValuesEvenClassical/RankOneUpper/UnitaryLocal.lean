module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.UnitaryLocal.Construction
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.UnitaryLocal.OuterElementary
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.UnitaryLocal.RadicalMember
public import CFSG.Quasithin.Defs

/-!
# Local inputs for PSU₃ almost-simple upper E-generation

The concrete model supplies nonabelianness, intrinsic rank f, ambient
rank at most f+1, and a proper Borel bounding every proper Sylow overgroup.
The linear fixed subgroup of an outer involution is identified with the
actual fixed-field PSL₂. The outer-rank calculation puts a Sylow subgroup of
that fixed subgroup inside every elementary subgroup of rank greater than f.
The radical-quotient calculation then supplies the literal E.1.5 witness.
This file assembles those facts into the local witness used by the parent
upper-generation argument; it does not assert the final generation theorem.

Source: Aschbacher–Smith E.1.1–6 and E.1.14(1), printed pp.209–211, 214.
The source cites Aschbacher (1982), Lemma 4.7, DOI 10.2307/2374202.
The results here use the separately proved concrete model theorems.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper.UnitaryLocal

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

/-! The source keeps `C_G(L) = 1` and `O₂(G) = 1` as separate local inputs.
They are discharged by the simple-socle branch in the parent assembly. -/

/-- The matrix model gives the nonabelianness required by the source branch. -/
theorem generalizedFitting_nonabelian {f : ℕ} (hf : 2 ≤ f)
    (e : generalizedFitting G ≃* PSU3Model f) :
    ¬ IsMulCommutative (generalizedFitting G) :=
  nonabelian hf e

/-- A large elementary subgroup has a concrete E-member outside the PSU₃
Borel. The returned `B` is the literal normalizer of `S ∩ L`; it contains
every proper overgroup of `S`, as required by the rank-one assembly. -/
theorem exists_local_member_of_large_rank
    {f : ℕ} (hf : 2 ≤ f)
    (L : Subgroup G) [L.Normal] (e : L ≃* PSU3Model f)
    (hC : centralizer (L : Set G) = ⊥) (hO : pCore 2 G = ⊥)
    (T₀ S : Sylow 2 G) (hgen : L ⊔ (T₀ : Subgroup G) = ⊤)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAS : A ≤ (S : Subgroup G)) (hr : f < Group.rank A) :
    ∃ B : Subgroup G, B ≠ ⊤ ∧
      (S : Subgroup G) ≤ B ∧
      (∀ M : Subgroup G, (S : Subgroup G) ≤ M → M ≠ ⊤ → M ≤ B) ∧
      ∃ t : G, t ∈ A ∧ t ∉ L ∧ t ^ 2 = 1 ∧
        ∃ H : Subgroup G, IsEMemberAt f (S : Subgroup G) A H ∧ ¬ H ≤ B := by
  let B : Subgroup G :=
    normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G)
  have hBprops := borel_properties L hf e T₀ S hgen
  have hBtop : B ≠ ⊤ := by simpa [B] using hBprops.1
  have hSB : (S : Subgroup G) ≤ B := by simpa [B] using hBprops.2.1
  have hB : ∀ M : Subgroup G, (S : Subgroup G) ≤ M → M ≠ ⊤ → M ≤ B := by
    simpa [B] using hBprops.2.2
  obtain ⟨t, htA, htL, ht2⟩ := exists_outer_involution_of_large_rank
    L hf e A hA hr
  obtain ⟨P, hPA⟩ := exists_sylow_fixedCore_map_le L hf e hC A hA hr
    t htA htL ht2
  obtain ⟨hE, hEsc⟩ := isEMemberAt_localCandidate L hf e hC hO S A hA hAS hr
    htA htL ht2 P hPA
  exact ⟨B, hBtop, hSB, hB, t, htA, htL, ht2, _, hE, by simpa [B] using hEsc⟩

/-- The source-shaped wrapper for an SQTK group with simple generalized
Fitting subgroup. The SQTK and simplicity hypotheses are retained at this
boundary for the parent classification assembly; the local calculation uses
only the displayed model, normality, centralizer and p-core inputs. -/
theorem exists_local_member_of_sqtk_psu3 {K : GroupClass} (_hG : IsSQTK K G)
    [IsSimpleGroup (generalizedFitting G)] {f : ℕ} (hf : 2 ≤ f)
    (T₀ S : Sylow 2 G)
    (hgen : generalizedFitting G ⊔ (T₀ : Subgroup G) = ⊤)
    (e : generalizedFitting G ≃* PSU3Model f)
    (hC : centralizer (generalizedFitting G : Set G) = ⊥)
    (hO : pCore 2 G = ⊥) (A : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hAS : A ≤ (S : Subgroup G))
    (hr : f < Group.rank A) :
    ∃ B : Subgroup G, B ≠ ⊤ ∧
      (S : Subgroup G) ≤ B ∧
      (∀ M : Subgroup G, (S : Subgroup G) ≤ M → M ≠ ⊤ → M ≤ B) ∧
      ∃ t : G, t ∈ A ∧ t ∉ generalizedFitting G ∧ t ^ 2 = 1 ∧
        ∃ H : Subgroup G, IsEMemberAt f (S : Subgroup G) A H ∧ ¬ H ≤ B := by
  exact exists_local_member_of_large_rank hf (generalizedFitting G) e hC hO T₀ S hgen
    A hA hAS hr

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper.UnitaryLocal

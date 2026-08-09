/-
Comparator solution.  The definitions come from `Defs.lean`, shared with the challenge; the
four statements are the challenge's, proved.  Nobody needs to read this file.

It does not import `Challenge`, so nothing here can influence what the challenge asks for.
-/
module
public import Comparator.BenderSuzukiConverse.Defs
import BenderSuzuki.Converse.StronglyEmbedded

namespace BSConverse

universe u v w

/-! ## 4. The claims -/

noncomputable section

open BenderSuzuki BenderSuzuki.PFchapter1section1 BenderSuzuki.MatrixGroups
open BenderSuzuki.Converse BenderSuzuki.PFAppendixIII

/-- The challenge's copy of Hypothesis (A) implies the repository's. -/
private theorem toRepo {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t : G} (h : HypothesisA G Ω H D Q t) :
    PFchapter1section1.HypothesisA G Ω H D Q t :=
  ⟨⟨h.A1.two_transitive, h.A1.point_stabilizer, h.A1.involution_t, h.A1.t_not_mem_H,
    h.A1.D_eq, h.A1.Q_le_H, h.A1.D_le_H, h.A1.Q_normal_in_H, h.A1.Q_disjoint_D,
    h.A1.Q_sup_D, h.A1.Q_even, h.A1.D_odd⟩, h.A2, h.A3⟩

/-- The repository's Hypothesis (A) implies the challenge's. -/
private theorem ofRepo {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t : G} (h : PFchapter1section1.HypothesisA G Ω H D Q t) :
    HypothesisA G Ω H D Q t :=
  ⟨⟨h.A1.two_transitive, h.A1.point_stabilizer, h.A1.involution_t, h.A1.t_not_mem_H,
    h.A1.D_eq, h.A1.Q_le_H, h.A1.D_le_H, h.A1.Q_normal_in_H, h.A1.Q_disjoint_D,
    h.A1.Q_sup_D, h.A1.Q_even, h.A1.D_odd⟩, h.A2, h.A3⟩

public theorem hypothesisA_stronglyEmbedded {G : Type u} {Ω : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    {H D Q : Subgroup G} {t : G} (hA : HypothesisA G Ω H D Q t) :
    IsStronglyEmbedded H :=
  Converse.hypothesisA_stronglyEmbedded (toRepo hA)

public theorem psl2_hypothesisA (k : ℕ) (hk : 2 ≤ k) :
    ∃ (_ : Finite (PSL2Model k)) (Ω : Type) (_ : Finite Ω)
      (act : MulAction (PSL2Model k) Ω)
      (H D Q : Subgroup (PSL2Model k)) (t : PSL2Model k),
      @HypothesisA (PSL2Model k) Ω _ _ act _ H D Q t :=
  ⟨inferInstance, P1 (PFAppendixIII.BinaryGaloisField k), inferInstance, inferInstance,
    _, _, _, _, ofRepo (Converse.hypothesisA_PSL2_binary k hk)⟩

public theorem suzuki_hypothesisA (m : ℕ) (hm : 0 < m) :
    ∃ (_ : Finite (SzModel m)) (Ω : Type) (_ : Finite Ω) (act : MulAction (SzModel m) Ω)
      (H D Q : Subgroup (SzModel m)) (t : SzModel m),
      @HypothesisA (SzModel m) Ω _ _ act _ H D Q t := by
  haveI : NeZero m := ⟨by omega⟩
  haveI hfin : Finite (SzModel m) := inferInstanceAs (Finite (SuzukiMatrixGroup m))
  letI actI : MulAction (SzModel m) (SzOmega m) :=
    inferInstanceAs (MulAction (SuzukiMatrixGroup m) (SzOmega m))
  exact ⟨hfin, SzOmega m, inferInstance, actI, _, _, _, _,
    ofRepo (Converse.hypothesisA_Sz m)⟩

public theorem psu3_hypothesisA (k : ℕ) (hk : 2 ≤ k) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
      J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
      Nat.card E = (2 ^ k) ^ 2 ∧
      Nat.card {z : E // J.conj z = z} = 2 ^ k ∧
      ∃ (_ : Finite (PSUModel J)) (Ω : Type) (_ : Finite Ω)
        (act : MulAction (PSUModel J) Ω)
        (H D Q : Subgroup (PSUModel J)) (t : PSUModel J),
        @HypothesisA (PSUModel J) Ω _ _ act _ H D Q t := by
  haveI : NeZero k := ⟨by omega⟩
  obtain ⟨actR, H, D, Q, t, hA⟩ := Converse.hypothesisA_PSU3 k hk
  refine ⟨UField k, inferInstance, inferInstance,
    ⟨(uform k).conj, (uform k).conj_involutive, (uform k).form,
      (uform k).form_hermitian, (uform k).form_nondegenerate⟩,
    rfl, Converse.card_UField k (by omega), Converse.card_fixed_UField k (by omega), ?_⟩
  haveI hfin : Finite (PSUModel (F := UField k)
      ⟨(uform k).conj, (uform k).conj_involutive, (uform k).form,
        (uform k).form_hermitian, (uform k).form_nondegenerate⟩) :=
    inferInstanceAs (Finite (PSU3 k))
  letI actI : MulAction (PSUModel (F := UField k)
      ⟨(uform k).conj, (uform k).conj_involutive, (uform k).form,
        (uform k).form_hermitian, (uform k).form_nondegenerate⟩) (UOmega k) := actR
  exact ⟨hfin, UOmega k, inferInstance, actI, H, D, Q, t, ofRepo hA⟩

end

end BSConverse

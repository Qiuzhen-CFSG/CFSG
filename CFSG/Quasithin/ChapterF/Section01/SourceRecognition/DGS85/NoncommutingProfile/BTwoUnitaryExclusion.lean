module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSylowFrattini
public import Theory.SpecificGroups.SU3.SylowFrattini

/-!
# Excluding binary unitary beta quotients

In either genuine unitary model, the first omega of every Sylow two-group
lies in its Frattini subgroup. The elementary central seed would therefore
lift into Phi(Q_alpha) times the adjacent-core intersection, contradicting
the proved (6.5) movement obstruction. The projective and full special
quotients are kept distinct, with the original unitary form and field
involution. These graph-level exclusions cover every positive degree.

Source: DGS, Groups and Graphs (1985), proof of (10.7), pp.158--159;
Hermitian root squares are proved in Theory.SpecificGroups.SU3.SylowFrattini.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- An actual projective-unitary beta quotient contradicts central-seed movement. -/
theorem BTwoCenterActionData.not_projective_unitary_beta
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J) : False := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  exact c.not_beta_sylow_omega_le_frattini h hB hSyl hb hactor hcentral ht hne hcomm hnot e
    (HermitianForm.SylowFrattini.projective_omega_le_frattini J hn hcard hconj)

/-- The full special-unitary beta quotient is excluded without removing its scalar center. -/
theorem BTwoCenterActionData.not_special_unitary_beta
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* J.specialSubgroup) : False := by
  exact c.not_beta_sylow_omega_le_frattini h hB hSyl hb hactor hcentral ht hne hcomm hnot e
    (HermitianForm.SylowFrattini.special_omega_le_frattini J hn hcard hconj)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

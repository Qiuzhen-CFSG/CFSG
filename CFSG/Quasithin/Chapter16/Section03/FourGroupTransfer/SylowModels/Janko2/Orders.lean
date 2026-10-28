module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.ModelFacts
public import CFSG.Quasithin.Chapter16.Section03.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.SpecificGroups.PSL3.BinaryComparison
public import Theory.Alternating.Aut

/-!
# The two J₂ Sylow-order comparisons in 16.3.4

The concrete J₂ carrier has two-part 128. The full automorphism groups of
A₅ and PSL₃(2) have orders 120 and 336, hence two-parts eight and sixteen.
Actual equivalences transport these computations to the supplied subgroups;
in the linear case field transport retains the full projective matrix group.

Source: Aschbacher–Smith, proof of 16.3.4, printed p.1178 / PDF p.1195.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
open Subgroup ClassificationModels
variable {G : Type*} [Group G] [Finite G] {L K : Subgroup G}

/-- The order of every actual Sylow subgroup of the supplied full J₂ model. -/
theorem j2_sylow_card (eK : K ≃* SporadicName.j2.Carrier) (S : Sylow 2 K) :
    Nat.card S = 128 := by
  have hc : Nat.card K = 604800 := (Nat.card_congr eK.toEquiv).trans
    Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier
  rw [S.card_eq_multiplicity, hc]
  decide +kernel

omit [Finite G] in
/-- The alternating component has a full automorphism group of order 120. -/
theorem j2_a5_aut_card (eL : L ≃* alternatingGroup (Fin 5)) :
    Nat.card (MulAut L) = 120 := by
  let e := Equiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  rw [Nat.card_congr (MulAut.congr eL).toEquiv, ← Nat.card_congr e]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

omit [Finite G] in
/-- Field-independent `IsPSL` gives an equivalence with the exact binary model. -/
theorem j2_l3Two_equiv (hL : ClassicalGroup.IsPSL L 3 2) :
    Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  exact ⟨(e.trans (Matrix.PSL3.binaryEquivPsl2Seven F hF)).trans
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two⟩

omit [Finite G] in
/-- The linear component has its full automorphism group, of order 336. -/
theorem j2_l3Two_aut_card (hL : ClassicalGroup.IsPSL L 3 2) :
    Nat.card (MulAut L) = 336 := by
  obtain ⟨e⟩ := j2_l3Two_equiv hL
  exact (Nat.card_congr (MulAut.congr e).toEquiv).trans
    Matrix.PSL3Two.Automorphisms.card_aut

/-- The strict inequality in the A₅ component alternative. -/
theorem j2_a5_sylowOrderGap (eK : K ≃* SporadicName.j2.Carrier)
    (eL : L ≃* alternatingGroup (Fin 5)) : SylowOrderGap L K := by
  intro A S
  rw [j2_sylow_card eK S, A.card_eq_multiplicity, j2_a5_aut_card eL]
  decide +kernel

/-- The strict inequality in the PSL₃(2) component alternative. -/
theorem j2_l3Two_sylowOrderGap (eK : K ≃* SporadicName.j2.Carrier)
    (hL : ClassicalGroup.IsPSL L 3 2) : SylowOrderGap L K := by
  intro A S
  rw [j2_sylow_card eK S, A.card_eq_multiplicity, j2_l3Two_aut_card hL]
  decide +kernel

/-- Both source component alternatives satisfy the required order comparison. -/
theorem j2_sylowOrderGap (eK : K ≃* SporadicName.j2.Carrier)
    (hL : Nonempty (L ≃* alternatingGroup (Fin 5)) ∨ ClassicalGroup.IsPSL L 3 2) :
    SylowOrderGap L K := by
  rcases hL with hL | hL
  · obtain ⟨eL⟩ := hL
    exact j2_a5_sylowOrderGap eK eL
  · exact j2_l3Two_sylowOrderGap eK hL

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels

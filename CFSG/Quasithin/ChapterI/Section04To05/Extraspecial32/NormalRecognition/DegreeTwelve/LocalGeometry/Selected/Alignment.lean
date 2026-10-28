module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Selected.Involution
public import Theory.GroupTheory.SymmetricThreeQuotientInverter

/-!+# Aligning an outside involution with the chosen cubic Sylow subgroup

Every involution in H outside Q inverts a subgroup of order three: in the
quotient H/Q ≅ S₃, multiply its image by a distinct conjugate transposition,
then extract an order-three element from the lifted dihedral subgroup.
Since |H| = 192, the inverted subgroup is Sylow. Conjugating it onto the
original h.X arranges the supplied involution without changing that choice.
This argument needs neither relative quaternion normality nor ambient fusion.

For the selected configuration, the fusion eight supplies an outside
involution in Qᵍ ∩ H which is fused to z. The existing transport theorem
applies the same conjugation to this involution and to g, retaining every
marking in InverterData. Its geometric premises remain with the selected
fusion assembly owner.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), 31–47, Lemmas 2.2–2.4 and 2.7(3).
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.Selected
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Every outside involution can be conjugated inside H to invert the
original chosen Sylow three-subgroup. In particular this applies to every
outside involution fused to z in the normal-quaternion branch. -/
public theorem outside_involution_alignment (h : Hypotheses z)
    (u : G) (hu : orderOf u = 2) (huH : u ∈ Centralizer z)
    (huQ : u ∉ coreInG z) :
    ∃ a : Centralizer z, ∀ x : h.X,
      ((a : G) * u * (a : G)⁻¹) * ((x : Centralizer z) : G) *
        ((a : G) * u * (a : G)⁻¹)⁻¹ = ((x : Centralizer z) : G)⁻¹ := by
  let uH : Centralizer z := ⟨u, huH⟩
  have huH2 : orderOf uH = 2 := (Subgroup.orderOf_coe uH).symm.trans hu
  have htwo : IsPGroup 2 (Core z) := IsPGroup.of_card (n := 5) h.core_card
  obtain ⟨R, hR, hinv⟩ := exists_inverted_three_of_symmetric_three_quotient
    (Core z) htwo h.quotient_model uH huH2
      (fun hm => huQ (mem_map_of_mem (Centralizer z).subtype hm))
  have hRp : IsPGroup 3 R := IsPGroup.of_card (n := 1) (by simpa using hR)
  obtain ⟨S, hRS⟩ := hRp.exists_le_sylow
  have hS : Nat.card S = 3 := by
    rw [S.card_eq_multiplicity, h.centralizer_card]
    decide +kernel
  have hRS' : R = (S : Subgroup (Centralizer z)) :=
    eq_of_le_of_card_ge hRS (by rw [hR, hS])
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (Centralizer z) S h.X
  have hmap : R.map (MulAut.conj a).toMonoidHom = (h.X : Subgroup (Centralizer z)) := by
    rw [hRS']
    exact congrArg Sylow.toSubgroup ha
  refine ⟨a, ?_⟩
  intro x
  obtain ⟨y, hy, he⟩ := (show (x : Centralizer z) ∈ R.map (MulAut.conj a).toMonoidHom by
    rw [hmap]
    exact x.property)
  have hi := congrArg (MulAut.conj a) (hinv y hy)
  simp only [map_mul, map_inv] at hi
  change (MulAut.conj a) y = (x : Centralizer z) at he
  rw [he] at hi
  exact congrArg (fun v : Centralizer z => (v : G)) hi

/-- Discharge the alignment premise of the selected-core transport, giving
the actual marked fused inverter for the conjugator a*g. -/
public theorem arrange_inverter (h : Hypotheses z) (d : FusionEightData z)
    (g : G) (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hne : coreIntersection z g ≠ fusionCore z) :
    ∃ a : Centralizer z, Nonempty (InverterData h ((a : G) * g)) :=
  arrange_inverter_of_outside_alignment h d
    (fun u hu huH huQ _ => outside_involution_alignment h u hu huH huQ)
    g hgQ hg hne

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.Selected

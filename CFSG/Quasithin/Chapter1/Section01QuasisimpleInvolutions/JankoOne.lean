module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Common
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import Theory.SpecificGroups.Janko1.Model.InvolutionCentralizer.Identification
public import Theory.SpecificGroups.Janko1.Model.Certification
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Excluding J₁ from the quasisimple involution classification

The marked quotient action is an involution with a characteristic-two fixed
group. The proved J₁ automorphism theorem makes it inner; faithfulness of
conjugation and the actual involution fusion transport its fixed group to
the certified C₂ × A₅ centralizer. Projecting through the central C₂ kernel
would make A₅ characteristic two, contradicting its trivial two-core.

All action transports use the original automorphism. No model order,
simplicity, fusion, or centralizer premise remains in the source application.
The imported certificates retain their original ATLAS provenance.
Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.503.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions

private theorem a5_not_characteristic_two :
    ¬ HasCharacteristicTwo (alternatingGroup (Fin 5)) := by
  let A := alternatingGroup (Fin 5)
  let : Group.IsPerfect A := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hc : pCore 2 A = ⊥ := by
    rcases (inferInstance : (pCore 2 A).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hp : IsPGroup 2 A :=
        (show IsPGroup 2 (⊤ : Subgroup A) from h ▸ pCore_isPGroup).of_equiv topEquiv
      let : Group.IsNilpotent A := hp.isNilpotent
      exact (Group.IsPerfect.not_isSolvable A inferInstance).elim
  intro h
  change centralizer (pCore 2 A : Set A) ≤ pCore 2 A at h
  rw [hc] at h
  have ht : (⊤ : Subgroup A) = ⊥ := le_antisymm (by
    intro x _
    apply h
    intro y hy
    have hy1 : y = 1 := hy
    simp [hy1]) bot_le
  exact top_ne_bot ht

private theorem product_not_characteristic_two :
    ¬ HasCharacteristicTwo Janko1.InvolutionCentralizer.ProductModel := by
  intro h
  apply a5_not_characteristic_two
  let f : Janko1.InvolutionCentralizer.ProductModel →* alternatingGroup (Fin 5) :=
    MonoidHom.snd _ _
  apply MonoidHom.centralizer_pCore_le_of_surjective_centralKernel f
    (fun x => ⟨(1, x), rfl⟩) _ h
  intro x hx
  have hx2 : x.2 = 1 := hx
  rw [mem_center_iff]
  intro y
  apply Prod.ext
  · exact mul_comm _ _
  · change y.2 * x.2 = x.2 * y.2
    rw [hx2, mul_one, one_mul]

/-- The full fixed group of an involution on the actual J₁ quotient is
C₂ × A₅ up to the genuine conjugacy transport, contradicting characteristic two. -/
theorem MarkedInvolution.not_janko_one {L : Type*} [Group L] [Finite L]
    [IsQuasisimple L] {α : MulAut L} {P : Sylow 2 L}
    (d : MarkedInvolution α P) (e : L ⧸ center L ≃* Janko1.Model) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  let : Group.IsPerfect Janko1.Model := Group.IsPerfect.ofSurjective
    (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨horder, hchar, _⟩ := d.centralQuotient_model_inputs e
  obtain ⟨z, hz⟩ := Janko1.OuterCertificate.aut_inner (MulAut.centralQuotientAction e α)
  have hzo : orderOf z = 2 := by
    rw [← MulAut.conj_orderOf_of_center_eq_bot
      (Subgroup.center_eq_bot_of_simple_perfect (G := Janko1.Model)), hz]
    exact horder
  obtain ⟨g, hg⟩ := Janko1.involution_fusion z hzo
  have he : MulAut.congr (MulAut.conj g) (MulAut.conj z) = MulAut.conj Janko1.a := by
    rw [MulAut.congr_conj]
    change MulAut.conj (g * z * g⁻¹) = _
    rw [hg]
  rw [← hz] at hchar
  have ht := hchar.of_equiv (MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj z))
  rw [he, MulAut.fixedSubgroup_conj] at ht
  exact product_not_characteristic_two
    (ht.of_equiv Janko1.InvolutionCentralizer.productEquiv)

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions

module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.SourceBounds
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# The middle contribution in the literal H/U_H quotient

A binary conjugation section with kernel U_H represents V_H/U_H. Mutual
normalization puts [Uγ,V_H] in Uγ∩V_H, and V_H≤O₂(H) puts it in Dγ.
Its coordinate displacement therefore lies in the image of Dγ∩V_H. The
first isomorphism theorem identifies that image's dimension with the rank
of the displayed canonical image in H/U_H, even though Dγ∩V_H need not
contain U_H. This removes all quotient-transport premises from the middle
estimate. The lower displacement bound for a faithful G₂ action remains a
separate representation-theoretic input.

Source: Aschbacher–Smith, 13.8.27, final paragraph, printed p.963.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry

variable {G W X : Type*} [Group G]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  {L T H V V₃ V₁ : Subgroup G}
  [((Source.UH H V₃).subgroupOf H).Normal]
  {ρ : Representation (ZMod 2) (Source.Hstar H) W}

/-- Displacement on V_H/U_H is bounded by the literal middle filtration
image. Only actual conjugation and the original quotient kernels are used. -/
theorem source_middle_displacement_le
    (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hfaith : Function.Injective ρ) (hUg : c.Ugamma V₃ ≤ H)
    (hreverse : Source.VH H V ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hVQ : Source.VH H V ≤ Source.QH H)
    (σ : Representation (ZMod 2) (Source.Hstar H) X)
    (t : BinaryConjugationSection H (Source.VH H V) (Source.UH H V₃)
      (σ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ (Source.starImage H (c.Ugamma V₃))) ≤
      rank (((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓ Source.VH H V).subgroupOf H).map
        (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf H))) := by
  let B := Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓ Source.VH H V
  have hnUg : Source.VH H V ≤ normalizer (c.Ugamma V₃ : Set G) := by
    have hm := map_mono (f := (MulAut.conj (c.gb : G)).toMonoidHom) s.normalizes
    rw [map_equiv_normalizer_eq] at hm
    exact hreverse.trans hm
  have hcommV : ⁅c.Ugamma V₃, Source.VH H V⁆ ≤ Source.VH H V :=
    le_normalizer_iff_commutator_le_right.mp (hUg.trans t.normalized)
  have hcomm : ⁅c.Ugamma V₃, Source.VH H V⁆ ≤ B := by
    dsimp only [B]
    rw [s.Dgamma_eq_inf_core _ hUg hfaith]
    exact le_inf (le_inf (le_normalizer_iff_commutator_le_left.mp hnUg)
      (hcommV.trans hVQ)) hcommV
  have htop : t.imageSpace (Source.VH H V) = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨u, hu⟩ := t.onto (Multiplicative.ofAdd v)
    exact (t.mem_imageSpace_iff _ _).mpr ⟨u, u.property, congrArg Multiplicative.toAdd hu⟩
  have hcomp : subspaceCommutator (σ.comp (QuotientGroup.mk' (pCore 2 H))) ⊤
      ((c.Ugamma V₃).subgroupOf H) =
      subspaceCommutator σ ⊤ (Source.starImage H (c.Ugamma V₃)) := by
    simpa only [Submodule.map_id, Source.starImage] using subspaceCommutator_map_embedding
      (σ.comp (QuotientGroup.mk' (pCore 2 H))) σ (QuotientGroup.mk' (pCore 2 H))
      (LinearMap.id (R := ZMod 2) (M := X)) (fun _ _ => rfl)
      ((c.Ugamma V₃).subgroupOf H) ⊤
  have hle : subspaceCommutator σ ⊤ (Source.starImage H (c.Ugamma V₃)) ≤ t.imageSpace B := by
    rw [← hcomp, ← htop, ← t.imageSpace_commutator _ _ hUg le_rfl]
    exact t.imageSpace_mono hcomm
  have hcard : Nat.card ((B.subgroupOf H).map
      (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf H))) =
      Nat.card (t.imageSpace B) := by
    rw [t.imageSpace_card_eq_relIndex B inf_le_right, ← relIndex_ker,
      QuotientGroup.ker_mk', relIndex_subgroupOf (inf_le_right.trans t.section_le)]
  have hdim : rank ((B.subgroupOf H).map
      (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf H))) =
      Module.finrank (ZMod 2) (t.imageSpace B) := by
    rw [rank, hcard, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      Nat.log_pow (by decide : 1 < 2)]
  rw [hdim]
  exact Submodule.finrank_mono hle

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
end

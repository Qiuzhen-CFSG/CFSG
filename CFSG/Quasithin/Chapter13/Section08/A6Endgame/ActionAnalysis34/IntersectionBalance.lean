module

public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.IntersectionBalance.SourceCalculation

/-!
# The subgroup and dimension deductions in Lemma 13.8.34

The fixed-space preimage U₁ and the image of the actual commutator are in
UH/V₁. Equality of those images lifts U₁V₃ into UαV₁ using the relative
normalization from F.9.13. A quotient of dimension two and the line V₁ give
codimension at most three. The specified element of H carries this bound
from α to γ; the critical-pair conjugator identifies the dimensions of UH
and Uγ. The kernel identity then gives the source rank sum on Uγ, and
mutual normalization bounds the displacement on the literal VH/UH by Dγ/I.

The final theorem discharges both module calculations using the compatible
marked natural/augmentation model and the literal noncentral source syntheme
quotient. It retains the earlier local normalization, kernel, conjugator and
model-identification inputs; none of its intersection or displacement bounds
is assumed. The parent owns the final rank-one contradiction and Lemma 13.8.34
and is not imported here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 13.8.34, second paragraph, printed p.968
(PDF p.985), and F.9.13.
-/

public section
open Subgroup Module Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.IntersectionBalance
variable {G : Type*} [Group G] [Finite G]

/-- Lift the actual displacement, then transfer the intersection bound through
both source conjugators. The module calculation remains an explicit premise. -/
theorem source_intersection_codimensions (H V₃ V₁ Uα Uγ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 Uγ]
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (hline : V₁ ≤ Source.UH H V₃) (hcard : Nat.card V₁ = 2)
    (hnline : Uα ≤ normalizer (V₁ : Set G))
    (hn : Source.UH H V₃ ≤ normalizer (Uα : Set G))
    (h : H) (hα : Uγ.map (MulAut.conj (h : G)).toMonoidHom = Uα)
    (g : G) (hγ : (Source.UH H V₃).map (MulAut.conj g).toMonoidHom = Uγ)
    (hdisp : quotientSpace (Source.UH H V₃) V₁
        (Uone H (Source.UH H V₃) V₁ a ⊔ V₃) =
      quotientSpace (Source.UH H V₃) V₁ ⁅Source.UH H V₃, Uα⁆)
    (hdim : finrank (ZMod 2) (Additive (Source.UH H V₃) ⧸
      inside (Source.UH H V₃) (Uone H (Source.UH H V₃) V₁ a ⊔ V₃)) = 2) :
    Uone H (Source.UH H V₃) V₁ a ⊔ V₃ ≤ Uα ⊔ V₁ ∧
    finrank (ZMod 2) (Additive (Source.UH H V₃) ⧸
      inside (Source.UH H V₃) (Source.UH H V₃ ⊓ Uα)) ≤ 3 ∧
    finrank (ZMod 2) (Additive (Source.UH H V₃) ⧸
      inside (Source.UH H V₃) (Source.UH H V₃ ⊓ Uγ)) ≤ 3 ∧
    finrank (ZMod 2) (Additive Uγ ⧸ Ispace (Source.UH H V₃) Uγ) ≤ 3 := by
  have hK : Uone H (Source.UH H V₃) V₁ a ⊔ V₃ ≤ Source.UH H V₃ :=
    sup_le (Uone_le H _ V₁ a) (le_conjugateSpanBy V₃ H)
  have hlift := lift_displacement (Source.UH H V₃) Uα V₁ _ hK hn hdisp
  have hcodim := intersection_codimension_le_three (Source.UH H V₃) Uα V₁ _
    hline hK hnline hlift hcard hdim
  have hcodimγ : finrank (ZMod 2) (Additive (Source.UH H V₃) ⧸
      inside (Source.UH H V₃) (Source.UH H V₃ ⊓ Uγ)) ≤ 3 := by
    rw [alpha_gamma_intersection_codimension H V₃ Uα Uγ h hα]
    exact hcodim
  refine ⟨hlift, hcodim, hcodimγ, ?_⟩
  rw [gamma_codimension_eq (Source.UH H V₃) Uγ g hγ]
  exact hcodimγ

/-- All dimension inputs used by the parent's rank-one contradiction, on
U = Additive Uγ, D = Dγ and I = Uγ ∩ UH. This intermediate lifting lemma
exposes the two module inputs, which
`source_intersection_and_dimension_balance` below discharges. -/
theorem source_dimension_inputs (H V V₃ V₁ Uα Uγ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 Uγ]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (hline : V₁ ≤ Source.UH H V₃) (hcard : Nat.card V₁ = 2)
    (hnline : Uα ≤ normalizer (V₁ : Set G))
    (hn : Source.UH H V₃ ≤ normalizer (Uα : Set G))
    (h : H) (hα : Uγ.map (MulAut.conj (h : G)).toMonoidHom = Uα)
    (g : G) (hγ : (Source.UH H V₃).map (MulAut.conj g).toMonoidHom = Uγ)
    (hγH : Uγ ≤ H) (hnγ : Source.VH H V ≤ normalizer (Uγ : Set G))
    (hVQ : Source.VH H V ≤ Source.QH H)
    (hkernel : Source.Dgamma Uγ (Source.UH H V₃) V₁ = Uγ ⊓ Source.QH H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hρ : SectionConjugation H V V₃ ρ)
    (hdisp : 1 < rank (Source.starImage H Uγ) →
      quotientSpace (Source.UH H V₃) V₁ (Uone H (Source.UH H V₃) V₁ a ⊔ V₃) =
      quotientSpace (Source.UH H V₃) V₁ ⁅Source.UH H V₃, Uα⁆)
    (hdim : finrank (ZMod 2) (Additive (Source.UH H V₃) ⧸
      inside (Source.UH H V₃) (Uone H (Source.UH H V₃) V₁ a ⊔ V₃)) = 2) :
    Ispace (Source.UH H V₃) Uγ ≤ Dspace (Source.UH H V₃) Uγ V₁ ∧
    finrank (ZMod 2) (Dspace (Source.UH H V₃) Uγ V₁) + rank (Source.starImage H Uγ) =
      finrank (ZMod 2) (Additive Uγ) ∧
    (1 < rank (Source.starImage H Uγ) →
      finrank (ZMod 2) (Additive Uγ ⧸ Ispace (Source.UH H V₃) Uγ) ≤ 3) ∧
    finrank (ZMod 2) (subspaceCommutator ρ ⊤ (Source.starImage H Uγ)) ≤
      finrank (ZMod 2) (Dspace (Source.UH H V₃) Uγ V₁ ⧸
        (Ispace (Source.UH H V₃) Uγ).comap (Dspace (Source.UH H V₃) Uγ V₁).subtype) := by
  refine ⟨Ispace_le_Dspace _ _ _, dimension_balance H _ Uγ V₁ hγH hkernel, ?_,
    source_displacement_bound H V V₃ Uγ V₁ hγH hnγ hVQ hkernel ρ hρ⟩
  intro hr
  exact (source_intersection_codimensions H V₃ V₁ Uα Uγ a hline hcard hnline hn
    h hα g hγ (hdisp hr) hdim).2.2.2


open Representation.SixLetterRadicalDisplacement
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

/-- The complete subgroup-intersection and dimension-balance deductions of
13.8.34, with the marked finite computations discharged on the actual source
quotient. Earlier local geometry and the compatible natural/cover coordinates
remain explicit; no codimension, displacement or product containment is assumed. -/
theorem source_intersection_and_dimension_balance
    (H M V V₃ V₁ Uα Uγ Vα R₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 Uγ]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* S) (hm : CompatibleModel H V₃ V₁ a e)
    (hline : V₁ ≤ Source.UH H V₃) (hcard : Nat.card V₁ = 2)
    (hmark : (Source.starImage H (H ⊓ M)).map e.toMonoidHom = H2)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hnorm : H ⊓ M ≤ normalizer (V : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hρ : SectionConjugation H V V₃ ρ)
    (hq : IsQuadratic ρ (Source.starImage H Vα))
    (hUV : Source.starImage H Uα ≤ Source.starImage H Vα)
    (hVR : Source.starImage H Vα ≤ Source.starImage H R₁)
    (hR : (Source.starImage H R₁).map e.toMonoidHom = D)
    (hnline : Uα ≤ normalizer (V₁ : Set G))
    (hn : Source.UH H V₃ ≤ normalizer (Uα : Set G))
    (h : H) (hα : Uγ.map (MulAut.conj (h : G)).toMonoidHom = Uα)
    (g : G) (hγ : (Source.UH H V₃).map (MulAut.conj g).toMonoidHom = Uγ)
    (hγH : Uγ ≤ H) (hnγ : Source.VH H V ≤ normalizer (Uγ : Set G))
    (hVQ : Source.VH H V ≤ Source.QH H)
    (hkernel : Source.Dgamma Uγ (Source.UH H V₃) V₁ = Uγ ⊓ Source.QH H) :
    (∀ b, (∀ v ∈ quotientSpace (Source.UH H V₃) V₁ (Uone H _ V₁ a ⊔ V₃),
      tildeRepresentation H _ V₁ a b v = v) ↔ b ∈ Source.starImage H R₁) ∧
    finrank (ZMod 2) (Additive (Source.UH H V₃) ⧸
      inside (Source.UH H V₃) (Uone H _ V₁ a ⊔ V₃)) = 2 ∧
    Ispace (Source.UH H V₃) Uγ ≤ Dspace (Source.UH H V₃) Uγ V₁ ∧
    finrank (ZMod 2) (Dspace (Source.UH H V₃) Uγ V₁) + rank (Source.starImage H Uγ) =
      finrank (ZMod 2) (Additive Uγ) ∧
    finrank (ZMod 2) (Additive Uγ) = finrank (ZMod 2) (Additive (Source.UH H V₃)) ∧
    finrank (ZMod 2) (subspaceCommutator ρ ⊤ (Source.starImage H Uγ)) ≤
      finrank (ZMod 2) (Dspace (Source.UH H V₃) Uγ V₁ ⧸
        (Ispace (Source.UH H V₃) Uγ).comap (Dspace (Source.UH H V₃) Uγ V₁).subtype) ∧
    (1 < rank (Source.starImage H Uγ) →
      rank (Source.starImage H Uα) = 2 ∧
      Uone H (Source.UH H V₃) V₁ a ⊔ V₃ ≤ Uα ⊔ V₁ ∧
      finrank (ZMod 2) (Additive (Source.UH H V₃) ⧸
        inside (Source.UH H V₃) (Source.UH H V₃ ⊓ Uα)) ≤ 3 ∧
      finrank (ZMod 2) (Additive (Source.UH H V₃) ⧸
        inside (Source.UH H V₃) (Source.UH H V₃ ⊓ Uγ)) ≤ 3 ∧
      finrank (ZMod 2) (Additive Uγ ⧸ Ispace (Source.UH H V₃) Uγ) ≤ 3 ∧
      finrank (ZMod 2) (Dspace (Source.UH H V₃) Uγ V₁ ⧸
        (Ispace (Source.UH H V₃) Uγ).comap (Dspace (Source.UH H V₃) Uγ V₁).subtype) ≤ 1) := by
  obtain ⟨hfix, hdim, hcalc⟩ := source_model_calculation H M V V₃ V₁ Uα Uγ Vα R₁
    a e hm hline hmark hflag hindex hnc hnorm ρ hρ hq hUV hVR hR hγH h hα
  have hID := Ispace_le_Dspace (Source.UH H V₃) Uγ V₁
  have hbalance := dimension_balance H (Source.UH H V₃) Uγ V₁ hγH hkernel
  refine ⟨hfix, hdim, hID, hbalance, (dimension_conjugate _ _ g hγ).symm,
    source_displacement_bound H V V₃ Uγ V₁ hγH hnγ hVQ hkernel ρ hρ, ?_⟩
  intro hr
  obtain ⟨hrank, hdisp⟩ := hcalc hr
  obtain ⟨hlift, hαdim, hγdim, hIdim⟩ := source_intersection_codimensions
    H V₃ V₁ Uα Uγ a hline hcard hnline hn h hα g hγ hdisp hdim
  refine ⟨hrank, hlift, hαdim, hγdim, hIdim, ?_⟩
  have hI := (Ispace (Source.UH H V₃) Uγ).finrank_quotient_add_finrank
  have hD := ((Ispace (Source.UH H V₃) Uγ).comap
    (Dspace (Source.UH H V₃) Uγ V₁).subtype).finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe hID).finrank_eq] at hD
  omega

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.IntersectionBalance

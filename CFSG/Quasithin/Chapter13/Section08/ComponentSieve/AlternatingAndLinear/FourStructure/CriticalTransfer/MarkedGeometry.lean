module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.Lifting
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.HeadPlane
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.RadicalPlacement
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary

/-!
# Forward critical-pair consequences of the marked radical

The natural and dual plane calculations give the commutator equality at α;
the specified source conjugator transports it to γ. The intersection
centralizer excludes I ≤ D_H. Relative invariance lifts from the section,
so the universal earlier result 13.8.18(1) now applies to I. Its generation
conclusion supplies the final premise of 13.8.9(1), and the lifted commutator
comparison yields V₁ ≰ Uγ as in 13.8.9(2).

`forward_noncontainment_of_source` constructs the marked plane from the
actual image of V₃ in the specified natural head, and discharges radical
placement with the same actor equivalence and source conjugator h. The
endpoint subgroups Uγ, A₁ and Gγ are the actual conjugates by the displayed
edge transporter g. Their relative normalization is derived, not assumed.
The nonsplitting exclusion, A₁ ≰ I, noncyclicity of Uγ*, and the universal
earlier chapter implications remain explicit inputs to this independent
conditional result. The full 13.8.25 assembly discharges these inputs.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.961–962 (PDF pp.978–979).
-/

@[expose] public section

open Representation Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  {H : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

namespace MarkedGeometry
open Representation.BinaryOffender

/-- The forward half of 13.8.25 after constructing the marked radical.
The two universal earlier implications are precisely the generation clause
13.8.18(1) (with its source setup discharged) and 13.8.9(1). Neither generation
for I nor either commutator equality is assumed. The marked radical is still
an explicit premise; its source construction is a separate obligation. -/
theorem forward_noncontainment_of_marked_radical
    [Finite G] [FiniteDimensional (ZMod 2) U]
    (V₃ V₁ : Subgroup G)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (I J E Ug Vg A₁ : Subgroup G)
    (hZI : V₁ ≤ I) (hIU : I ≤ Source.UH H V₃)
    (N : Subrepresentation ρ) (hN : s.image I = N.toSubmodule)
    (eH : Source.Hstar H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (hNat : ChiefFactors.IsNaturalOrDual N.toRepresentation eH)
    (hUgVg : Ug ≤ Vg) (hVgH : Vg ≤ H) (hUJ : Source.UH H V₃ ≤ J)
    (hUA : Source.UH H V₃ ≤ normalizer (A₁ : Set G))
    (hnormUg : Source.UH H V₃ ≤ normalizer (Ug : Set G))
    (hcentralizer : ⁅J ⊓ centralizer (Ug : Set G), Vg⁆ ≤ A₁)
    (hA : Nat.card A₁ = 2) (hnot : ¬ A₁ ≤ I)
    (hrank : 1 < rank (Source.starImage H Ug))
    (hcenters : ∀ B ≤ Source.starImage H Vg, 1 < rank B →
      ¬ HasCommonCenter N.toRepresentation B)
    (h : H) (P : Submodule (ZMod 2) ChiefFactors.NaturalSpace)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hrad : (Source.starImage H (Vg.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom)).map
      eH.toMonoidHom ≤ BinaryLinear.radical P)
    (generation18 : ∀ F ≤ Source.UH H V₃,
      ¬ F ≤ Source.DH (Source.UH H V₃) Ug A₁ → J = conjugateSpanBy F J ⊔ E)
    (noncentral9 : ∀ F ≤ Source.UH H V₃, Vg ≤ normalizer (F : Set G) →
      J = conjugateSpanBy F J ⊔ E → ¬ ⁅F, Vg⁆ ≤ Ug) :
    commSpace N.toRepresentation
        (Source.starImage H (Ug.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom)) =
      commSpace N.toRepresentation
        (Source.starImage H (Vg.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom)) ∧
    commSpace N.toRepresentation (Source.starImage H Ug) =
      commSpace N.toRepresentation (Source.starImage H Vg) ∧
    ¬ I ≤ Source.DH (Source.UH H V₃) Ug A₁ ∧
    Vg ≤ normalizer (I : Set G) ∧
    J = conjugateSpanBy I J ⊔ E ∧ ¬ V₁ ≤ Ug := by
  have hAB : Source.starImage H Ug ≤ Source.starImage H Vg :=
    Subgroup.map_mono (show Ug.subgroupOf H ≤ Vg.subgroupOf H from fun a ha => hUgVg ha)
  have hdim := commSpace_rank_gt_one_of_no_common_center N.toRepresentation eH hNat
    (Source.starImage H Ug) hrank (hcenters _ hAB hrank)
  have hrad' : ((Source.starImage H Vg).map
      (MulAut.conj (QuotientGroup.mk' (pCore 2 H) h⁻¹)).toMonoidHom).map
        eH.toMonoidHom ≤ BinaryLinear.radical P := by
    rw [← starImage_conjugate Vg hVgH h⁻¹]
    exact hrad
  obtain ⟨hα, hγ⟩ := commSpaces_of_conjugate_radical N.toRepresentation eH hNat hAB
    P hP (QuotientGroup.mk' (pCore 2 H) h⁻¹) hrad' hdim
  have hα' : commSpace N.toRepresentation
        (Source.starImage H (Ug.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom)) =
      commSpace N.toRepresentation
        (Source.starImage H (Vg.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom)) := by
    change commSpace N.toRepresentation
      (Source.starImage H (Ug.map (MulAut.conj ((h⁻¹ : H) : G)).toMonoidHom)) =
      commSpace N.toRepresentation
      (Source.starImage H (Vg.map (MulAut.conj ((h⁻¹ : H) : G)).toMonoidHom))
    rw [starImage_conjugate Ug (hUgVg.trans hVgH) h⁻¹,
      starImage_conjugate Vg hVgH h⁻¹]
    exact hα
  have hHI : H ≤ normalizer (I : Set G) := by
    apply s.normalizes_of_image_invariant I hZI hIU
    intro a u hu
    rw [hN] at hu ⊢
    exact N.apply_mem_toSubmodule _ hu
  have hVI := hVgH.trans hHI
  have hc := s.critical_intersection_centralizes I J Ug Vg A₁ hZI hIU N hN
    hUgVg hVgH hUJ hUA hcentralizer hA hnot
  have hID := s.not_le_DH_of_commSpace_rank I Ug A₁ N hN hc.1 (by omega)
  have hgen := generation18 I hIU hID
  have hcompare := s.lift_commSpace_comparison I Ug Vg hIU hVgH N hN hγ.symm.le
  have hline := noncentral_commutator_supported_on_line I Ug Vg V₁
    (hIU.trans hnormUg) hcompare (noncentral9 I hIU hVI hgen)
  exact ⟨hα', hγ, hID, hVI, hgen, hline.1⟩

/-- The marked radical and forward implication of 13.8.25 for an actual
source critical pair. The source's right edge transporter is represented
by `g` in left-conjugation notation, while `h` retains the right-conjugation
convention of 13.8.8(2). Both group and head identifications remain fixed.

The seed hypotheses are the earlier action of `(L₁T)*` on Ṽ₃ and the
marked L₀ facts. `generation18` and `noncentral9` are the universal earlier
conclusions 13.8.18(1) and 13.8.9(1), with their source setup discharged.
Generation for I, its Vγ-invariance, both commutator equalities, and radical
containment are conclusions. Properness of W suffices for the plane
construction, so this applies in particular to the source's nonzero maximal
W and any natural-or-dual irreducible inside W. -/
theorem forward_noncontainment_of_source
    [Finite G] [FiniteDimensional (ZMod 2) U]
    (V₃ V₁ : Subgroup G)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (L₀ L₁ T : Subgroup G) (hL : L₀ ≤ L₁) (hPH : L₁ ⊔ T ≤ H)
    (hthree : Nat.card (L₀ ⧸ pCore 2 L₀) = 3) (hfix : ⁅L₀, V₃⁆ ≤ V₁)
    (hT : IsPGroup 2 T)
    (hstable : ∀ a : Source.starImage H (L₁ ⊔ T), ∀ v ∈ s.image V₃,
      ρ a v ∈ s.image V₃)
    (hirr : IsAtom (⟨s.image V₃, hstable⟩ :
      Subrepresentation (ρ.comp (Source.starImage H (L₁ ⊔ T)).subtype)))
    (hdim : Module.finrank (ZMod 2) (s.image V₃) = 2)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (eH : Source.Hstar H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] ChiefFactors.NaturalSpace)
    (he : ∀ a u, e (W.quotientRepresentation a u) = eH a (e u))
    (I : Subgroup G) (hZI : V₁ ≤ I) (hIU : I ≤ Source.UH H V₃)
    (N : Subrepresentation ρ) (hN : s.image I = N.toSubmodule)
    (hNat : ChiefFactors.IsNaturalOrDual N.toRepresentation eH)
    (g : G) (J E Ug Vg A₁ : Subgroup G)
    (hJ : J = H.map (MulAut.conj g).toMonoidHom)
    (hUg : Ug = (Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
    (hA₁ : A₁ = V₁.map (MulAut.conj g).toMonoidHom)
    (hUgVg : Ug ≤ Vg) (hVgH : Vg ≤ H) (hUJ : Source.UH H V₃ ≤ J)
    (hcentralizer : ⁅J ⊓ centralizer (Ug : Set G), Vg⁆ ≤ A₁)
    (hZ : Nat.card V₁ = 2) (hnot : ¬ A₁ ≤ I)
    (hrank : 1 < rank (Source.starImage H Ug))
    (hcenters : ∀ B ≤ Source.starImage H Vg, 1 < rank B →
      ¬ HasCommonCenter N.toRepresentation B)
    (h : H)
    (hplace : Vg.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2)
    (generation18 : ∀ F ≤ Source.UH H V₃,
      ¬ F ≤ Source.DH (Source.UH H V₃) Ug A₁ → J = conjugateSpanBy F J ⊔ E)
    (noncentral9 : ∀ F ≤ Source.UH H V₃, Vg ≤ normalizer (F : Set G) →
      J = conjugateSpanBy F J ⊔ E → ¬ ⁅F, Vg⁆ ≤ Ug) :
    let seed := sourceGeneratingSeed s L₁ T hT hstable hirr hdim
    let P := headPlane ρ seed W e
    Module.finrank (ZMod 2) P = 2 ∧
    (Source.starImage H (L₁ ⊔ T)).map eH.toMonoidHom ≤ BinaryLinear.parabolic P ∧
    (Source.starImage H (Vg.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom)).map
      eH.toMonoidHom ≤ BinaryLinear.radical P ∧
    commSpace N.toRepresentation
        (Source.starImage H (Ug.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom)) =
      commSpace N.toRepresentation
        (Source.starImage H (Vg.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom)) ∧
    commSpace N.toRepresentation (Source.starImage H Ug) =
      commSpace N.toRepresentation (Source.starImage H Vg) ∧
    ⁅I, Vg⁆ ≤ ⁅I, Ug⁆ ⊔ V₁ ∧
    ⁅I ⊓ Source.DH (Source.UH H V₃) Ug A₁, Vg⁆ = ⊥ ∧
    ¬ I ≤ Source.DH (Source.UH H V₃) Ug A₁ ∧
    Vg ≤ normalizer (I : Set G) ∧
    J = conjugateSpanBy I J ⊔ E ∧ ¬ V₁ ≤ Ug := by
  let seed := sourceGeneratingSeed s L₁ T hT hstable hirr hdim
  have hP := headPlane_finrank ρ seed W hW e
  have hrad := source_radical_placement s L₀ L₁ T Vg hL hPH hthree hfix
    hT hstable hirr hdim W hW eH e he h hplace
  have hnormUg : Source.UH H V₃ ≤ normalizer (Ug : Set G) := by
    rw [hUg]
    apply hUJ.trans
    rw [hJ]
    exact (map_mono s.normalizes).trans
      ((Source.UH H V₃).le_normalizer_map (MulAut.conj g).toMonoidHom)
  have hUA : Source.UH H V₃ ≤ normalizer (A₁ : Set G) := by
    rw [hA₁]
    apply hUJ.trans
    rw [hJ]
    exact (s.centralizes_conjugate_line g).trans (centralizer_le_normalizer _)
  have hA : Nat.card A₁ = 2 := by
    rw [hA₁, Subgroup.card_map_of_injective (MulAut.conj g).injective, hZ]
  obtain ⟨hα, hγ, hID, hVI, hgen, hline⟩ :=
    forward_noncontainment_of_marked_radical V₃ V₁ s I J E Ug Vg A₁ hZI hIU N hN
      eH hNat hUgVg hVgH hUJ hUA hnormUg hcentralizer hA hnot hrank hcenters
      h (headPlane ρ seed W e) hP hrad generation18 noncentral9
  exact ⟨hP, headPlane_stable ρ seed W eH e he, hrad, hα, hγ,
    s.lift_commSpace_comparison I Ug Vg hIU hVgH N hN hγ.symm.le,
    (s.critical_intersection_centralizes I J Ug Vg A₁ hZI hIU N hN
      hUgVg hVgH hUJ hUA hcentralizer hA hnot).2.1,
    hID, hVI, hgen, hline⟩

end MarkedGeometry

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer

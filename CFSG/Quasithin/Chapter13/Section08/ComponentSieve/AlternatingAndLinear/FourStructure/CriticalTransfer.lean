module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences

/-!
# Linear bounds from the source critical pair

The actual edge conjugator defines Uγ and A₁. The section-transfer results
prove the critical dimension bound and construct the line of displacements.
They also turn A₁ ≰ U_H into pointwise fixation of D̃_H. Establishing that
noncontainment in the equality case still requires the source reversal
argument; constructing the marked radical and proving the irreducible-section
lower bound remain separate obligations.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed p.962 (PDF p.979), using
F.9.13(6), F.9.16 and Remark F.9.17. In left-conjugation notation the source's
edge transporter g_b is represented here by its inverse.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Representation Representation.BinaryOffender
open Subgroup
open CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
open CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry
open scoped commutatorElement

/-- Construct the bound and the actual displacement line from the source pair.
The subgroup-index inequality is the earlier critical-pair choice. The last
implication is ready for the reversal result; equality alone is not asserted
to imply it here. -/
theorem critical_pair_linear_bounds
    {G U : Type*} [Group G] [Finite G] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}
    (s : ConjugationSection H UH Z ρ) (g : G)
    (hforward : UH.map (MulAut.conj g).toMonoidHom ≤ H)
    (hreverse : UH ≤ H.map (MulAut.conj g).toMonoidHom)
    (hZ : Nat.card Z = 2) (hfaith : Function.Injective ρ)
    (hcritical : Nat.log 2 ((Source.DH UH (UH.map (MulAut.conj g).toMonoidHom)
      (Z.map (MulAut.conj g).toMonoidHom)).relIndex UH) ≤
      Nat.log 2 ((Source.Dgamma (UH.map (MulAut.conj g).toMonoidHom) UH Z).relIndex
        (UH.map (MulAut.conj g).toMonoidHom))) :
    let Ug := UH.map (MulAut.conj g).toMonoidHom
    let A := Z.map (MulAut.conj g).toMonoidHom
    let D := s.image (Source.DH UH Ug A)
    let S := s.image A
    Module.finrank (ZMod 2) (U ⧸ D) ≤ rank (Source.starImage H Ug) ∧
      Module.finrank (ZMod 2) S ≤ 1 ∧
      (∀ a ∈ Source.starImage H Ug, ∀ d ∈ D, ρ a d - d ∈ S) ∧
      (¬ A ≤ UH → D ≤ fixedSpace ρ (Source.starImage H Ug)) := by
  dsimp only
  obtain ⟨hS, hcomm⟩ := s.critical_line_displacement_of_conjugate
    (UH.map (MulAut.conj g).toMonoidHom) g hreverse hZ
  refine ⟨s.critical_bound _ _ hforward hfaith hcritical, hS, hcomm, ?_⟩
  intro hnot
  apply s.critical_fixed_of_line_not_le _ _
    (hreverse.trans ((s.centralizes_conjugate_line g).trans (centralizer_le_normalizer _)))
    _ hnot
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hZ]

/-! The following adapter discharges the irreducible-section lower bound from
the source upper-section geometry.  The upper section, its index-two seed and
the parabolic normalizer are explicit because these are the genuine source
inputs used in the dual orientation; no family tag is treated as a substitute
for them. -/

theorem critical_section_codimension_ge_two_of_source_data
    {G U : Type*} [Group G] [Finite G]
    [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    {L T H V V₃ V₁ : Subgroup G}
    {ρ : Representation (ZMod 2) (Source.Hstar H) U}
    [IsElementaryAbelian 2 (Source.VH H V)]
    (S : SourceData L T H V V₃ V₁ ρ) (c : CriticalPair L T H V)
    (hc : Eligible S c)
    (hcomm : Coinvariants.ker
        (S.N.toRepresentation.comp (Source.starImage H (c.Ugamma V₃)).subtype) =
      Coinvariants.ker
        (S.N.toRepresentation.comp (Source.starImage H c.Vgamma).subtype))
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (τ : Representation (ZMod 2) (Source.Hstar H) E)
    (t : UpperSection H (Source.VH H V) (Source.UH H V₃) τ)
    (X : Subgroup G) (hXV : X ≤ Source.VH H V)
    (hspan : Source.VH H V = conjugateSpanBy X H)
    (hindex : (Source.UH H V₃).relIndex X = 2)
    (hparabolic : ∀ a : H,
      S.eH (QuotientGroup.mk' (pCore 2 H) a) ∈ BinaryLinear.parabolic S.plane →
        (a : G) ∈ normalizer (X : Set G))
    (B : Subgroup G)
    (hgen : vertexGroup L T H c.gamma =
      conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H c.gamma) ⊔ B)
    (hedge : ⁅B, X.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃) :
    2 ≤ Module.finrank (ZMod 2)
      (S.N.toSubmodule ⧸
        (S.sectionModel.image (Source.DH (Source.UH H V₃)
          (c.Ugamma V₃) (c.Aone V₁))).comap S.N.toSubmodule.subtype) := by
  have hnoncentral : ¬ ⁅H, Source.VH H V⁆ ≤ Source.UH H V₃ := by
    intro hh
    apply S.noncentral
    simpa only [commutator_comm] using hh
  exact critical_section_codimension_ge_two_of_source S c hc hcomm
    (Source.VH H V) τ t X hXV hspan hindex S.plane S.plane_dim hparabolic (c.gb : G) B
    c.vertexGroup_gamma (by rfl) (by rfl) S.line_card hgen hedge hnoncentral

/-! The forward marked calculation, including the transported commutator
equality and the 13.8.9/13.8.18 generation consequences. -/

theorem critical_pair_forward_geometry
    {G U : Type*} [Group G] [Finite G]
    [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    {L T H V V₃ V₁ : Subgroup G}
    {ρ : Representation (ZMod 2) (Source.Hstar H) U}
    [IsElementaryAbelian 2 (Source.VH H V)]
    (S : SourceData L T H V V₃ V₁ ρ) (c : CriticalPair L T H V)
    (hc : Eligible S c) :
    commSpace S.N.toRepresentation (Source.starImage H (c.Ugamma V₃)) =
      commSpace S.N.toRepresentation (Source.starImage H c.Vgamma) ∧
    ⁅S.I, c.Vgamma⁆ ≤ ⁅S.I, c.Ugamma V₃⁆ ⊔ V₁ ∧
    ¬ S.I ≤ Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) ∧
    c.Vgamma ≤ normalizer (S.I : Set G) ∧
    vertexGroup L T H c.gamma =
      conjugateSpanBy S.I (vertexGroup L T H c.gamma) ⊔
        edgeGroup L T H c.gamma c.previous ∧
    ¬ V₁ ≤ c.Ugamma V₃ := by
  obtain ⟨h, _, hplace, _⟩ := hc.marked
  have hPH : S.L₁ ⊔ T ≤ H := S.edge_eq.symm.le.trans inf_le_right
  let _ : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le
    (show V ≤ Source.VH H V from le_conjugateSpanBy V H)
  have hedge := c.edge_commutator_le_of_flag V₃ S.seed_le S.flag_index S.noncentral
    S.edge_normalizes
  obtain ⟨_, _, _, hα, hγ, hcomm, _, hID, hVI, hgen, hline⟩ :=
    MarkedGeometry.forward_noncontainment_of_source V₃ V₁ S.sectionModel S.L₀ S.L₁ T
      S.L₀_le hPH S.cubic S.fixes_seed S.two_group S.seed_stable S.seed_irreducible
      S.seed_dim S.W S.maximal.ne_top S.eH S.head S.head_equivariant S.I S.line_le_I S.I_le
      S.N S.image_I S.natural_irreducible (c.gb : G) (vertexGroup L T H c.gamma)
      (edgeGroup L T H c.gamma c.previous) (c.Ugamma V₃) c.Vgamma (c.Aone V₁)
      c.vertexGroup_gamma (by rfl) (by rfl) hc.Ugamma_le hc.Vgamma_le hc.endpoint_le
      (S.endpoint_centralizer c) S.line_card hc.line_not_le hc.noncyclic hc.centers h
      hplace hc.generation
      (by
        intro F hF hVF hgen'
        exact c.noncentral_of_generation V₃ F S.V_le (hF.trans hc.endpoint_le) hgen'
          hedge S.noncentral)
  exact ⟨hγ, hcomm, hID, hVI, hgen, hline⟩

/-! This is the complete bundle consumed by the terminal noncyclic argument.
The source line, denominator, actor and marked plane are all the actual
constructions.  The equality branch is handled by the reversed critical pair,
so its fixation conclusion is returned as a function of the equality premise. -/

theorem critical_pair_endgame_inputs
    {G U : Type*} [Group G] [Finite G]
    [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    {L T H V V₃ V₁ : Subgroup G}
    {ρ : Representation (ZMod 2) (Source.Hstar H) U}
    [IsElementaryAbelian 2 (Source.VH H V)]
    (S : SourceData L T H V V₃ V₁ ρ) (c : CriticalPair L T H V)
    (hc : Eligible S c)
    (hgeo : ∀ d : CriticalPair L T H V, EarlierGeometry d V₃ V₁)
    (hcore : ∀ d : CriticalPair L T H V,
      d.Vgamma ≤ (edgeGroup L T H (base L T H true) d.second).pCoreIn 2)
    (generation18 : ∀ d : CriticalPair L T H V,
      ∀ F ≤ Source.UH H V₃,
      ¬ F ≤ Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone V₁) →
      vertexGroup L T H d.gamma =
        conjugateSpanBy F (vertexGroup L T H d.gamma) ⊔
          edgeGroup L T H d.gamma d.previous)
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃)
      (c.Aone V₁)).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex
        (c.Ugamma V₃)))
    (hIcodim : 2 ≤ Module.finrank (ZMod 2)
      (S.N.toSubmodule ⧸
        (S.sectionModel.image (Source.DH (Source.UH H V₃)
          (c.Ugamma V₃) (c.Aone V₁))).comap S.N.toSubmodule.subtype)) :
    let D := S.sectionModel.image (Source.DH (Source.UH H V₃)
      (c.Ugamma V₃) (c.Aone V₁))
    let A := Source.starImage H (c.Ugamma V₃)
    let B := Source.starImage H c.Vgamma
    ∃ g : Source.Hstar H,
      Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A ∧
      2 ≤ Module.finrank (ZMod 2)
        (S.N.toSubmodule ⧸ D.comap S.N.toSubmodule.subtype) ∧
      ¬ c.Aone V₁ ≤ Source.UH H V₃ ∧
      (Module.finrank (ZMod 2) (U ⧸ D) = rank A → D ≤ fixedSpace ρ A) ∧
      Module.finrank (ZMod 2) (S.sectionModel.image (c.Aone V₁)) ≤ 1 ∧
      (∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S.sectionModel.image (c.Aone V₁)) ∧
      A ≤ B ∧ IsElementaryTwo B ∧ 1 < rank A ∧
      Module.finrank (ZMod 2) S.plane = 2 ∧
      (B.map (MulAut.conj g).toMonoidHom).map S.eH.toMonoidHom ≤
        BinaryLinear.radical S.plane ∧
      (∀ X ≤ B, 1 < rank X → 1 < fixedCodim S.W.quotientRepresentation X) := by
  let D := S.sectionModel.image (Source.DH (Source.UH H V₃)
      (c.Ugamma V₃) (c.Aone V₁))
  let A := Source.starImage H (c.Ugamma V₃)
  let B := Source.starImage H c.Vgamma
  have hforward : (Source.UH H V₃).map (MulAut.conj (c.gb : G)).toMonoidHom ≤ H := by
    simpa only [CriticalPair.Ugamma] using hc.Ugamma_le.trans hc.Vgamma_le
  have hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom := by
    rw [← c.vertexGroup_gamma]
    exact hc.endpoint_le
  have hl := critical_pair_linear_bounds S.sectionModel (c.gb : G) hforward hreverse
    S.line_card S.faithful hcritical
  have hsym := equality_case_noncontainment_and_fixation S c hgeo hcore generation18
    hc.noncyclic hc.equality
  obtain ⟨h, _, _, hrad⟩ := hc.marked
  let g : Source.Hstar H := QuotientGroup.mk' (pCore 2 H) (h⁻¹)
  have hrad' : (B.map (MulAut.conj g).toMonoidHom).map S.eH.toMonoidHom ≤
      BinaryLinear.radical S.plane := by
    rw [← MarkedGeometry.starImage_conjugate c.Vgamma hc.Vgamma_le h⁻¹]
    exact hrad
  refine ⟨g, ?_, hIcodim, hsym.1, (fun _ => hsym.2), hl.2.1, hl.2.2.1, ?_, hc.elementary,
    hc.noncyclic, S.plane_dim, hrad', hc.axes⟩
  · convert hl.1 using 1 <;> rfl
  · exact map_mono (subgroupOf_mono H hc.Ugamma_le)

/-! Source-level assembly: the codimension argument and the critical-pair
transfer are kept as separate lemmas above, while this wrapper discharges the
former's explicit upper-section premises before exporting the complete bundle. -/

theorem critical_pair_endgame_inputs_of_source
    {G U : Type*} [Group G] [Finite G]
    [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    {L T H V V₃ V₁ : Subgroup G}
    {ρ : Representation (ZMod 2) (Source.Hstar H) U}
    [IsElementaryAbelian 2 (Source.VH H V)]
    (S : SourceData L T H V V₃ V₁ ρ) (c : CriticalPair L T H V)
    (hc : Eligible S c)
    (hgeo : ∀ d : CriticalPair L T H V, EarlierGeometry d V₃ V₁)
    (hcore : ∀ d : CriticalPair L T H V,
      d.Vgamma ≤ (edgeGroup L T H (base L T H true) d.second).pCoreIn 2)
    (generation18 : ∀ d : CriticalPair L T H V,
      ∀ F ≤ Source.UH H V₃,
      ¬ F ≤ Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone V₁) →
      vertexGroup L T H d.gamma =
        conjugateSpanBy F (vertexGroup L T H d.gamma) ⊔
          edgeGroup L T H d.gamma d.previous)
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃)
      (c.Aone V₁)).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex
        (c.Ugamma V₃)))
    (hcomm : Coinvariants.ker
        (S.N.toRepresentation.comp (Source.starImage H (c.Ugamma V₃)).subtype) =
      Coinvariants.ker
        (S.N.toRepresentation.comp (Source.starImage H c.Vgamma).subtype))
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (τ : Representation (ZMod 2) (Source.Hstar H) E)
    (t : UpperSection H (Source.VH H V) (Source.UH H V₃) τ)
    (X : Subgroup G) (hXV : X ≤ Source.VH H V)
    (hspan : Source.VH H V = conjugateSpanBy X H)
    (hindex : (Source.UH H V₃).relIndex X = 2)
    (hparabolic : ∀ a : H,
      S.eH (QuotientGroup.mk' (pCore 2 H) a) ∈ BinaryLinear.parabolic S.plane →
        (a : G) ∈ normalizer (X : Set G))
    (B : Subgroup G)
    (hgen : vertexGroup L T H c.gamma =
      conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H c.gamma) ⊔ B)
    (hedge : ⁅B, X.map (MulAut.conj (c.gb : G)).toMonoidHom⁆ ≤ c.Ugamma V₃) :
    let D := S.sectionModel.image (Source.DH (Source.UH H V₃)
      (c.Ugamma V₃) (c.Aone V₁))
    let A := Source.starImage H (c.Ugamma V₃)
    let Bstar := Source.starImage H c.Vgamma
    ∃ g : Source.Hstar H,
      Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A ∧
      2 ≤ Module.finrank (ZMod 2)
        (S.N.toSubmodule ⧸ D.comap S.N.toSubmodule.subtype) ∧
      ¬ c.Aone V₁ ≤ Source.UH H V₃ ∧
      (Module.finrank (ZMod 2) (U ⧸ D) = rank A → D ≤ fixedSpace ρ A) ∧
      Module.finrank (ZMod 2) (S.sectionModel.image (c.Aone V₁)) ≤ 1 ∧
      (∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S.sectionModel.image (c.Aone V₁)) ∧
      A ≤ Bstar ∧ IsElementaryTwo Bstar ∧ 1 < rank A ∧
      Module.finrank (ZMod 2) S.plane = 2 ∧
      (Bstar.map (MulAut.conj g).toMonoidHom).map S.eH.toMonoidHom ≤
        BinaryLinear.radical S.plane ∧
      (∀ X ≤ Bstar, 1 < rank X → 1 < fixedCodim S.W.quotientRepresentation X) := by
  have hIcodim := critical_section_codimension_ge_two_of_source_data S c hc hcomm τ t X hXV
    hspan hindex hparabolic B hgen hedge
  exact critical_pair_endgame_inputs S c hc hgeo hcore generation18 hcritical hIcodim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer

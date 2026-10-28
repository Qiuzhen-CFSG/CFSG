module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.Source
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.HeadPlane

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.RadicalPlacement.LayerAction

/-!
# The actual source radical placement in the L₄ branch

The image of V₃ in the specified conjugation section generates the whole
module. Its earlier invariance, irreducibility and dimension conclusions
therefore construct the source seed, with parabolic exactly (L₁T)*. This is
the `ChiefFactors.SourceSeed` construction for a general concrete model of
U_H/V₁; the generating argument uses the actual H-conjugate span.

The marked L₀ has quotient of order three and fixes Ṽ₃. Hence L₀* is not a
two-group and fixes the seed plane. `LayerAction` proves that these action
facts put O₂((L₁T)*) into the radical of the chosen natural head plane.
Relative normalization puts the image of O₂(L₁T) into O₂((L₁T)*).
The containment supplied by 13.8.8(2) then proves the assertion for that
same conjugator h, without changing either the head or the actor coordinates.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.25,
printed pp.960–961 (PDF pp.977–978), and 13.8.8(2), printed p.949. The
order-three quotient of L₀ is Notation 13.2.1; its fixation of Ṽ₃ and the
irreducible generating two-space are the earlier source inputs recalled
on pp.957 and 961. Natural-head existence and orientation remain inputs.
-/

@[expose] public section

open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  {H V₃ V₁ : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- The actual image of V₃ generates every concrete model of U_H/V₁. -/
theorem section_image_generates (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (W : Subrepresentation ρ) (hseed : s.image V₃ ≤ W.toSubmodule) : W = ⊤ := by
  let J : Subgroup (Source.UH H V₃) := {
    carrier := {u | (s.quotient u).toAdd ∈ W}
    one_mem' := by change (s.quotient 1).toAdd ∈ W; rw [map_one]; exact W.toSubmodule.zero_mem
    mul_mem' := by
      intro a b ha hb
      change (s.quotient (a*b)).toAdd ∈ W
      rw [map_mul]
      exact W.toSubmodule.add_mem ha hb
    inv_mem' := by
      intro a ha
      change (s.quotient a⁻¹).toAdd ∈ W
      rw [map_inv]
      exact W.toSubmodule.neg_mem ha }
  let B : Subgroup G := J.map (Source.UH H V₃).subtype
  have hVB : V₃ ≤ B := by
    intro v hv
    let u : Source.UH H V₃ := ⟨v, le_conjugateSpanBy V₃ H hv⟩
    exact ⟨u, hseed ⟨u, hv, rfl⟩, rfl⟩
  have hHB : H ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    rintro a ha _ ⟨u, hu, rfl⟩
    refine ⟨⟨a*u*a⁻¹, (mem_normalizer_iff.mp (s.normalizes ha) u).mp u.property⟩, ?_, rfl⟩
    change (s.quotient _).toAdd ∈ W
    rw [← s.conjugates ⟨a, ha⟩ u]
    exact W.apply_mem_toSubmodule _ hu
  have hUB : Source.UH H V₃ ≤ B := conjugateSpanBy_le hVB hHB
  apply top_unique
  intro v _
  obtain ⟨u, hu⟩ := s.surjective (Multiplicative.ofAdd v)
  obtain ⟨w, hw, hwu⟩ := hUB u.property
  have he : w = u := Subtype.ext hwu
  subst w
  change (s.quotient u).toAdd ∈ W at hw
  rw [hu] at hw
  exact hw

/-- Construct the marked seed from the earlier source action on Ṽ₃. -/
noncomputable def sourceGeneratingSeed
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (L₁ T : Subgroup G) (hT : IsPGroup 2 T)
    (hstable : ∀ g : Source.starImage H (L₁ ⊔ T), ∀ v ∈ s.image V₃,
      ρ g v ∈ s.image V₃)
    (hirr : IsAtom (⟨s.image V₃, hstable⟩ :
      Subrepresentation (ρ.comp (Source.starImage H (L₁ ⊔ T)).subtype)))
    (hdim : Module.finrank (ZMod 2) (s.image V₃) = 2) : GeneratingSeed ρ where
  parabolic := Source.starImage H (L₁ ⊔ T)
  sylow := Source.starImage H T
  sylow_le := map_mono (comap_mono le_sup_right)
  sylow_two_group := hT.comap_subtype.map _
  space := ⟨s.image V₃, hstable⟩
  irreducible := hirr
  dim_two := hdim
  generates := section_image_generates s

/-- Fixation modulo V₁, rather than ambient centrality, suffices. -/
theorem seed_fixed_of_commutator
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (R : Subgroup G) (hc : ⁅R, V₃⁆ ≤ V₁) :
    ∀ g ∈ Source.starImage H R, ∀ v ∈ s.image V₃, ρ g v = v := by
  intro g hg v hv
  have hd := s.displacement_mem V₃ R V₁ hc g hg v hv
  obtain ⟨u, hu, he⟩ := (s.mem_image V₁ _).mp hd
  have hz := (s.quotient_eq_zero_iff u).mpr hu
  exact sub_eq_zero.mp (he.symm.trans hz)

/-- Relative core normality survives restriction to H and its quotient map. -/
theorem starImage_core_le (H P : Subgroup G) :
    Source.starImage H (P.pCoreIn 2) ≤ (Source.starImage H P).pCoreIn 2 := by
  have hn : P ≤ normalizer (P.pCoreIn 2 : Set G) := by
    have hh := (pCore 2 P).le_normalizer_map P.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, P.range_subtype] at hh
    exact hh
  apply le_pCoreIn_of_normalizes
  · exact (isPGroup_pCoreIn 2 P).comap_subtype.map _
  · exact map_mono (comap_mono (pCoreIn_le 2 P))
  · exact (map_mono ((comap_mono hn).trans
      ((P.pCoreIn 2).le_normalizer_comap H.subtype))).trans
        (((P.pCoreIn 2).subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))


/-- The source conjugate is inside H, and its entire star image lies in the
marked radical. The two seed identifications are discharged by the source
constructor in `source_radical_placement` below. -/
theorem source_radical_placement_of_seed [Finite G]
    (sectionModel : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (L₀ L₁ T Vg : Subgroup G) (hL : L₀ ≤ L₁) (hPH : L₁ ⊔ T ≤ H)
    (hthree : Nat.card (L₀ ⧸ pCore 2 L₀) = 3) (hfix : ⁅L₀, V₃⁆ ≤ V₁)
    (seed : GeneratingSeed ρ)
    (hparabolic : seed.parabolic = Source.starImage H (L₁ ⊔ T))
    (hseed : seed.space.toSubmodule = sectionModel.image V₃)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (eH : Source.Hstar H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] ChiefFactors.NaturalSpace)
    (he : ∀ g u, e (W.quotientRepresentation g u) = eH g (e u))
    (h : H)
    (hplace : Vg.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    Vg.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom ≤ H ∧
      (Source.starImage H (Vg.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom)).map
        eH.toMonoidHom ≤ BinaryLinear.radical (headPlane ρ seed W e) := by
  have hRH : L₀ ≤ H := hL.trans (le_sup_left.trans hPH)
  have hR : ¬ IsPGroup 2 (Source.starImage H L₀) :=
    ChiefFactors.Alignment.starImage_not_two_of_cubic_quotient H L₀ hRH hthree
  have hRP : Source.starImage H L₀ ≤ seed.parabolic := by
    rw [hparabolic]
    exact map_mono (comap_mono (hL.trans le_sup_left))
  have hfixed : ∀ g ∈ Source.starImage H L₀, ∀ v ∈ seed.space.toSubmodule, ρ g v = v := by
    rw [hseed]
    exact seed_fixed_of_commutator sectionModel L₀ hfix
  have hc := seed_core_maps_radical ρ seed W hW eH e he
    (Source.starImage H L₀) hRP hR hfixed
  rw [hparabolic] at hc
  refine ⟨hplace.trans ((pCoreIn_le 2 (L₁ ⊔ T)).trans hPH), ?_⟩
  apply (map_mono (f := eH.toMonoidHom) ((map_mono (comap_mono hplace)).trans
    (starImage_core_le H (L₁ ⊔ T)))).trans hc

/-- Source 13.8.8(2)'s actual conjugate maps into the radical of the actual
seed plane in the fixed natural head. Only the earlier source seed and L₀
facts are inputs; neither radical containment nor a full-parabolic
identification is assumed. -/
theorem source_radical_placement [Finite G]
    (sectionModel : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (L₀ L₁ T Vg : Subgroup G) (hL : L₀ ≤ L₁) (hPH : L₁ ⊔ T ≤ H)
    (hthree : Nat.card (L₀ ⧸ pCore 2 L₀) = 3) (hfix : ⁅L₀, V₃⁆ ≤ V₁)
    (hT : IsPGroup 2 T)
    (hstable : ∀ g : Source.starImage H (L₁ ⊔ T), ∀ v ∈ sectionModel.image V₃,
      ρ g v ∈ sectionModel.image V₃)
    (hirr : IsAtom (⟨sectionModel.image V₃, hstable⟩ :
      Subrepresentation (ρ.comp (Source.starImage H (L₁ ⊔ T)).subtype)))
    (hdim : Module.finrank (ZMod 2) (sectionModel.image V₃) = 2)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (eH : Source.Hstar H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] ChiefFactors.NaturalSpace)
    (he : ∀ g u, e (W.quotientRepresentation g u) = eH g (e u))
    (h : H)
    (hplace : Vg.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    (Source.starImage H (Vg.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom)).map
      eH.toMonoidHom ≤ BinaryLinear.radical (headPlane ρ
        (sourceGeneratingSeed sectionModel L₁ T hT hstable hirr hdim) W e) :=
  (source_radical_placement_of_seed sectionModel L₀ L₁ T Vg hL hPH hthree hfix
    (sourceGeneratingSeed sectionModel L₁ T hT hstable hirr hdim) rfl rfl
    W hW eH e he h hplace).2

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry

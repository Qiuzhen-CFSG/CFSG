module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers.Placement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers.Cyclic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets

/-!
# Source normalizers for A₁ placement and the cyclic L₄ contradiction

These adapters use the actual critical pair: A₁ = V₁^{g_b},
Vγ = V_H^{g_b}, Uγ = U_H^{g_b}, and U_H = ⟨V₃^H⟩. The source conclusion
H = G₁ is supplied as H = N_G(V₁). Since V_H is its genuine conjugate span,
normalization of Vγ by N_G(A₁) is proved here. The specified H-element g
then transports γ to α simultaneously in ambient subgroups, quotient actor
images, and the central section.

For placement, perfectness of the point parabolic removes the possible
central lifting error, and the marked plane gives the contradiction in both
natural orientations. For the cyclic case only the derived middle parabolic
is needed: exact centralizing lifts make it normalize Vα*, and the concrete
four-group obstruction excludes this. The old blanket quotient-line-fixer
implication is not an input. The final adapter keeps the earlier module and
critical-pair conclusions and the independent marked vector explicit; the
rank contradiction and full 13.8.25 assembly remain with their source owner.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.25,
printed pp.961–962 (PDF pp.978–979), with the critical-pair definitions on
printed p.947. Conjugations here are left conjugations: use inverses of the
book's right-conjugation elements.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers
open CriticalTransfer CriticalGeometry
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  {H UH Z L T V : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- The genuine ambient normality follows from H = G₁ = N_G(V₁) and the definition of V_H. -/
theorem normalizer_Aone_le_normalizer_Vgamma (c : CriticalPair L T H V)
    (hH : H = normalizer (Z : Set G)) :
    normalizer (c.Aone Z : Set G) ≤ normalizer (c.Vgamma : Set G) := by
  change normalizer (Z.map (MulAut.conj (c.gb : G)).toMonoidHom : Set G) ≤
    normalizer ((Source.VH H V).map (MulAut.conj (c.gb : G)).toMonoidHom : Set G)
  rw [← Subgroup.map_equiv_normalizer_eq, ← hH]
  exact (Subgroup.map_mono (le_normalizer_conjugateSpanBy V H)).trans
    (Subgroup.le_normalizer_map _)

/-- The ambient γ-to-α conjugation agrees with conjugation in the actual quotient H/O₂(H). -/
theorem starImage_conjugate (X : Subgroup G) (hXH : X ≤ H) (g : H) :
    (Source.starImage H X).map
      (MulAut.conj (QuotientGroup.mk' (pCore 2 H) g)).toMonoidHom =
      Source.starImage H (X.map (MulAut.conj (g : G)).toMonoidHom) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hJH : X.map (MulAut.conj (g : G)).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem g.property (hXH hx)) (H.inv_mem g.property)
  have he : (X.subgroupOf H).map (MulAut.conj g).toMonoidHom =
      (X.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hJH, map_map]
    change (X.subgroupOf H).map ((MulAut.conj (g : G)).toMonoidHom.comp H.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le hXH]
  have hq : (MulAut.conj (q g)).toMonoidHom.comp q =
      q.comp (MulAut.conj g).toMonoidHom := by
    ext x
    simp
  unfold Source.starImage
  rw [map_map, hq, ← map_map, he]

/-- Equivariance identifies the image of the ambient conjugate with the conjugate section subspace. -/
theorem section_image_conjugate (s : ConjugationSection H UH Z ρ)
    (X : Subgroup G) (hXU : X ≤ UH) (g : H) :
    s.image (X.map (MulAut.conj (g : G)).toMonoidHom) =
      (s.image X).map (ρ (QuotientGroup.mk' (pCore 2 H) g)) := by
  ext v
  constructor
  · rintro ⟨u, ⟨x, hx, hxu⟩, rfl⟩
    let w : UH := ⟨x, hXU hx⟩
    refine ⟨(s.quotient w).toAdd, ⟨w, hx, rfl⟩, ?_⟩
    rw [s.conjugates]
    exact congrArg (fun u : UH => (s.quotient u).toAdd) (Subtype.ext hxu)
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨w, hw, rfl⟩ := (s.mem_image X v).mp hv
    rw [s.conjugates]
    exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩

open Representation Representation.BinaryOffender ChiefFactors BinaryLinear.MiddleParabolic
open CriticalTransfer.MarkedGeometry
local notation "Vec" => (Fin 4 → ZMod 2)
variable [Finite G] [FiniteDimensional (ZMod 2) U]
  {V₁ V₃ : Subgroup G}

/-- A₁ lies outside the actual I whose section is the chosen natural-or-dual irreducible. -/
theorem criticalPair_Aone_not_le
    (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hH : H = normalizer (V₁ : Set G))
    (hV₁ : Nat.card V₁ = 2) (hdisj : V₁ ⊓ c.Aone V₁ = ⊥)
    (hVgH : c.Vgamma ≤ H)
    (I : Subgroup G) (hIU : I ≤ Source.UH H V₃)
    (N : Subrepresentation ρ) (hI : s.image I = N.toSubmodule)
    (eH : Source.Hstar H ≃* BinaryLinear.GL Vec)
    (hN : IsNaturalOrDual N.toRepresentation eH)
    (hB : IsElementaryTwo (Source.starImage H c.Vgamma))
    (P : Submodule (ZMod 2) Vec) (hP : Module.finrank (ZMod 2) P = 2)
    (g : H)
    (hrad : (Source.starImage H
      (c.Vgamma.map (MulAut.conj (g : G)).toMonoidHom)).map eH.toMonoidHom ≤
      BinaryLinear.radical P) : ¬ c.Aone V₁ ≤ I := by
  have hA : Nat.card (c.Aone V₁) = 2 := by
    change Nat.card (V₁.map (MulAut.conj (c.gb : G)).toMonoidHom) = 2
    rw [Subgroup.card_map_of_injective (MulAut.conj (c.gb : G)).injective, hV₁]
  have hAZ : ¬ c.Aone V₁ ≤ V₁ := by
    intro hle
    rw [inf_eq_right.mpr hle] at hdisj
    rw [hdisj, Subgroup.card_bot] at hA
    omega
  let : IsElementaryAbelian 2 (Source.starImage H c.Vgamma) := hB.2
  apply A1_not_le_source_irreducible s (c.Aone V₁) c.Vgamma I hIU hA hAZ
    (normalizer_Aone_le_normalizer_Vgamma c hH) N hI eH hN hB.1
    (IsElementaryAbelian.isPGroup 2 _) P hP (QuotientGroup.mk' (pCore 2 H) g)
  rw [starImage_conjugate c.Vgamma hVgH g]
  exact hrad

omit [Finite G] [FiniteDimensional (ZMod 2) U] in
/-- The middle-parabolic application with fixation of the actual conjugate A₁ image left explicit. -/
theorem criticalPair_middle_contradiction_of_fixed_line
    (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hH : H = normalizer (V₁ : Set G))
    (hA1U : c.Aone V₁ ≤ Source.UH H V₃) (hVgH : c.Vgamma ≤ H)
    (eH : Source.Hstar H ≃* BinaryLinear.GL Vec)
    {K P F : Submodule (ZMod 2) Vec} (hKP : K ≤ P) (hPF : P ≤ F)
    (hK : Module.finrank (ZMod 2) K = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    (hB : IsElementaryTwo (Source.starImage H c.Vgamma))
    (hcard : Nat.card (Source.starImage H c.Vgamma) = 4)
    (g : H)
    (hrad : (Source.starImage H
      (c.Vgamma.map (MulAut.conj (g : G)).toMonoidHom)).map eH.toMonoidHom ≤
        BinaryLinear.radical P)
    (hfix : ∀ k : Source.Hstar H, eH k ∈ middle K F →
      ∀ v ∈ s.image ((c.Aone V₁).map (MulAut.conj (g : G)).toMonoidHom), ρ k v = v) : False := by
  rw [section_image_conjugate s (c.Aone V₁) hA1U g] at hfix
  rw [← starImage_conjugate c.Vgamma hVgH g] at hrad
  exact middle_contradiction_of_fixed_source_line s (c.Aone V₁) c.Vgamma hA1U
    (normalizer_Aone_le_normalizer_Vgamma c hH) eH hKP hPF hK hP hF hB hcard
    (QuotientGroup.mk' (pCore 2 H) g) hrad hfix

/-- The cyclic contradiction for the genuine critical pair; no quotient-normalizer hypothesis remains. -/
theorem criticalPair_cyclic_contradiction_of_marked_vector
    (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hH : H = normalizer (V₁ : Set G)) (hV₁ : Nat.card V₁ = 2)
    (hVgH : c.Vgamma ≤ H) (hUgH : c.Ugamma V₃ ≤ H)
    (hUA : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G))
    (eH : Source.Hstar H ≃* BinaryLinear.GL Vec)
    (hchief : ChiefFactorsNaturalOrDual ρ eH)
    (I W : Subrepresentation ρ) (hI : IsAtom I) (hIW : I ≤ W)
    (hhead : IsNatural W.quotientRepresentation eH)
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hrank : rank (Source.starImage H (c.Ugamma V₃)) = 1)
    (hB : IsElementaryTwo (Source.starImage H c.Vgamma))
    (hBrank : 1 < rank (Source.starImage H c.Vgamma))
    (hbound : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) ≤
      2 * rank (Source.starImage H (c.Ugamma V₃)))
    (hS : Module.finrank (ZMod 2) (s.image (c.Aone V₁)) = 1)
    (hDcodim : Module.finrank (ZMod 2)
      (U ⧸ s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))) ≤
        rank (Source.starImage H (c.Ugamma V₃)))
    (hIfix : I.toSubmodule ⊓
      s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)) ≤
        fixedSpace ρ (Source.starImage H c.Vgamma))
    {K P F : Submodule (ZMod 2) Vec} (hKP : K ≤ P) (hPF : P ≤ F)
    (hK : Module.finrank (ZMod 2) K = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    (g : H)
    (hrad : (Source.starImage H
      (c.Vgamma.map (MulAut.conj (g : G)).toMonoidHom)).map eH.toMonoidHom ≤
        BinaryLinear.radical P)
    (hcenter : (Source.starImage H
      ((c.Ugamma V₃).map (MulAut.conj (g : G)).toMonoidHom)).map eH.toMonoidHom ≤
        (Subgroup.center (borel K P F)).map (borel K P F).subtype)
    (v : U)
    (hv : v ∈ commSpace ρ (Source.starImage H
      ((c.Ugamma V₃).map (MulAut.conj (g : G)).toMonoidHom)))
    (hvT : v ∈ fixedSpace ρ ((borel K P F).comap eH.toMonoidHom))
    (hvW : v ∉ W.toSubmodule) : False := by
  have hAcard : Nat.card (c.Aone V₁) = 2 := by
    change Nat.card (V₁.map (MulAut.conj (c.gb : G)).toMonoidHom) = 2
    rw [Subgroup.card_map_of_injective (MulAut.conj (c.gb : G)).injective, hV₁]
  have hA1U : c.Aone V₁ ≤ Source.UH H V₃ := by
    by_contra hn
    have hz := s.image_eq_bot_of_not_le (c.Aone V₁) hAcard hn
    rw [hz, finrank_bot] at hS
    omega
  have hD := (s.critical_line_displacement (c.Ugamma V₃) (c.Aone V₁) hUA hAcard).2
  rw [← starImage_conjugate c.Vgamma hVgH g] at hrad
  rw [← starImage_conjugate (c.Ugamma V₃) hUgH g] at hcenter hv
  exact cyclic_contradiction_of_source_marked_vector s eH hchief I W hI hIW hhead
    (c.Aone V₁) c.Vgamma hA1U (normalizer_Aone_le_normalizer_Vgamma c hH)
    (Source.starImage H (c.Ugamma V₃)) hA hrank hB hBrank hbound
    (s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))) hS hDcodim hIfix hD
    hKP hPF hK hP hF (QuotientGroup.mk' (pCore 2 H) g) hrad hcenter v hv hvT hvW

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers

module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.Flag
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.SourceVector
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.NormalizedVector
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.Lifting

/-!
# Marking the source Sylow flag and its fixed vector

In the specified natural head, the actual V₂ image gives the first flag cut
and the actual V₃ image gives the second. The source Sylow subgroup maps
onto a Sylow subgroup of H/O₂(H); reconstruction of its flag supplies the
third cut and proves equality with the full flag stabilizer. The V₂ vector
is fixed in the original central section and lies outside the proper
submodule W, not merely outside a subspace in an unrelated model.

In the rank-one branch, the cyclic module calculation and central-root
identities place this vector in [Ũ_H,Uα*]. The actor Uα* is constructed as
the actual conjugate of Uγ*, and equals the ambient image of the intrinsic
center of T*. The corrected conjugator lifts through L₁T and retains the
book's initial radical placement and specified natural-head coordinates.
The source-normalizer implication and final contradiction remain with the
parent splitting argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Notation 13.2.1 and 13.8.25, printed pp.961–962
(PDF pp.978–979), with the source notation recalled on printed p.916.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking
open Subgroup Representation Representation.BinaryOffender ChiefFactors
open CriticalTransfer CriticalTransfer.MarkedGeometry BinaryLinear.MiddleParabolic

variable {G U : Type*} [Group G] [Finite G] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  {H V₃ V₁ : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- Construct the incident source flag and its actual marked fixed vector, in the given
head coordinates. Both marked image subspaces and the ambient Sylow subgroup are retained. -/
theorem source_flag_and_fixed_vector
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (V₂ L₁ : Subgroup G) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (h₂₃ : V₂ ≤ V₃) (hidx : V₁.relIndex V₂ = 2)
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hstable : ∀ a : Source.starImage H (L₁ ⊔ (T : Subgroup G)), ∀ v ∈ s.image V₃,
      ρ a v ∈ s.image V₃)
    (hirr : IsAtom (⟨s.image V₃, hstable⟩ :
      Subrepresentation (ρ.comp (Source.starImage H (L₁ ⊔ (T : Subgroup G))).subtype)))
    (hdim : Module.finrank (ZMod 2) (s.image V₃) = 2)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] NaturalSpace)
    (he : ∀ a u, e (W.quotientRepresentation a u) = eH a (e u)) :
    let seed := sourceGeneratingSeed s L₁ (T : Subgroup G) T.isPGroup' hstable hirr hdim
    let P := headPlane ρ seed W e
    ∃ (L F : Submodule (ZMod 2) NaturalSpace) (v : U),
      L = (s.image V₂).map (e.toLinearMap.comp W.toSubmodule.mkQ) ∧
      L ≤ P ∧ P ≤ F ∧ Module.finrank (ZMod 2) L = 1 ∧
      Module.finrank (ZMod 2) P = 2 ∧ Module.finrank (ZMod 2) F = 3 ∧
      (Source.starImage H (T : Subgroup G)).map eH.toMonoidHom = borel L P F ∧
      v ∈ s.image V₂ ∧ v ≠ 0 ∧
      v ∈ fixedSpace ρ ((borel L P F).comap eH.toMonoidHom) ∧
      v ∉ W.toSubmodule := by
  let seed := sourceGeneratingSeed s L₁ (T : Subgroup G) T.isPGroup' hstable hirr hdim
  let P := headPlane ρ seed W e
  let Tstar : Sylow 2 (Source.Hstar H) := (T.subtype hTH).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 H))
  obtain ⟨v, hv, hv0, hvT, hvW⟩ := exists_source_fixed_vector s V₂ L₁ (T : Subgroup G)
    h₂₃ hidx hTV₂ T.isPGroup' hstable hirr hdim W hW
  let z := e (W.toSubmodule.mkQ v)
  let L := Submodule.span (ZMod 2) {z}
  have hz : z ≠ 0 := by
    intro h
    have hq : W.toSubmodule.mkQ v = 0 := e.injective (h.trans (map_zero e).symm)
    exact hvW ((Submodule.Quotient.mk_eq_zero _).mp hq)
  have hL : Module.finrank (ZMod 2) L = 1 := finrank_span_singleton hz
  have hP : Module.finrank (ZMod 2) P = 2 := headPlane_finrank ρ seed W hW e
  have hLimage : L = (s.image V₂).map (e.toLinearMap.comp W.toSubmodule.mkQ) := by
    have hs := eq_span_singleton_of_mem_of_finrank_eq_one
      (image_finrank_one s V₂ (h₂₃.trans (le_conjugateSpanBy V₃ H)) hidx) hv hv0
    rw [hs, Submodule.map_span, Set.image_singleton]
    rfl
  have hTL : (Tstar : Subgroup (Source.Hstar H)).map eH.toMonoidHom ≤
      BinaryLinear.parabolic L := by
    rintro _ ⟨t, ht, rfl⟩ u
    change eH t u ∈ L ↔ u ∈ L
    have ht' : t ∈ Source.starImage H (T : Subgroup G) := ht
    have htz : eH t z = z := by
      calc
        eH t z = e (W.quotientRepresentation t (W.toSubmodule.mkQ v)) := (he _ _).symm
        _ = z := congrArg (fun w => e (W.toSubmodule.mkQ w)) (hvT ⟨t, ht'⟩)
    constructor
    · intro hu
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c, (eH t).injective ?_⟩
      simpa only [map_smul, htz] using hc
    · intro hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [map_smul, htz]
      exact L.smul_mem c (Submodule.mem_span_singleton_self z)
  have hTP : (Tstar : Subgroup (Source.Hstar H)).map eH.toMonoidHom ≤
      BinaryLinear.parabolic P := by
    apply le_trans (Subgroup.map_mono seed.sylow_le)
    exact headPlane_stable ρ seed W eH e he
  obtain ⟨F, hLP, hPF, hF, hflag⟩ := exists_flag_through_line_plane eH Tstar L P hL hP hTL hTP
  have hpre : (borel L P F).comap eH.toMonoidHom = Source.starImage H (T : Subgroup G) := by
    rw [← hflag, Subgroup.comap_map_eq_self_of_injective eH.injective]
    rfl
  exact ⟨L, F, v, hLimage, hLP, hPF, hL, hP, hF, hflag, hv, hv0, hpre ▸ hvT, hvW⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking
open Subgroup Representation Representation.BinaryOffender ChiefFactors
open CriticalTransfer CriticalTransfer.MarkedGeometry BinaryLinear.MiddleParabolic

variable {G U : Type*} [Group G] [Finite G] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  {H V₃ V₁ : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- Construct the source flag, central Sylow actor, and actual V₂ commutator vector.
The seed and maximal plane-parabolic action are the preceding conclusions on
printed pp.960–961; `hplace` is 13.8.8(2), and `hbound` is its quadratic bound.
The compatible chief factors and rank-one assumption give all new cyclic module
conclusions internally.

The initial `h₀` uses the book's right-conjugation convention. The returned `g`
uses left conjugation: `g = c * h₀⁻¹`, where the correction `c` belongs to L₁T.
Thus the actual ambient actors, their H/O₂(H) images, and the fixed head coordinates
stay connected. The output uses the intrinsic center of the actual source T*.
No marked-vector membership, commutator fixation, or center equality is assumed. -/
theorem source_flag_center_and_commutator_vector
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (V₂ L₀ L₁ : Subgroup G) (T : Sylow 2 G)
    (hL : L₀ ≤ L₁) (hPH : L₁ ⊔ (T : Subgroup G) ≤ H)
    (hthree : Nat.card (L₀ ⧸ pCore 2 L₀) = 3) (hfix : ⁅L₀, V₃⁆ ≤ V₁)
    (h₂₃ : V₂ ≤ V₃) (hidx : V₁.relIndex V₂ = 2)
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hstable : ∀ a : Source.starImage H (L₁ ⊔ (T : Subgroup G)), ∀ v ∈ s.image V₃,
      ρ a v ∈ s.image V₃)
    (hirr : IsAtom (⟨s.image V₃, hstable⟩ :
      Subrepresentation (ρ.comp (Source.starImage H (L₁ ⊔ (T : Subgroup G))).subtype)))
    (hdim : Module.finrank (ZMod 2) (s.image V₃) = 2)
    (I W : Subrepresentation ρ) (hI : IsAtom I) (hIW : I ≤ W) (hW : W ≠ ⊤)
    (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
    (hchief : ChiefFactorsNaturalOrDual ρ eH)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] NaturalSpace)
    (he : ∀ a u, e (W.quotientRepresentation a u) = eH a (e u))
    (hpar : (Source.starImage H (L₁ ⊔ (T : Subgroup G))).map eH.toMonoidHom =
      BinaryLinear.parabolic (headPlane ρ
        (sourceGeneratingSeed s L₁ (T : Subgroup G) T.isPGroup' hstable hirr hdim) W e))
    (Ug Vg : Subgroup G) (hUgVg : Ug ≤ Vg) (hVgH : Vg ≤ H)
    (hA : IsElementaryTwo (Source.starImage H Ug)) (hrank : rank (Source.starImage H Ug) = 1)
    (hbound : fixedCodim ρ (Source.starImage H Ug) ≤ 2 * rank (Source.starImage H Ug))
    (h₀ : H)
    (hplace : Vg.map (MulAut.conj ((h₀ : G)⁻¹)).toMonoidHom ≤
      (L₁ ⊔ (T : Subgroup G)).pCoreIn 2) :
    let seed := sourceGeneratingSeed s L₁ (T : Subgroup G) T.isPGroup' hstable hirr hdim
    let P := headPlane ρ seed W e
    let q := QuotientGroup.mk' (pCore 2 H)
    ∃ (L F : Submodule (ZMod 2) NaturalSpace) (k : BinaryLinear.GL NaturalSpace)
      (c g : H) (v : U),
      L = (s.image V₂).map (e.toLinearMap.comp W.toSubmodule.mkQ) ∧
      L ≤ P ∧ P ≤ F ∧ Module.finrank (ZMod 2) L = 1 ∧
      Module.finrank (ZMod 2) P = 2 ∧ Module.finrank (ZMod 2) F = 3 ∧
      (Source.starImage H (T : Subgroup G)).map eH.toMonoidHom = borel L P F ∧
      k ∈ BinaryLinear.parabolic P ∧ (c : G) ∈ L₁ ⊔ (T : Subgroup G) ∧
      g = c * h₀⁻¹ ∧ eH (q c) = k ∧ q g = eH.symm k * q h₀⁻¹ ∧
      Source.starImage H (Ug.map (MulAut.conj (g : G)).toMonoidHom) =
        (center (Source.starImage H (T : Subgroup G))).map
          (Source.starImage H (T : Subgroup G)).subtype ∧
      (Source.starImage H (Ug.map (MulAut.conj (g : G)).toMonoidHom)).map eH.toMonoidHom =
        (center (borel L P F)).map (borel L P F).subtype ∧
      (Source.starImage H (Vg.map (MulAut.conj (g : G)).toMonoidHom)).map eH.toMonoidHom ≤
        BinaryLinear.radical P ∧
      v ∈ s.image V₂ ∧ v ≠ 0 ∧
      v ∈ commSpace ρ (Source.starImage H (Ug.map (MulAut.conj (g : G)).toMonoidHom)) ∧
      v ∈ fixedSpace ρ ((borel L P F).comap eH.toMonoidHom) ∧
      v ∈ fixedSpace ρ (Source.starImage H (T : Subgroup G)) ∧ v ∉ W.toSubmodule := by
  let seed := sourceGeneratingSeed s L₁ (T : Subgroup G) T.isPGroup' hstable hirr hdim
  let P := headPlane ρ seed W e
  let q := QuotientGroup.mk' (pCore 2 H)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hPH
  obtain ⟨L, F, v, hLimage, hLP, hPF, hLdim, hPdim, hFdim, hflag, hv, hv0, hvT, _⟩ :=
    source_flag_and_fixed_vector s V₂ L₁ T hTH h₂₃ hidx hTV₂ hstable hirr hdim W hW eH e he
  have hpre : (borel L P F).comap eH.toMonoidHom = Source.starImage H (T : Subgroup G) := by
    rw [← hflag, Subgroup.comap_map_eq_self_of_injective eH.injective]
  have hvT' : v ∈ fixedSpace ρ seed.sylow := by rwa [hpre] at hvT
  have hvseed : v ∈ seed.space.toSubmodule ⊓ fixedSpace ρ seed.sylow :=
    ⟨s.image_mono h₂₃ hv, hvT'⟩
  have hrad := source_radical_placement s L₀ L₁ (T : Subgroup G) Vg hL hPH hthree hfix
    T.isPGroup' hstable hirr hdim W hW eH e he h₀ hplace
  have hrad' : ((Source.starImage H Vg).map (MulAut.conj (q h₀⁻¹)).toMonoidHom).map
      eH.toMonoidHom ≤ BinaryLinear.radical P := by
    rw [← starImage_conjugate Vg hVgH h₀⁻¹]
    exact hrad
  let Tstar : Sylow 2 (Source.Hstar H) := (T.subtype hTH).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 H))
  have hAB : Source.starImage H Ug ≤ Source.starImage H Vg := map_mono (comap_mono hUgVg)
  obtain ⟨k, hk, hc, hcH, hradk, hvc, hvW⟩ := normalized_center_and_vector
    ρ seed I W hI hIW hW eH hchief e he L F hLP hPF hLdim hFdim hpar Tstar rfl hflag
    (Source.starImage H Ug) (Source.starImage H Vg) hAB hA hrank hbound (q h₀⁻¹) hrad'
    v hvseed hv0
  have hkmap : k ∈ (Source.starImage H (L₁ ⊔ (T : Subgroup G))).map eH.toMonoidHom := by
    rw [hpar]
    exact hk
  obtain ⟨a, ⟨c, hcpar, hca⟩, hak⟩ := hkmap
  have hck : eH (q c) = k := by rw [hca]; exact hak
  let g := c * h₀⁻¹
  have hg : q g = eH.symm k * q h₀⁻¹ := by
    change q (c * h₀⁻¹) = _
    rw [map_mul, ← hck, eH.symm_apply_apply]
  have hUg : Source.starImage H (Ug.map (MulAut.conj (g : G)).toMonoidHom) =
      (Source.starImage H Ug).map (MulAut.conj (eH.symm k * q h₀⁻¹)).toMonoidHom := by
    rw [starImage_conjugate Ug (hUgVg.trans hVgH) g, hg]
  have hVg : Source.starImage H (Vg.map (MulAut.conj (g : G)).toMonoidHom) =
      (Source.starImage H Vg).map (MulAut.conj (eH.symm k * q h₀⁻¹)).toMonoidHom := by
    rw [starImage_conjugate Vg hVgH g, hg]
  refine ⟨L, F, k, c, g, v, hLimage, hLP, hPF, hLdim, hPdim, hFdim, hflag,
    hk, hcpar, rfl, hck, hg,
    ?_, ?_, ?_, hv, hv0, ?_, hvT, hvT', hvW⟩
  · rw [hUg]
    exact hcH
  · rw [hUg]
    exact hc
  · rw [hVg]
    exact hradk
  · rw [hUg]
    exact hvc

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking

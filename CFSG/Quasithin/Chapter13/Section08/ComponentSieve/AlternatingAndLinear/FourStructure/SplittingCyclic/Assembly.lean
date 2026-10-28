module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers


/-!
# Source assembly of A₁ placement and the cyclic contradiction

The actual central section U_H/V₁, source critical pair and earlier local
conclusions give A₁ ≰ I and m(Uγ*) > 1. The point-parabolic lifting argument
first excludes A₁ ≤ I in either natural orientation. The conjugate of
13.7.3(7) then fixes I ∩ D_H. In rank one, the quadratic bound forces W = I
and a commutator two-space; the critical index bound makes the image of A₁
nonzero. The marked V₂ seed constructs the source Sylow flag, the central
actor and its fixed commutator vector. These imply fixation by the middle
parabolic and normalization of Vα* by its derived subgroup, already excluded
by the concrete middle-parabolic calculation. This sufficient derived-group
argument handles the central lifting error without assuming that quotient
line fixation is exact ambient fixation.

All group images use the same H/O₂(H) action and actual ambient conjugators.
The explicit earlier inputs are H = G₁ = N_G(V₁), the critical-pair subgroup
and centralizer relations, 13.8.8's index and radical bounds, 13.8.18's
noncyclic Vγ*, 13.8.23's quadratic bound, and the marked parabolic/seed facts.
The compatible natural head and natural-or-dual chief factors are the
preceding part of 13.8.25. None of A₁ ≰ I, W = I, the fixed intersection,
the central-actor identity or the marked commutator vector is an input.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.961–962 (PDF pp.978–979).
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic
open ChiefFactors CriticalTransfer CriticalTransfer.MarkedGeometry CriticalGeometry

variable {G U : Type*} [Group G] [Finite G] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- A codimension-one critical denominator cannot be fixed when the full
commutator has dimension two. Thus the critical line has nonzero image. -/
theorem critical_line_finrank_of_cyclic_commutator
    (s : ConjugationSection H UH Z ρ) (Ug A : Subgroup G)
    (hUA : UH ≤ normalizer (A : Set G)) (hA : Nat.card A = 2)
    (hc : Nat.card (Source.starImage H Ug) = 2)
    (hcomm : Module.finrank (ZMod 2) (commSpace ρ (Source.starImage H Ug)) = 2)
    (hD : Module.finrank (ZMod 2) (U ⧸ s.image (Source.DH UH Ug A)) ≤ 1) :
    Module.finrank (ZMod 2) (s.image A) = 1 := by
  obtain ⟨hle, hdis⟩ := s.critical_line_displacement Ug A hUA hA
  have hnonzero : Module.finrank (ZMod 2) (s.image A) ≠ 0 := by
    intro hz
    have hbot := Submodule.finrank_eq_zero.mp hz
    have hfix : s.image (Source.DH UH Ug A) ≤ fixedSpace ρ (Source.starImage H Ug) := by
      intro d hd a
      have hm := hdis a a.property d hd
      rw [hbot] at hm
      exact sub_eq_zero.mp hm
    have hm := Submodule.finrank_mono hfix
    have hd := (s.image (Source.DH UH Ug A)).finrank_quotient_add_finrank
    have hf := fixedCodim_add_finrank ρ (Source.starImage H Ug)
    rw [commSpace_finrank_of_card_two ρ _ hc] at hcomm
    omega
  omega

variable {L V V₁ V₃ : Subgroup G}

/-- The actual critical pair satisfies A₁ ≰ I and m(Uγ*) > 1, from the earlier
source conclusions and compatible natural-module data. The flag, central
actor, marked vector, critical-line dimension and fixed intersection are
constructed in the proof. -/
theorem source_placement_and_rank
    (T : Sylow 2 G) (c : CriticalPair L (T : Subgroup G) H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hH : H = normalizer (V₁ : Set G)) (hV₁ : Nat.card V₁ = 2)
    (hdisj : V₁ ⊓ c.Aone V₁ = ⊥)
    (hUV : c.Ugamma V₃ ≤ c.Vgamma) (hVH : c.Vgamma ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hcentralizer : ⁅H.map (MulAut.conj (c.gb : G)).toMonoidHom ⊓
      centralizer (c.Ugamma V₃ : Set G), c.Vgamma⁆ ≤ c.Aone V₁)
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hB : IsElementaryTwo (Source.starImage H c.Vgamma))
    (hBrank : 1 < rank (Source.starImage H c.Vgamma))
    (hbound : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) ≤
      2 * rank (Source.starImage H (c.Ugamma V₃)))
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃)
      (c.Aone V₁)).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)))
    (V₂ L₀ L₁ : Subgroup G) (hL : L₀ ≤ L₁) (hPH : L₁ ⊔ (T : Subgroup G) ≤ H)
    (hthree : Nat.card (L₀ ⧸ pCore 2 L₀) = 3) (hfix : ⁅L₀, V₃⁆ ≤ V₁)
    (h₂₃ : V₂ ≤ V₃) (hidx : V₁.relIndex V₂ = 2)
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hstable : ∀ a : Source.starImage H (L₁ ⊔ (T : Subgroup G)), ∀ v ∈ s.image V₃,
      ρ a v ∈ s.image V₃)
    (hirr : IsAtom (⟨s.image V₃, hstable⟩ :
      Subrepresentation (ρ.comp (Source.starImage H (L₁ ⊔ (T : Subgroup G))).subtype)))
    (hdim : Module.finrank (ZMod 2) (s.image V₃) = 2)
    (I : Subgroup G) (hZI : V₁ ≤ I) (hIU : I ≤ Source.UH H V₃)
    (N W : Subrepresentation ρ) (hN : IsAtom N) (hNW : N ≤ W) (hW : W ≠ ⊤)
    (hI : s.image I = N.toSubmodule)
    (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
    (hchief : ChiefFactorsNaturalOrDual ρ eH)
    (e : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] NaturalSpace)
    (he : ∀ a u, e (W.quotientRepresentation a u) = eH a (e u))
    (hpar : (Source.starImage H (L₁ ⊔ (T : Subgroup G))).map eH.toMonoidHom =
      BinaryLinear.parabolic (headPlane ρ
        (sourceGeneratingSeed s L₁ (T : Subgroup G) T.isPGroup' hstable hirr hdim) W e))
    (h₀ : H)
    (hplace : c.Vgamma.map (MulAut.conj ((h₀ : G)⁻¹)).toMonoidHom ≤
      (L₁ ⊔ (T : Subgroup G)).pCoreIn 2) :
    (¬ c.Aone V₁ ≤ I) ∧ 1 < rank (Source.starImage H (c.Ugamma V₃)) := by
  let seed := sourceGeneratingSeed s L₁ (T : Subgroup G) T.isPGroup' hstable hirr hdim
  let P := headPlane ρ seed W e
  have hP : Module.finrank (ZMod 2) P = 2 := headPlane_finrank ρ seed W hW e
  have hrad := source_radical_placement s L₀ L₁ (T : Subgroup G) c.Vgamma hL hPH hthree hfix
    T.isPGroup' hstable hirr hdim W hW eH e he h₀ hplace
  have hnot := SourceNormalizers.criticalPair_Aone_not_le c s hH hV₁ hdisj hVH
    I hIU N hI eH (AxisExclusions.naturalOrDual_atom ρ eH hchief N hN)
    hB P hP h₀⁻¹ hrad
  refine ⟨hnot, ?_⟩
  have hAcard : Nat.card (c.Aone V₁) = 2 := by
    change Nat.card (V₁.map (MulAut.conj (c.gb : G)).toMonoidHom) = 2
    rw [Subgroup.card_map_of_injective (MulAut.conj (c.gb : G)).injective, hV₁]
  have hUA : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G) :=
    hreverse.trans ((s.centralizes_conjugate_line (c.gb : G)).trans (centralizer_le_normalizer _))
  have hIfix := (s.critical_intersection_centralizes I _ (c.Ugamma V₃) c.Vgamma
    (c.Aone V₁) hZI hIU N hI hUV hVH hreverse hUA hcentralizer hAcard hnot).2.2
  rw [hI] at hIfix
  have hhead : IsNatural W.quotientRepresentation eH := ⟨e, he⟩
  have hfaith : Function.Injective ρ := AxisExclusions.faithful_of_equivariant_surjection
    ρ W.quotientRepresentation W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective
    (fun _ _ => rfl) (AxisExclusions.natural_faithful _ eH hhead)
  have hDcodim := s.critical_bound (c.Ugamma V₃) (c.Aone V₁) (hUV.trans hVH) hfaith hcritical
  by_contra! hn
  have hrank : rank (Source.starImage H (c.Ugamma V₃)) = 1 := by
    have hp := hA.rank_pos
    omega
  obtain ⟨hWN, hWcomm, hUcomm⟩ := cyclic_sections ρ eH hchief N W hN hNW hhead
    (Source.starImage H (c.Ugamma V₃)) hA hrank hbound
  have hc : Nat.card (Source.starImage H (c.Ugamma V₃)) = 2 := by
    rw [hA.card_eq_two_pow_rank, hrank]
    rfl
  have hS := critical_line_finrank_of_cyclic_commutator s (c.Ugamma V₃) (c.Aone V₁)
    hUA hAcard hc hUcomm (by simpa only [hrank] using hDcodim)
  obtain ⟨K, F, k, a, g, v, hKimage, hKP, hPF, hK, hP', hF, hflag,
    hk, ha, hg, hak, hqg, hcenterSource, hcenter, hradg, hv₂, hv0, hv, hvT, hvSourceT, hvW⟩ :=
    CyclicMarking.source_flag_center_and_commutator_vector s V₂ L₀ L₁ T hL hPH hthree hfix
      h₂₃ hidx hTV₂ hstable hirr hdim N W hN hNW hW eH hchief e he hpar
      (c.Ugamma V₃) c.Vgamma hUV hVH hA hrank hbound h₀ hplace
  exact SourceNormalizers.criticalPair_cyclic_contradiction_of_marked_vector c s hH hV₁
    hVH (hUV.trans hVH) hUA eH hchief N W hN hNW hhead hA hrank hB hBrank hbound
    hS hDcodim hIfix hKP hPF hK hP' hF g hradg hcenter.le v hv hvT hvW

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic

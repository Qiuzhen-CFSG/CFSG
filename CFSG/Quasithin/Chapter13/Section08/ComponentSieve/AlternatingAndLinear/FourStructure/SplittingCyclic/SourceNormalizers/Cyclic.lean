module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers.Lifting
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers.MiddleDerived
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicContradiction

/-!
# The cyclic contradiction from ambient source normality

Fixation of the conjugate critical line makes the derived middle parabolic
normalize the actual conjugate Vγ*. The natural-or-dual hyperplane calculation
gives its order four, and the concrete derived-parabolic obstruction excludes
it. Thus the source argument needs neither a blanket implication from quotient
fixation to actor normalization nor assumed relative normality of Vα*.

The marked-vector adapter retains the established cyclic module calculations
and their actual line image in the central section. The marked vector is an
independent source input, as in the original conditional adapter.

Source: Aschbacher–Smith 13.8.25, printed pp.961–962 (PDF pp.978–979).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers
open Representation Representation.BinaryOffender ChiefFactors CriticalTransfer
open CriticalTransfer.MarkedGeometry BinaryLinear.MiddleParabolic
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}
  (s : ConjugationSection H UH Z ρ)

/-- Fixation of the conjugate source line already excludes an elementary four-group in the marked radical. -/
theorem middle_contradiction_of_fixed_source_line
    (A1 Vg : Subgroup G) (hA1U : A1 ≤ UH)
    (hn : normalizer (A1 : Set G) ≤ normalizer (Vg : Set G))
    (eH : Source.Hstar H ≃* BinaryLinear.GL V)
    {L P F : Submodule (ZMod 2) V} (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    (hB : IsElementaryTwo (Source.starImage H Vg))
    (hcard : Nat.card (Source.starImage H Vg) = 4)
    (g : Source.Hstar H)
    (hrad : ((Source.starImage H Vg).map (MulAut.conj g).toMonoidHom).map
      eH.toMonoidHom ≤ BinaryLinear.radical P)
    (hfix : ∀ k : Source.Hstar H, eH k ∈ middle L F →
      ∀ v ∈ (s.image A1).map (ρ g), ρ k v = v) : False := by
  let Bα := (Source.starImage H Vg).map (MulAut.conj g).toMonoidHom
  let E := Bα.map eH.toMonoidHom
  let : IsElementaryAbelian 2 (Source.starImage H Vg) := hB.2
  let : IsElementaryAbelian 2 Bα := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hEcard : Nat.card E = 4 := by
    dsimp only [E, Bα]
    rw [Subgroup.card_map_of_injective eH.injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  let M := (middle L F).comap eH.toMonoidHom
  have hnM := derived_normalizes_conjugate_starImage s A1 Vg hA1U hn g M hfix
  have hmap : M.map eH.toMonoidHom = middle L F :=
    Subgroup.map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr eH.surjective]; exact le_top)
  have hnormE : ⁅middle L F, middle L F⁆ ≤ normalizer (E : Set (BinaryLinear.GL V)) := by
    rw [← hmap, ← Subgroup.map_commutator]
    exact (Subgroup.map_mono hnM).trans (Subgroup.le_normalizer_map _)
  exact MiddleDerived.no_derived_normal_elementary_four hLP hPF hL hP hF E hEcard
    ((hrad.trans (radical_plane_le_borel hLP hPF)).trans inf_le_left) hnormE

variable [FiniteDimensional (ZMod 2) U]

/-- The marked-vector cyclic contradiction with ambient normality in place of the unproved quotient-normalizer premise. -/
theorem cyclic_contradiction_of_source_marked_vector
    (eH : Source.Hstar H ≃* BinaryLinear.GL V)
    (hchief : ChiefFactors.ChiefFactorsNaturalOrDual ρ eH)
    (I W : Subrepresentation ρ) (hI : IsAtom I) (hIW : I ≤ W)
    (hhead : ChiefFactors.IsNatural W.quotientRepresentation eH)
    (A1 Vg : Subgroup G) (hA1U : A1 ≤ UH)
    (hn : normalizer (A1 : Set G) ≤ normalizer (Vg : Set G))
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A) (hrank : rank A = 1)
    (hB : IsElementaryTwo (Source.starImage H Vg)) (hBrank : 1 < rank (Source.starImage H Vg))
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (D : Submodule (ZMod 2) U) (hS : Module.finrank (ZMod 2) (s.image A1) = 1)
    (hDcodim : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hIfix : I.toSubmodule ⊓ D ≤ fixedSpace ρ (Source.starImage H Vg))
    (hD : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ (s.image A1))
    {L P F : Submodule (ZMod 2) V} (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    (g : Source.Hstar H)
    (hrad : ((Source.starImage H Vg).map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom ≤
      BinaryLinear.radical P)
    (hcenter : (A.map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom ≤
      (Subgroup.center (borel L P F)).map (borel L P F).subtype)
    (v : U) (hv : v ∈ commSpace ρ (A.map (MulAut.conj g).toMonoidHom))
    (hvT : v ∈ fixedSpace ρ ((borel L P F).comap eH.toMonoidHom))
    (hvW : v ∉ W.toSubmodule) : False := by
  obtain ⟨hWI, hW, hU⟩ := cyclic_sections ρ eH hchief I W hI hIW hhead A hA hrank hbound
  have hIf := AxisExclusions.naturalOrDual_faithful _ eH
    (AxisExclusions.naturalOrDual_atom ρ eH hchief I hI)
  obtain ⟨hfix, hsupI⟩ := hyperplane_and_supplement_of_fixed_intersection ρ I hIf
    (Source.starImage H Vg) hB.1 D (by simpa only [hrank] using hDcodim) hIfix
  have hsup : W.toSubmodule ⊔ D = ⊤ := by rw [hWI]; exact hsupI
  have hSC : (s.image A1) ≤ commSpace ρ A := by
    rw [commSpace_eq_line_sup_of_supplement ρ W D (s.image A1) A hsup hD hS hW hU]
    exact le_sup_right
  have hc : (borel L P F).comap eH.toMonoidHom ≤
      Subgroup.centralizer (A.map (MulAut.conj g).toMonoidHom : Set (Source.Hstar H)) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    apply eH.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      Subgroup.mem_centralizer_iff.mp (centralizes_flag_center hLP hPF hL hF ht.1)
        (eH a) (hcenter (Subgroup.mem_map_of_mem _ ha))
  have hT := commSpace_fixed_of_marked_vector ρ W
    (A.map (MulAut.conj g).toMonoidHom) ((borel L P F).comap eH.toMonoidHom) hc
    ((conjugate_commSpace_finrank W.toRepresentation A g).trans hW)
    ((conjugate_commSpace_finrank ρ A g).trans hU) v hv hvT hvW
  have hcard := card_eq_four_of_naturalOrDual_hyperplane I.toRepresentation eH
    (AxisExclusions.naturalOrDual_atom ρ eH hchief I hI) (Source.starImage H Vg)
    hB hBrank P hP g hrad hfix
  have hMfix := middle_fixes_commSpace ρ eH hLP hPF hL hP hF _ hcenter hT
  apply middle_contradiction_of_fixed_source_line s A1 Vg hA1U hn eH hLP hPF hL hP hF
    hB hcard g hrad
  intro k hk v hv
  have hm : v ∈ commSpace ρ (A.map (MulAut.conj g).toMonoidHom) := by
    rw [commSpace_conjugate]
    exact Submodule.map_mono hSC hv
  exact hMfix hm ⟨k, hk⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers

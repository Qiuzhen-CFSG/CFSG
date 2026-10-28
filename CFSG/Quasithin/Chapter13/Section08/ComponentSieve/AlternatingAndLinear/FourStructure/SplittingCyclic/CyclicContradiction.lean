module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicRank.NaturalOrDual

/-!
# The conditional middle-parabolic cyclic contradiction

The cyclic module calculation gives W = I and the commutator two-space.
A marked fixed vector outside W fixes this space under the Borel, hence
under the middle parabolic. Fixation of the conjugate critical line makes
the actual conjugate actor normal there. Its order is four by the faithful
natural-or-dual action on I, contradicting the concrete middle-parabolic
obstruction. The flag, relative normality and conjugator are all explicit.

The final theorem deliberately retains two source inputs: fixation of the
critical line must normalize Vγ*, and the marked V₂ vector must lie in the
central-involution commutator space outside W. Constructing these from the
actual central section remains the source assembly owner's obligation.
The theorem is not yet the unconditional source rank(Uγ*) > 1 conclusion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.961–962 (PDF pp.978–979).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic

open Representation Representation.BinaryOffender ChiefFactors
open CriticalTransfer.MarkedGeometry
open BinaryLinear.MiddleParabolic

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

/-- The plane radical preserves every incident line and hyperplane, hence lies in the
full flag stabilizer. -/
theorem radical_plane_le_borel
    {L P F : Submodule (ZMod 2) V} (hLP : L ≤ P) (hPF : P ≤ F) :
    BinaryLinear.radical P ≤ borel L P F := by
  intro a ha
  refine ⟨⟨?_, ?_⟩, BinaryLinear.radical_le_parabolic P ha⟩
  · intro v
    constructor
    · intro hv
      have hh := (BinaryLinear.radical P).inv_mem ha
      have he : v = a v := by simpa using hh.1 (a v) (hLP hv)
      exact he.symm ▸ hv
    · intro hv
      simpa only [ha.1 v (hLP hv)] using hv
  · intro v
    constructor
    · intro hv
      have hd := hPF (ha.2 v)
      have hh := F.sub_mem hv hd
      simpa using hh
    · intro hv
      have hh := F.add_mem (hPF (ha.2 v)) hv
      simpa using hh

/-- The actual conjugate actor is a relatively normal elementary four-group in the middle
parabolic, contradicting its concrete obstruction. Its order comes from the chosen
natural-or-dual module. -/
theorem middle_contradiction_of_commSpace
    (eH : H ≃* BinaryLinear.GL V)
    {L P F : Submodule (ZMod 2) V} (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    (A B : Subgroup H) (hB : IsElementaryTwo B) (hBrank : 1 < rank B)
    (S : Submodule (ZMod 2) U) (hSC : S ≤ commSpace ρ A)
    (hnorm : ∀ k : H, (∀ s ∈ S, ρ k s = s) →
      k ∈ Subgroup.normalizer (B : Set H))
    (g : H)
    (hrad : (B.map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom ≤
      BinaryLinear.radical P)
    (J : Subrepresentation ρ) (hJ : ChiefFactors.IsNaturalOrDual J.toRepresentation eH)
    (hfix : fixedCodim J.toRepresentation B = 1)
    (hcenter : (A.map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom ≤
      (Subgroup.center (borel L P F)).map (borel L P F).subtype)
    (hT : commSpace ρ (A.map (MulAut.conj g).toMonoidHom) ≤
      fixedSpace ρ ((borel L P F).comap eH.toMonoidHom)) : False := by
  let Bα := B.map (MulAut.conj g).toMonoidHom
  let E := Bα.map eH.toMonoidHom
  let : IsElementaryAbelian 2 B := hB.2
  let : IsElementaryAbelian 2 Bα := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hcard := card_eq_four_of_naturalOrDual_hyperplane J.toRepresentation eH hJ
    B hB hBrank P hP g hrad hfix
  have hEcard : Nat.card E = 4 := by
    dsimp only [E, Bα]
    rw [Subgroup.card_map_of_injective eH.injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  have hMfix := middle_fixes_commSpace ρ eH hLP hPF hL hP hF _ hcenter hT
  have hEH : E ≤ middle L F :=
    (hrad.trans (radical_plane_le_borel hLP hPF)).trans inf_le_left
  have hnormE : middle L F ≤ Subgroup.normalizer (E : Set (BinaryLinear.GL V)) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk x hx
    obtain ⟨b, hb, rfl⟩ := hx
    have hkfix : ∀ s ∈ S.map (ρ g), ρ (eH.symm k) s = s := by
      intro s hs
      have hmem : s ∈ commSpace ρ (A.map (MulAut.conj g).toMonoidHom) := by
        rw [commSpace_conjugate]
        exact Submodule.map_mono hSC hs
      exact hMfix hmem ⟨eH.symm k, by simpa using hk⟩
    have hkn := fixed_conjugate_line_normalizes ρ S B g (eH.symm k) hnorm hkfix
    refine Subgroup.mem_map.mpr
      ⟨eH.symm k * b * (eH.symm k)⁻¹, (hkn b).mp hb, ?_⟩
    simp
  exact no_normal_elementary_four hLP hPF hL hP hF E hEcard hEH hnormE

/-- The cyclic contradiction assembled from the module calculations, source intersection
and critical-line displacement, with precisely the source normalizer and marked-
vector inputs still explicit. -/
theorem cyclic_contradiction_of_marked_vector
    (eH : H ≃* BinaryLinear.GL V)
    (hchief : ChiefFactors.ChiefFactorsNaturalOrDual ρ eH)
    (I W : Subrepresentation ρ) (hI : IsAtom I) (hIW : I ≤ W)
    (hhead : ChiefFactors.IsNatural W.quotientRepresentation eH)
    (A B : Subgroup H) (hA : IsElementaryTwo A) (hrank : rank A = 1)
    (hB : IsElementaryTwo B) (hBrank : 1 < rank B)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (D S : Submodule (ZMod 2) U) (hS : Module.finrank (ZMod 2) S = 1)
    (hDcodim : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hIfix : I.toSubmodule ⊓ D ≤ fixedSpace ρ B)
    (hD : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hnorm : ∀ k : H, (∀ s ∈ S, ρ k s = s) →
      k ∈ Subgroup.normalizer (B : Set H))
    {L P F : Submodule (ZMod 2) V} (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    (g : H)
    (hrad : (B.map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom ≤
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
    B hB.1 D (by simpa only [hrank] using hDcodim) hIfix
  have hsup : W.toSubmodule ⊔ D = ⊤ := by rw [hWI]; exact hsupI
  have hSC : S ≤ commSpace ρ A := by
    rw [commSpace_eq_line_sup_of_supplement ρ W D S A hsup hD hS hW hU]
    exact le_sup_right
  have hc : (borel L P F).comap eH.toMonoidHom ≤
      Subgroup.centralizer (A.map (MulAut.conj g).toMonoidHom : Set H) := by
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
  exact middle_contradiction_of_commSpace ρ eH hLP hPF hL hP hF A B hB hBrank
    S hSC hnorm g hrad I (AxisExclusions.naturalOrDual_atom ρ eH hchief I hI) hfix hcenter hT

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic

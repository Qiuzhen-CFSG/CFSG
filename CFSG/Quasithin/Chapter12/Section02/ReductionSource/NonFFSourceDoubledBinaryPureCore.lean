module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureCore
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureDual
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPureSylow

/-!
# The pure-line centralizer completes the binary terminal geometry

For the actual offender commutator line, its aligned local Sylow preserves
both original marked factors. Each factor has a nonzero fixed vector modulo
the line. Under the explicit source 7.7.2 hypothesis, central-quotient
characteristic two puts these lifts in the original centralizer two-core.
The point stabilizer then puts the whole natural factor and at least four
vectors of the companion dual factor in that core. Both orientations of
the pure line are handled by the original graph action.

Thus the core intersects the order-64 orbit in at least 32 elements. The
proved core escape makes that intersection a hyperplane, and the original
pair-generation/Baer–Suzuki theorem supplies the contradiction. The actual
chosen-module application consequently produces a pure-line centralizer
which is not of characteristic two, under the still-explicit w≤1 bound.
No quotient fixed-space, irreducibility or hyperplane-placement premise
remains. Source 7.7.2, the bound w≤1, the other doubled rows and the full
non-FF contradiction remain obligations of qt-d-1222-nonff-doubled.

Source: Aschbacher–Smith H.4.1, A.1.8, B.2.14 and 7.6.1,
printed pp.21,78,380,702–703, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE
open DoubledBinaryPureCore DoubledBinaryPureFactors
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- For the same original conjugator, the pure-line Sylow preserves both
factors, and each factor supplies a fixed-vector lift outside the line.
Under source 7.7.2, their full local conjugate spans lie in the two-core. -/
theorem sourceOrbit_binary_pureLine_fixed_seeds
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G))
    (Z : Subgroup G) (hZ : Nat.card Z = 2)
    (hpure : Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom) :
    let Vt := V.map (MulAut.conj t).toMonoidHom
    let C := centralizer (Z : Set G)
    let S := (T : Subgroup G) ⊓ C
    S ≤ normalizer (V : Set G) ⊓ normalizer (Vt : Set G) ∧
      (∃ x ∈ fixedModuloLine Z V S, x ∉ Z) ∧
      (∃ y ∈ fixedModuloLine Z Vt S, y ∉ Z) ∧
      (∀ P : Sylow 2 C, (P : Subgroup C).map C.subtype = S →
        HasCharacteristicTwo C →
        conjugateSpanBy (fixedModuloLine Z V S ⊔ fixedModuloLine Z Vt S)
          (L ⊓ C) ≤ C.pCoreIn 2) := by
  dsimp only
  let W := D.sourceOrbit
  let Vt := V.map (MulAut.conj t).toMonoidHom
  let C := centralizer (Z : Set G)
  let S := (T : Subgroup G) ⊓ C
  have hVW : V ≤ W := by
    change V ≤ D.sourceOrbit
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  have hVtW : Vt ≤ W := (map_mono hVW).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (D.sourceOrbit_weakClosure_setup.normalizes ht))
  obtain ⟨t₀,_,_,_,_,E,a,_,_,hinner,hcov,hV,hVt₀⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  let tN : normalizer (W : Set G) := ⟨t,D.sourceOrbit_weakClosure_setup.normalizes ht⟩
  have hother : Vt = V.map (MulAut.conj t₀).toMonoidHom :=
    outer_conjugate_eq W V _ hVW
      (card_map_of_injective (MulAut.conj t₀).injective).symm E a hcov hV hVt₀ tN
      (fun hi => hnt ((hinner tN).mp hi))
  have hVt : ∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ Vt := by
    intro w
    rw [hother]
    exact hVt₀ w
  have hZne : Z ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hZ
    contradiction
  have hn := pureLine_normalizes_factors W V Vt Z hVW hVtW E a hcov hV hVt hZne hpure
  have hSN : S ≤ normalizer (V : Set G) ⊓ normalizer (Vt : Set G) :=
    (le_inf (inf_le_left.trans D.sourceOrbit_weakClosure_setup.normalizes) inf_le_right).trans hn
  have hZW : Z ≤ W := hpure.elim (fun hh => hh.trans hVW) (fun hh => hh.trans hVtW)
  have hWS : W ≤ S := le_inf D.sourceOrbit_weakClosure_setup.le_sylow
    ((le_centralizer W).trans (centralizer_le hZW))
  have hcardV := natural_factor_card W V hVW E hV
  have hcardVt : Nat.card Vt = 8 := by
    rw [card_map_of_injective (MulAut.conj t).injective,hcardV]
  have hVZ : ¬ V ≤ Z := by
    intro hh
    have hc := Nat.card_le_card_of_injective (inclusion hh) (inclusion_injective hh)
    rw [hcardV,hZ] at hc
    omega
  have hVtZ : ¬ Vt ≤ Z := by
    intro hh
    have hc := Nat.card_le_card_of_injective (inclusion hh) (inclusion_injective hh)
    rw [hcardVt,hZ] at hc
    omega
  refine ⟨hSN,exists_fixedModuloLine_outside Z V S (T.isPGroup'.to_le inf_le_left)
    (hVW.trans hWS) (hSN.trans inf_le_left) inf_le_right hVZ,
    exists_fixedModuloLine_outside Z Vt S (T.isPGroup'.to_le inf_le_left)
      (hVtW.trans hWS) (hSN.trans inf_le_right) inf_le_right hVtZ,?_⟩
  intro P hP hc
  have hpZ := (IsElementaryAbelian.isPGroup 2 W).to_le hZW
  apply conjugateSpanBy_le
  · exact sup_le (fixedModuloLine_le_core Z V S hpZ hc P hP)
      (fixedModuloLine_le_core Z Vt S hpZ hc P hP)
  · exact inf_le_right.trans (C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (pCore 2 C)))


/-- Source 7.7.2 and the actual local Sylow placement put the whole original
natural factor in the centralizer core. The fixed seed and irreducibility
premises of printed p.702 are discharged, without assuming W = V. -/
theorem sourceOrbit_binary_natural_factor_le_pureLine_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (Z : Subgroup G) (hZ : Nat.card Z = 2) (hZV : Z ≤ V)
    (P : Sylow 2 (centralizer (Z : Set G)))
    (hP : (P : Subgroup _).map (centralizer (Z : Set G)).subtype =
      (T : Subgroup G) ⊓ centralizer (Z : Set G))
    (hc : HasCharacteristicTwo (centralizer (Z : Set G))) :
    V ≤ (centralizer (Z : Set G)).pCoreIn 2 := by
  obtain ⟨t,ht,hnt,q,hq,E,a,hE,_,_,hcov,hV,_⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  obtain ⟨_,⟨x,hx,hxZ⟩,_,_⟩ := D.sourceOrbit_binary_pureLine_fixed_seeds
    h hd F hF hmodel t ht hnt Z hZ (Or.inl hZV)
  have hVW : V ≤ D.sourceOrbit := by
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  let C := centralizer (Z : Set G)
  let S := (T : Subgroup G) ⊓ C
  have hZC : Z ≤ C := (hZV.trans hVW).trans
    ((le_centralizer D.sourceOrbit).trans (centralizer_le (hZV.trans hVW)))
  have hVC : V ≤ C := hVW.trans
    ((le_centralizer D.sourceOrbit).trans (centralizer_le (hZV.trans hVW)))
  have hpZ := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le (hZV.trans hVW)
  have hZN : Z ≤ C.pCoreIn 2 := le_pCoreIn_of_normalizes hpZ hZC
    (Subgroup.centralizer_le_normalizer _)
  have hxV : x ∈ V := ((mem_fixedModuloLine Z V S hVC inf_le_right x).mp hx).1
  have hxcore := fixedModuloLine_le_core Z V S hpZ hc P hP hx
  exact DoubledBinaryPureNatural.natural_factor_le_of_fixed_seed D.sourceOrbit L V Z
    (C.pCoreIn 2) D.sourceOrbit_component_normalizes hVW q hq E hE hV hZ hZV hZN
    (inf_le_right.trans (C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (pCore 2 C)))) x hxV hxcore hxZ



/-- Either orientation of the pure line forces a core intersection of
order at least 32, from characteristic two and the actual Sylow marking. -/
theorem sourceOrbit_binary_pureLine_core_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G))
    (Z : Subgroup G) (hZ : Nat.card Z = 2)
    (hpure : Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom)
    (P : Sylow 2 (centralizer (Z : Set G)))
    (hP : (P : Subgroup _).map (centralizer (Z : Set G)).subtype =
      (T : Subgroup G) ⊓ centralizer (Z : Set G))
    (hc : HasCharacteristicTwo (centralizer (Z : Set G))) :
    32 ≤ Nat.card (D.sourceOrbit ⊓ (centralizer (Z : Set G)).pCoreIn 2 : Subgroup G) := by
  let W := D.sourceOrbit
  let Vt := V.map (MulAut.conj t).toMonoidHom
  let C := centralizer (Z : Set G)
  let S := (T : Subgroup G) ⊓ C
  have hVW : V ≤ W := by
    change V ≤ D.sourceOrbit
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  have hVtW : Vt ≤ W := (map_mono hVW).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (D.sourceOrbit_weakClosure_setup.normalizes ht))
  obtain ⟨t₀,_,_,q,hq,E,a,hE,_,hinner,hcov,hV,hVt₀⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  let tN : normalizer (W : Set G) := ⟨t,D.sourceOrbit_weakClosure_setup.normalizes ht⟩
  have hother : Vt = V.map (MulAut.conj t₀).toMonoidHom :=
    outer_conjugate_eq W V _ hVW
      (card_map_of_injective (MulAut.conj t₀).injective).symm E a hcov hV hVt₀ tN
      (fun hi => hnt ((hinner tN).mp hi))
  have hVt : ∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ Vt := by
    intro w
    rw [hother]
    exact hVt₀ w
  have hcardV := natural_factor_card W V hVW E hV
  have hcardVt : Nat.card Vt = 8 := by
    rw [card_map_of_injective (MulAut.conj t).injective,hcardV]
  have hZW : Z ≤ W := hpure.elim (fun hh => hh.trans hVW) (fun hh => hh.trans hVtW)
  have hWS : W ≤ S := le_inf D.sourceOrbit_weakClosure_setup.le_sylow
    ((le_centralizer W).trans (centralizer_le hZW))
  have hn := (D.sourceOrbit_binary_pureLine_fixed_seeds h hd F hF hmodel t ht hnt Z hZ hpure).1
  rcases hpure with hZV | hZVt
  · exact DoubledBinaryPureDual.core_intersection_card W L V Vt Z S
      D.sourceOrbit_component_normalizes hVW hVtW q hq E hE hV hVt hcardVt
      hZ hZV hWS hn P hP hc
  · let E' := E.trans BinaryLinearThree.NaturalDual.graphSwap
    let q' := BinaryLinearThree.AutomorphismAction.graph.toMonoidHom.comp q
    have hE' (l : L) (w : Additive W) :
        E' (automizerRepresentation W (W.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes l)) w) =
            BinaryLinearThree.NaturalDual.action (q' l) (E' w) := by
      change BinaryLinearThree.NaturalDual.graphSwap (E _) =
        BinaryLinearThree.NaturalDual.action (BinaryLinearThree.AutomorphismAction.graph (q l))
          (BinaryLinearThree.NaturalDual.graphSwap (E w))
      have he : E (automizerRepresentation W (W.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes l)) w) =
            BinaryLinearThree.NaturalDual.action (q l) (E w) := hE l w
      rw [he,BinaryLinearThree.NaturalDual.graphSwap_covariance]
    have hA' (w : Additive W) : (E' w).2 = 0 ↔ (w.toMul : G) ∈ Vt := by
      change BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv (E w).1 = 0 ↔ _
      rw [LinearEquiv.map_eq_zero_iff]
      exact hVt w
    have hB' (w : Additive W) : (E' w).1 = 0 ↔ (w.toMul : G) ∈ V := by
      change BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm.toLinearEquiv (E w).2 = 0 ↔ _
      rw [LinearEquiv.map_eq_zero_iff]
      exact hV w
    exact DoubledBinaryPureDual.core_intersection_card W L Vt V Z S
      D.sourceOrbit_component_normalizes hVtW hVW q'
      (BinaryLinearThree.AutomorphismAction.graph.surjective.comp hq) E' hE' hA' hB' hcardV
      hZ hZVt hWS (le_inf (hn.trans inf_le_right) (hn.trans inf_le_left)) P hP hc

/-- The original binary offender is impossible once source 7.7.2 holds
for its pure line. The quotient fixed spaces, both factor arguments and
hyperplane/core placement are discharged here, with w≤1 retained. -/
theorem sourceOrbit_binary_false_of_pureLine_characteristicTwo
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1)
    {g : G} (hg : IsWOffenderAt D.sourceOrbit T g)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G))
    (Z : Subgroup G) (hZ : Nat.card Z = 2)
    (hpure : Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom)
    (hZW : Z ≤ D.sourceOrbit) (hZg : Z ≤ D.sourceOrbit.map (MulAut.conj g).toMonoidHom)
    (P : Sylow 2 (centralizer (Z : Set G)))
    (hP : (P : Subgroup _).map (centralizer (Z : Set G)).subtype =
      (T : Subgroup G) ⊓ centralizer (Z : Set G))
    (hc : HasCharacteristicTwo (centralizer (Z : Set G))) : False := by
  have hcard := D.sourceOrbit_binary_pureLine_core_card h hd F hF hmodel t ht hnt Z hZ hpure P hP hc
  have hnot := D.sourceOrbit_binary_not_le_sharedLine_core h hd F hF hmodel hnon hw hg hZW hZ hZg
  let A := D.sourceOrbit ⊓ (centralizer (Z : Set G)).pCoreIn 2
  have hW : Nat.card D.sourceOrbit = 64 := by
    obtain ⟨_,_,_,_,_,E,_⟩ := D.sourceOrbit_binary_pair_coordinates h hd F hF hmodel
    change Nat.card (Additive D.sourceOrbit) = 64
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2)]
    norm_num [BinaryLinearThree.NaturalDual.Space,Module.finrank_prod,
      BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  have hi : A.relIndex D.sourceOrbit = 2 := by
    have hcount := relIndex_mul_card_of_le (show A ≤ D.sourceOrbit from inf_le_left)
    rw [hW] at hcount
    have hn : A.relIndex D.sourceOrbit ≠ 1 := fun he =>
      hnot ((relIndex_eq_one.mp he).trans inf_le_right)
    change 32 ≤ Nat.card A at hcard
    have hpos : 0 < A.relIndex D.sourceOrbit := Nat.pos_of_ne_zero (by
      intro he
      rw [he,zero_mul] at hcount
      contradiction)
    have hlo : 2 ≤ A.relIndex D.sourceOrbit := by omega
    apply le_antisymm _ hlo
    nlinarith [Nat.mul_le_mul_left (A.relIndex D.sourceOrbit) hcard]
  exact hnot (D.sourceOrbit_binary_le_centralizer_core_of_hyperplane h hd F hF hmodel hnon hw
    hZW (show A ≤ D.sourceOrbit from inf_le_left) hi inf_le_right)


/-- The actual offender and pure commutator line have two nonzero quotient
fixed seeds. The source characteristic-two premise places both local spans
in the same centralizer core which the offender hyperplane must escape. -/
theorem sourceOrbit_binary_exists_pureLine_fixed_seeds
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit T g ∧
      ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
        let Vt := V.map (MulAut.conj t).toMonoidHom
        let Z := ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆
        let C := centralizer (Z : Set G)
        let S := (T : Subgroup G) ⊓ C
        Nat.card Z = 2 ∧ (Z ≤ V ∨ Z ≤ Vt) ∧
        Z ≤ D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ∧
        D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ C ∧
        (∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = S) ∧
        S ≤ normalizer (V : Set G) ⊓ normalizer (Vt : Set G) ∧
        (∃ x ∈ fixedModuloLine Z V S, x ∉ Z) ∧
        (∃ y ∈ fixedModuloLine Z Vt S, y ∉ Z) ∧
        (HasCharacteristicTwo C →
          conjugateSpanBy (fixedModuloLine Z V S ⊔ fixedModuloLine Z Vt S)
            (L ⊓ C) ≤ C.pCoreIn 2) ∧
        ¬ D.sourceOrbit ≤ C.pCoreIn 2 ∧
        ¬ offenderFixedSpan D.sourceOrbit g ≤ C.pCoreIn 2 := by
  obtain ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,⟨P,hP⟩,hWcore,hAcore⟩ :=
    D.sourceOrbit_binary_exists_sylow_pureLine_core_obstruction h hd F hF hmodel hnon hw
  obtain ⟨hn,hx,hy,hcore⟩ := D.sourceOrbit_binary_pureLine_fixed_seeds
    h hd F hF hmodel t ht hnt _ hZ hpure
  exact ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,⟨P,hP⟩,hn,hx,hy,
    hcore P hP,hWcore,hAcore⟩


/-- The exact remaining binary obstruction is a pure-line centralizer
failing source 7.7.2. The line is the actual offender commutator and its
local Sylow is aligned with the original T. No geometric callback remains. -/
theorem sourceOrbit_binary_exists_pureLine_not_characteristicTwo
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1) :
    ∃ g : G, IsWOffenderAt D.sourceOrbit T g ∧
      ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
        let Z := ⁅offenderNormalizer D.sourceOrbit g,offenderFixedSpan D.sourceOrbit g⁆
        Nat.card Z = 2 ∧ (Z ≤ V ∨ Z ≤ V.map (MulAut.conj t).toMonoidHom) ∧
        Z ≤ D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ∧
        D.sourceOrbit ⊔ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (Z : Set G) ∧
        (∃ P : Sylow 2 (centralizer (Z : Set G)),
          (P : Subgroup _).map (centralizer (Z : Set G)).subtype =
            (T : Subgroup G) ⊓ centralizer (Z : Set G)) ∧
        ¬ HasCharacteristicTwo (centralizer (Z : Set G)) := by
  obtain ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,⟨P,hP⟩,_,_⟩ :=
    D.sourceOrbit_binary_exists_sylow_pureLine_core_obstruction h hd F hF hmodel hnon hw
  refine ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,⟨P,hP⟩,?_⟩
  exact D.sourceOrbit_binary_false_of_pureLine_characteristicTwo h hd F hF hmodel hnon hw hg
    t ht hnt _ hZ hpure (hpair.trans inf_le_left) (hpair.trans inf_le_right) P hP

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

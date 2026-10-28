module
public import Stellmacher.SectionTwo.BaumannOmegaSupplementData
public import Stellmacher.SectionTwo.BaumannOmegaQuotientSupplement
public import Stellmacher.SectionTwo.BaumannOmegaActionFactors
public import Stellmacher.SectionTwo.TwoFourGeneratingCoordinate

/-!
# A generating coordinate on the Baumann omega module

Under the native local hypotheses of (2.4), form the Baumann subgroup B,
its normal closure L, and the normal closure Z of Ω₁(Z(B)). For any exact
centralizer quotient of Z, this theorem selects a local subgroup K with
Sylow image B and nested Frattini quotient SL₂(2), generating with S.
It retains the complete raw factor family inside the image of L and the
selected coordinate's exact quotient image, on the unchanged module Z.

The normal-supplement construction identifies Z with the native module
of a Sylow subgroup of L. Its quotient transport supplies trivial two-core
and the exact nontrivial Sylow intersection. The rich offender recognition
then gives one-seven factors on Z. Mapping that family into the ambient
quotient allows the generating-coordinate Frattini-lift theorem to select K.
The returned image includes the selected factor and the Sylow lines in the
other coordinates; it does not assert that the entire image is SL₂(2).

Source: Stellmacher (2.2)--(2.4), Journal of Algebra 190 (1997), p20,
applied to the actual modules Zi in the opening of (6.3), p31.
-/

namespace Stellmacher.SectionTwo
universe u

public theorem baumann_omega_selected_coordinate
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    (hcore : pCore 2 G = (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G))
    (hnot : ¬ vSubgroup S ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G))
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G))
    (B L Z : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (hL : L = Subgroup.normalClosure (B : Set G))
    (hZ : Z = Subgroup.normalClosure (omegaOneCenterAmbient B : Set G))
    {X : Type u} [Group X] [Finite X] (q : G →* X) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (Z : Set G)) :
    letI := centralizerQuotientAction Z (hZ ▸ Subgroup.normalClosure_normal) q hq hker
    IsElementaryAbelian 2 Z ∧ Z ≤ B ∧
    B.map q = ((S.mapSurjective hq : Sylow 2 X) : Subgroup X) ⊓ L.map q ∧
    ∃ (n : ℕ) (D : Fin n → Subgroup (L.map q))
      (K : Subgroup G) (PK : Sylow 2 K) (i : Fin n),
      IsInternalDirectProductFamily ⊤ D ∧ Function.Injective D ∧
      (∀ j, SectionOne.IsOneSevenFactor (V := Z) (D j)) ∧
      (∀ j, (D j).Normal) ∧
      IsInternalDirectProductFamily (⊤ : Subgroup Z)
        (fun j : Option (Fin n) => match j with
          | none => FixedPoints.subgroup (⊤ : Subgroup (L.map q)) Z
          | some j => commutatorAction (D j) Z) ∧
      B ≤ K ∧ K ≤ L ∧ (PK : Subgroup K).map K.subtype = B ∧
      IsSL2Two ((K ⧸ pCore 2 K) ⧸ frattini (K ⧸ pCore 2 K)) ∧
      K ⊔ (S : Subgroup G) = ⊤ ∧
      K.map q = (D i).map (L.map q).subtype ⊔
        ⨆ j : {j : Fin n // j ≠ i},
          ((S.mapSurjective hq : Sylow 2 X) : Subgroup X) ⊓
            (D j).map (L.map q).subtype := by
  classical
  subst L
  subst Z
  subst B
  let B := (S : Subgroup G) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
  let L := Subgroup.normalClosure (B : Set G)
  let Z := Subgroup.normalClosure (omegaOneCenterAmbient B : Set G)
  let _ := centralizerQuotientAction Z Subgroup.normalClosure_normal q hq hker
  obtain ⟨PB, hPB, hsecL, hgenL, hNgen, hPBself, hVeq, _hVZ, hZB, hnotL⟩ :=
    baumann_omega_supplement_data h S hcore hnot hunique
  change (PB : Subgroup L).map L.subtype = B at hPB
  change (vSubgroup PB).map L.subtype = Z at hVeq
  change (vSubgroup PB).map L.subtype ≤ B at hZB
  have hZe : IsElementaryAbelian 2 Z := by
    rw [← hVeq]
    let _ : IsElementaryAbelian 2 (vSubgroup PB) :=
      (vSubgroup_le_twoCore_and_elementaryAbelian hsecL PB).2
    exact IsElementaryAbelian.map L.subtype
  let _ : IsElementaryAbelian 2 Z := hZe
  have hZB' : Z ≤ B := hVeq ▸ hZB
  have hself : B ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ B) : Set G) = B :=
    baumann_eq_of_intermediate (S : Subgroup G) B le_rfl inf_le_left
  obtain ⟨hbarCore, hBinf, hBne⟩ := baumann_omega_quotient_supplement S L B Z PB
    hsecL hPB inf_le_left hVeq hnotL q hq hker
  obtain ⟨_hJ, n, D, hprod, hDin, hDF, hDn, hmod⟩ :=
    baumann_omega_action_factors Z Subgroup.normalClosure_normal q hq hker L PB
      hsecL.solvable hNgen (hPB ▸ hZB') (hPB ▸ hself) hbarCore
  let E (i : Fin n) : Subgroup X := (D i).map (L.map q).subtype
  have hprodE : IsInternalDirectProductFamily (L.map q) E := by
    have hp := hprod.map_injective (L.map q).subtype (L.map q).subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hp
    exact hp
  have hSL (i : Fin n) : IsSL2Two (E i) := by
    obtain ⟨e⟩ := (hDF i).1
    exact ⟨(Subgroup.equivMapOfInjective (D i) (L.map q).subtype
      (L.map q).subtype_injective).symm.trans e⟩
  let _ : L.Normal := Subgroup.normalClosure_normal
  have hLn : (L.map q).Normal := Subgroup.Normal.map inferInstance q hq
  obtain ⟨K, PK, i, hBK, hKL, hPK, hA, hgen, himage⟩ :=
    exists_generating_coordinate_frattini_lift_with_image h.solvable S (S.mapSurjective hq)
      q hq (B.map q) (L.map q) B L PB hPB rfl hBinf hBne rfl hgenL
        hunique hLn E hprodE hSL
  exact ⟨hZe, hZB', hBinf, n, D, K, PK, i, hprod, hDin, hDF, hDn, hmod,
    hBK, hKL, hPK, hA, hgen, himage⟩

end Stellmacher.SectionTwo

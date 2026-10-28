module
public import Stellmacher.SectionTwo.BaumannOmegaSelectedCoordinate
public import Stellmacher.SectionTwo.OmegaCoordinateModule
public import Stellmacher.SectionTwo.SelectedCoordinateImageResidual

/-!
# The selected Baumann omega module with its factor family

Under the native Section Two hypotheses, select a generating coordinate
on the original normal closure Z of Omega_1(Z(B)), where B is the Baumann
subgroup and L its normal closure. The selected K retains Sylow image B
and its nested SL2(2) Frattini quotient. Its actual omega/residual and
Z/residual commutators coincide, have order four, and are normalized by L.
The fixed subgroup of K in Omega_1(Z(B)) has relative index two.

The rich coordinate selection preserves the complete raw factor family,
its indexing and exact action on Z. The selected-coordinate image theorem
computes both K's quotient image and its two-residual image. Restricting
the ambient quotient Sylow to the normal image of L gives the precise
Sylow needed for the omega-coordinate calculation. That calculation
supplies the literal ambient module and fixed-index assertions.

Source: Stellmacher (2.2)--(2.4), applied in the opening paragraph of (6.3),
Journal of Algebra 190 (1997), pp.20 and31,
refs/latex/stellmacher-n-group.tex. The full original family is retained
for the later conjugate-factor argument; no replacement of Z by V(S)
or assumption on the full core/residual commutator occurs.
-/

namespace Stellmacher.SectionTwo
universe u

public theorem baumann_omega_selected_module
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
      K.map q = (D i).map (L.map q).subtype ⊔ B.map q ∧
      (twoResidualAmbient K).map q =
        ((commutator (D i)).map (D i).subtype).map (L.map q).subtype ∧
      ⁅omegaOneCenterAmbient B, twoResidualAmbient K⁆ = ⁅Z, twoResidualAmbient K⁆ ∧
      Nat.card (⁅Z, twoResidualAmbient K⁆ : Subgroup G) = 4 ∧
      L ≤ Subgroup.normalizer ((⁅Z, twoResidualAmbient K⁆ : Subgroup G) : Set G) ∧
      (omegaOneCenterAmbient B ⊓ Subgroup.centralizer (K : Set G)).relIndex
        (omegaOneCenterAmbient B) = 2 := by
  classical
  let _ := centralizerQuotientAction Z (hZ ▸ Subgroup.normalClosure_normal) q hq hker
  obtain ⟨hZe, hZB, hBinf, n, D, K, PK, i, hprod, hDin, hDF, hDn, hmod,
      hBK, hKL, hPK, hA, hgen, hKi⟩ :=
    baumann_omega_selected_coordinate h S hcore hnot hunique B L Z hB hL hZ q hq hker
  let _ : IsElementaryAbelian 2 Z := hZe
  let _ : L.Normal := hL ▸ Subgroup.normalClosure_normal
  let _ : (L.map q).Normal := Subgroup.Normal.map inferInstance q hq
  let _ : (D i).Normal := hDn i
  let T := S.mapSurjective hq
  obtain ⟨TE, hTE⟩ := T.exists_subgroupOf_eq_of_normal (L.map q)
  have hTmap : (TE : Subgroup (L.map q)).map (L.map q).subtype = B.map q := by
    rw [hTE]
    change Subgroup.map (L.map q).subtype (Subgroup.comap (L.map q).subtype (T : Subgroup X)) = _
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
    exact hBinf.symm
  have hAV : omegaOneCenterAmbient B ≤ Z := by
    rw [hZ]
    exact Subgroup.le_normalClosure
  obtain ⟨hKiB, hRi⟩ := selected_coordinate_image_and_residual q T (L.map q)
    inferInstance D hprod (fun j => (hDF j).1) B K i hBinf hKi
  obtain ⟨hcomm, hcard, hnorm, hindex⟩ := omega_coordinate_module Z B
    (hZ ▸ Subgroup.normalClosure_normal) hZB hAV q hq hker (L.map q) TE hTmap
      (D i) K hKiB hRi (hDF i)
  have hLnorm : L ≤ Subgroup.normalizer ((⁅Z, twoResidualAmbient K⁆ : Subgroup G) : Set G) := by
    exact (Subgroup.le_comap_map q L).trans hnorm
  exact ⟨hZe, hZB, hBinf, n, D, K, PK, i, hprod, hDin, hDF, hDn, hmod,
    hBK, hKL, hPK, hA, hgen, hKiB, hRi, hcomm, hcard, hLnorm, hindex⟩

end Stellmacher.SectionTwo


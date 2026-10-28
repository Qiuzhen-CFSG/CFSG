module

public import Stellmacher.SectionsOneToFourDefs


/-!
# Stellmacher (2.1): the quotient has trivial 2-core

Under the standing hypotheses of Section 2, let `S` be a Sylow 2-subgroup of
`G`, let `V` be the normal closure of `Ω₁(Z(S))`, and present `G / C_G(V)` by a
surjective homomorphism `q` with kernel `cSubgroup S`.  Result (2.1), at
`refs/latex/stellmacher-n-group.tex`, lines 548--564, states that the quotient
has trivial 2-core.

The proof pulls the quotient 2-core back to `G`.  Its image lies in the mapped
Sylow subgroup, so the pullback lies in `ker q ⊔ S` and centralizes
`Ω₁(Z(S))`.  Normality extends this centralization to `V`, forcing the pullback
into `C_G(V) = ker q`; surjectivity then makes the quotient 2-core trivial.
-/

namespace Stellmacher.SectionTwo

universe u

public structure Hypotheses
    (G : Type u) [Group G] [Finite G] : Prop where
  solvable : Group.IsSolvable G
  even_order : Even (Nat.card G)
  centralizer_twoCore_le :
    Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G

set_option linter.unusedVariables false in
/-- **Stellmacher (2.1).**  `\bar G=G/C_G(V)` has trivial `2`-core.  The
surjective-kernel presentation keeps the quotient explicit without relying on
a global normality instance for the notation `C_G(V)`. -/
public theorem lemma_two_one
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q)
    (hker : q.ker = cSubgroup S) :
    pCore 2 barG = ⊥ := by
  let Q : Subgroup barG := pCore 2 barG
  let R : Subgroup G := Q.comap q
  let barS : Sylow 2 barG := S.mapSurjective hq
  have hQ_le_barS : Q ≤ (barS : Subgroup barG) := by
    exact fitting_pCore_le_sylow barS
  have hR_le : R ≤ q.ker ⊔ (S : Subgroup G) := by
    intro r hr
    have hqrQ : q r ∈ Q := hr
    have hqrbarS : q r ∈ (barS : Subgroup barG) := hQ_le_barS hqrQ
    have hqrmap : q r ∈ (S : Subgroup G).map q := by
      simpa [barS] using hqrbarS
    rw [Subgroup.mem_map] at hqrmap
    obtain ⟨s, hsS, hqs⟩ := hqrmap
    have hk : r * s⁻¹ ∈ q.ker := by
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_inv, hqs]
      simp
    have hk_sup : r * s⁻¹ ∈ q.ker ⊔ (S : Subgroup G) :=
      (le_sup_left : q.ker ≤ q.ker ⊔ (S : Subgroup G)) hk
    have hs_sup : s ∈ q.ker ⊔ (S : Subgroup G) :=
      (le_sup_right : (S : Subgroup G) ≤ q.ker ⊔ (S : Subgroup G)) hsS
    have hrs := (q.ker ⊔ (S : Subgroup G)).mul_mem hk_sup hs_sup
    simpa [mul_assoc] using hrs
  have hz_le_v : zSubgroup S ≤ vSubgroup S := by
    exact Subgroup.le_normalClosure
  have hker_le_cent_z : q.ker ≤ Subgroup.centralizer (zSubgroup S : Set G) := by
    rw [hker, cSubgroup]
    exact Subgroup.centralizer_le hz_le_v
  have hS_le_cent_z : (S : Subgroup G) ≤ Subgroup.centralizer (zSubgroup S : Set G) := by
    intro s hsS
    rw [Subgroup.mem_centralizer_iff]
    intro z hzZ
    simp only [zSubgroup, omegaOneCenterAmbient] at hzZ
    obtain ⟨zS, hzS, rfl⟩ := Subgroup.mem_map.mp hzZ
    obtain ⟨zC, _hzOmega, rfl⟩ := Subgroup.mem_map.mp hzS
    have hzcomm := (Subgroup.mem_center_iff.mp zC.property) ⟨s, hsS⟩
    simpa using congrArg (fun x : S => (x : G)) hzcomm.symm
  have hR_le_cent_z : R ≤ Subgroup.centralizer (zSubgroup S : Set G) :=
    hR_le.trans (sup_le hker_le_cent_z hS_le_cent_z)
  have hz_le_cent_R : zSubgroup S ≤ Subgroup.centralizer (R : Set G) :=
    Subgroup.le_centralizer_iff.mp hR_le_cent_z
  have hv_le_cent_R : vSubgroup S ≤ Subgroup.centralizer (R : Set G) := by
    exact Subgroup.normalClosure_le_normal hz_le_cent_R
  have hR_le_ker : R ≤ q.ker := by
    rw [hker, cSubgroup]
    exact Subgroup.le_centralizer_iff.mp hv_le_cent_R
  apply le_antisymm ?_ bot_le
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨x, rfl⟩ := hq y
  exact MonoidHom.mem_ker.mp (hR_le_ker hy)

end Stellmacher.SectionTwo

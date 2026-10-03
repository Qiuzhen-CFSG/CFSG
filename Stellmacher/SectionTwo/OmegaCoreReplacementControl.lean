module

public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# Omega-center control from maximal elementary replacements

Suppose `V ≤ Q ≤ S`, with `V` normal elementary abelian and
centralized by `Q`, and every replacement `V C_A(V)` of a
maximal-order elementary abelian subgroup `A` of `S` is again
maximal and lies in `Q`. Put `Z=Ω₁(Z(J(S)))` and
`Z₀=Ω₁(Z(J(Q)))`. Then `Z,V ≤ Z₀` and
`Z₀ ≤ C_Z₀(A)V` for every such `A`.

A maximal elementary subgroup contains each elementary subgroup of `S`
that centralizes it. One replacement inside `Q` compares the maximal
families and gives `J(Q)≤J(S)` and `Z≤Q`; the fixed-center theorem
then gives both first containments. Every replacement lies in `J(Q)`,
so is centralized by `Z₀`. Maximality puts `Z₀` in that replacement,
and product decomposition with `V≤Z₀` gives the final bound.

These are the omega-center assertions after the maximal replacement in the
noncentralizing case of Stellmacher (2.3), journal p.20. The source application
takes `Q=O₂(⟨J(S)^G⟩)`; the explicit replacement hypotheses isolate this
finite-group step from the later factor/module construction.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (2.3).
-/

namespace Stellmacher.SectionTwo

private theorem elementary_centralizer_le_maximal
    {G : Type*} [Group G] [Finite G] (S A W : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) [IsElementaryAbelian 2 W]
    (hWS : W ≤ S) (hWA : W ≤ Subgroup.centralizer (A : Set G)) : W ≤ A := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  have hsup : IsElementaryAbelian 2 (A ⊔ W : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hWA
  have heq : A = A ⊔ W := Subgroup.eq_of_le_of_card_ge le_sup_left
    (hA.2.2 (A ⊔ W) (sup_le hA.1 hWS) hsup)
  exact heq ▸ le_sup_right

private theorem omegaCenter_le_centralizer
    {G : Type*} [Group G] (Q : Subgroup G) :
    omegaOneCenterAmbient Q ≤ Subgroup.centralizer (Q : Set G) := by
  intro z hz
  exact Subgroup.mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff Q z).mp hz).2.2

/-- Maximal elementary replacements control the smaller core's Thompson omega-center. -/
public theorem omega_core_replacement_control
    {G : Type*} [Group G] [Finite G] (S Q V : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V]
    (hVQ : V ≤ Q) (hQS : Q ≤ S)
    (hQV : Q ≤ Subgroup.centralizer (V : Set G))
    (hreplace : ∀ A ∈ elementaryAbelianMaxSubgroups S,
      (V ⊔ (A ⊓ Subgroup.centralizer (V : Set G))) ∈ elementaryAbelianMaxSubgroups S ∧
      V ⊔ (A ⊓ Subgroup.centralizer (V : Set G)) ≤ Q) :
    let Z := omegaOneCenterAmbient (elementaryAbelianMaxJ S)
    let Z0 := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
    Z ≤ Z0 ∧ V ≤ Z0 ∧ ∀ A ∈ elementaryAbelianMaxSubgroups S,
      Z0 ≤ (Z0 ⊓ Subgroup.centralizer (A : Set G)) ⊔ V := by
  let Z := omegaOneCenterAmbient (elementaryAbelianMaxJ S)
  let Z0 := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
  let _ : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian _
  let _ : IsElementaryAbelian 2 Z0 := omegaOneCenterAmbient_elementaryAbelian _
  have hJS : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA ↦ hA.1
  have hJQ : elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA ↦ hA.1
  have hZS : Z ≤ S := (Subgroup.map_subtype_le _).trans hJS
  have hZ0Q : Z0 ≤ Q := (Subgroup.map_subtype_le _).trans hJQ
  obtain ⟨A0, hA0⟩ := elementaryAbelianMaxSubgroups_nonempty S
  let K0 := V ⊔ (A0 ⊓ Subgroup.centralizer (V : Set G))
  obtain ⟨hK0, hK0Q⟩ := hreplace A0 hA0
  have hJQJS : elementaryAbelianMaxJ Q ≤ elementaryAbelianMaxJ S := by
    apply sSup_le
    intro D hD
    apply le_sSup
    refine ⟨hD.1.trans hQS, hD.2.1, ?_⟩
    intro B hBS hBe
    exact (hK0.2.2 B hBS hBe).trans (hD.2.2 K0 hK0Q hK0.2.1)
  have hZQ : Z ≤ Q := by
    have hZK0 : Z ≤ K0 := elementary_centralizer_le_maximal S K0 Z hK0 hZS
      ((omegaCenter_le_centralizer _).trans (Subgroup.centralizer_le (le_sSup hK0)))
    exact hZK0.trans hK0Q
  have hZZ0 : Z ≤ Z0 := elementary_centralizer_maxJ_le_omegaCenter Q Z hZQ
    ((omegaCenter_le_centralizer _).trans (Subgroup.centralizer_le hJQJS))
  have hVZ0 : V ≤ Z0 := elementary_centralizer_maxJ_le_omegaCenter Q V hVQ
    ((Subgroup.le_centralizer_iff.mp hQV).trans (Subgroup.centralizer_le hJQ))
  refine ⟨hZZ0, hVZ0, ?_⟩
  intro A hA
  let K := V ⊔ (A ⊓ Subgroup.centralizer (V : Set G))
  obtain ⟨hK, hKQ⟩ := hreplace A hA
  have hKmaxQ : K ∈ elementaryAbelianMaxSubgroups Q :=
    ⟨hKQ, hK.2.1, fun D hDQ hDe ↦ hK.2.2 D (hDQ.trans hQS) hDe⟩
  have hZ0K : Z0 ≤ K := elementary_centralizer_le_maximal S K Z0 hK (hZ0Q.trans hQS)
    ((omegaCenter_le_centralizer _).trans (Subgroup.centralizer_le (le_sSup hKmaxQ)))
  intro z hz
  obtain ⟨v, hv, a, ha, hza⟩ := Subgroup.mem_sup_of_normal_left.mp (hZ0K hz)
  have haZ0 : a ∈ Z0 := by
    have hh := Z0.mul_mem (Z0.inv_mem (hVZ0 hv)) hz
    rw [← hza] at hh
    simpa [mul_assoc] using hh
  let _ : IsElementaryAbelian 2 A := hA.2.1
  have haC : a ∈ Subgroup.centralizer (A : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance :
      A ≤ Subgroup.centralizer (A : Set G)) ha.1
  rw [← hza]
  exact ((Z0 ⊓ Subgroup.centralizer (A : Set G)) ⊔ V).mul_mem
    ((le_sup_right : V ≤ (Z0 ⊓ Subgroup.centralizer (A : Set G)) ⊔ V) hv)
    ((le_sup_left : Z0 ⊓ Subgroup.centralizer (A : Set G) ≤
      (Z0 ⊓ Subgroup.centralizer (A : Set G)) ⊔ V) ⟨haZ0, haC⟩)

end Stellmacher.SectionTwo

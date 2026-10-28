module

public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# Thompson noncontainment at the endpoint of Stellmacher (5.2)

This module derives the native noncontainment `J(S) ≰ C₀` used immediately
before the quotient application of Stellmacher (2.2).  Here `V` is the normal
elementary abelian two-subgroup in the source minimal bad subgroup,
`C₀ = C_G(V)`, and `B = C_S(Ω₁(Z(J(S))))` is the corresponding Baumann
subgroup.  Assertion (7) supplies that the ambient image of `O₂(K)` is not
contained in `C₀`.

If `J(S) ≤ C₀`, then it centralizes `V`.  The maximal-elementary-subgroup
calculation puts `V` in `Ω₁(Z(J(S)))`, so `B` centralizes `V` and lies in
`C₀`.  Since `C₀` is normal, the full commutator equality `[K,B] = K` forces
all of `K` into `C₀`, and therefore also the ambient image of `O₂(K)`.  This
contradicts assertion (7).  In particular, the proof does not assume the false
intermediate containment `O₂(K) ≤ J(S)` or `O₂(K) ≤ B(S)`.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of Lemma (5.2),
p. 29, the scan-correct unbarred assertion `J(T₀) ≰ C₀`; see
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionsFiveToSeven

universe u

/-- Assertion (7), together with `[K,B(S)] = K`, forces the elementary
Thompson subgroup of `S` outside the centralizer of `V`. -/
public theorem five_two_thompson_not_le_centralizer
    {G : Type u} [Group G] [Finite G]
    (S V C0 B K : Subgroup G)
    [V.Normal] (hVelem : IsElementaryAbelian 2 V)
    (hVS : V ≤ S)
    (hC0 : C0 = Subgroup.centralizer (V : Set G))
    [C0.Normal]
    (hB : B = S ⊓ Subgroup.centralizer
      (Stellmacher.omegaOneCenterAmbient
        (Stellmacher.elementaryAbelianMaxJ S) : Set G))
    (hcoreNot : ¬ twoCoreIn K ≤ C0)
    (hcomm : ⁅K, B⁆ = K) :
    ¬ Stellmacher.elementaryAbelianMaxJ S ≤ C0 := by
  intro hJle
  have hJcentralV : Stellmacher.elementaryAbelianMaxJ S ≤
      Subgroup.centralizer (V : Set G) := by
    rwa [← hC0]
  let _ : IsElementaryAbelian 2 V := hVelem
  have hVcentralJ : V ≤ Subgroup.centralizer
      (Stellmacher.elementaryAbelianMaxJ S : Set G) :=
    Subgroup.le_centralizer_iff.mp hJcentralV
  have hVomega : V ≤ Stellmacher.omegaOneCenterAmbient
      (Stellmacher.elementaryAbelianMaxJ S) :=
    Stellmacher.elementary_centralizer_maxJ_le_omegaCenter S V hVS hVcentralJ
  have hBle : B ≤ C0 := by
    rw [hB, hC0]
    exact inf_le_right.trans (Subgroup.centralizer_le hVomega)
  have hKle : K ≤ C0 := by
    calc
      K = ⁅K, B⁆ := hcomm.symm
      _ ≤ ⁅K, C0⁆ := Subgroup.commutator_mono le_rfl hBle
      _ ≤ C0 := Subgroup.commutator_le_right K C0
  exact hcoreNot ((Subgroup.map_subtype_le (pCore 2 K)).trans hKle)

end Stellmacher.SectionsFiveToSeven

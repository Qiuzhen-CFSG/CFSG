module

public import Stellmacher.ElementaryAbelianMaxJ
public import BenderSuzuki.External.Huppert.IV.Basic

/-!
# Normalizer preservation of the Baumann subgroup

Every element normalizing `Q` normalizes its Baumann subgroup
`Q ∩ C_G(Ω₁(Z(J(Q))))`, with `J` the elementary Thompson subgroup.
This gives the normality of `B₀` in `P` and its normalization by `C` in
Stellmacher (4.6), by taking `Q = O₂(C)`.

The proof transports `J(Q)` through conjugation, uses the characteristic
omega subgroup of its characteristic center, and then uses normality of a
centralizer inside the normalizer of the centralized subgroup. Intersecting
with `Q` preserves normalization. No finiteness hypothesis is needed.

Source: `refs/latex/stellmacher-n-group.tex`, proof of (4.6), the assertions
about the normalizers of `B₀`.
-/

namespace Stellmacher

universe u

private theorem normalizer_le_normalizer_omegaOneCenterAmbient
    {G : Type u} [Group G] (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (omegaOneCenterAmbient Q : Set G) := by
  let K : Subgroup Q :=
    (omega₁ (G := Subgroup.center Q) (p := 2)).map (Subgroup.center Q).subtype
  let _ : (omega₁ (G := Subgroup.center Q) (p := 2)).Characteristic :=
    omega₁_characteristic (Subgroup.center Q)
  have hK : K.Characteristic := inferInstance
  let _ : K.Characteristic := hK
  exact BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic Q K

/-- Normalizing a subgroup normalizes its elementary Baumann subgroup. -/
public theorem normalizer_le_normalizer_baumann
    {G : Type u} [Group G] (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer
        ((Q ⊓ Subgroup.centralizer
          (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) : Subgroup G) : Set G) := by
  have hJ : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (elementaryAbelianMaxJ Q : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
    change Q.map (MulAut.conj x).toMonoidHom = Q at hx
    change (elementaryAbelianMaxJ Q).map (MulAut.conj x).toMonoidHom = _
    rw [← elementaryAbelianMaxJ_map_equiv (MulAut.conj x) Q, hx]
  let W : Subgroup G := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
  have hW : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (W : Set G) :=
    hJ.trans (normalizer_le_normalizer_omegaOneCenterAmbient _)
  have hC : Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (W : Set G))).mp inferInstance
  exact (le_inf le_rfl (hW.trans hC)).trans Subgroup.inf_normalizer_le_normalizer_inf

end Stellmacher

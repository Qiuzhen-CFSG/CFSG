module

public import CFSG.Quasithin.ChapterD.Section01.Configuration
public import Theory.GroupTheory.PResidual.NormalSylowCommutator

/-!
# The original Sylow consequence of the qrc configuration

In the original D.1.1 configuration, R=O₂(G₁) lies in the shared Sylow
subgroup and hence in G₂. Transport the residual commutator theorem through
the actual inclusion G₂ → G to obtain R ∈ Syl₂(O²(G₂)R).

The explicit earlier inputs are the odd order of O²(G₂/O₂(G₂)) from the
solvable case of B.6.8(2), and [O₂(G₂),O²(G₂)] ≤ R proved in D.1.4's
unique-factor argument. Their source owners must discharge both inputs.
The later A₃-block/Baumann addendum is not needed for this consequence.
All subgroups, quotient maps and the ambient inclusion remain literal.

Source: Aschbacher–Smith, D.1.4, printed p.176, and its Sylow application
in 15.4.2(4), printed pp.1155–1156, refs/quasithin.pdf.
-/

noncomputable section
namespace CFSG.Quasithin.ChapterD
open Subgroup
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}

private theorem QRCConfiguration.left_core_le_right
    (d : QRCConfiguration G₁ G₂ T V) : twoCoreIn G₁ ≤ G₂ := by
  let := d.finite_left
  obtain ⟨S₁, h₁⟩ := d.sylow_left
  obtain ⟨S₂, h₂⟩ := d.sylow_right
  have hRT : twoCoreIn G₁ ≤ T := by
    rw [← h₁]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal S₁)
  exact hRT.trans (h₂ ▸ map_subtype_le (S₂ : Subgroup G₂))

/-- The Sylow conclusion used in the solvable branch of D.1.4 and E15.4.2(4).
The two earlier inputs are the odd residual above O₂(G₂) from B.6.8(2)
and the literal core-commutator containment from the unique-factor argument. -/
public theorem QRCConfiguration.exists_sylow_residual_sup_of_core_commutator
    (d : QRCConfiguration G₁ G₂ T V)
    (hodd : Odd (Nat.card (pResidual 2 (G₂ ⧸ pCore 2 G₂))))
    (hc : ⁅twoCoreIn G₂, (pResidual 2 G₂).map G₂.subtype⁆ ≤ twoCoreIn G₁) :
    let H := (pResidual 2 G₂).map G₂.subtype ⊔ twoCoreIn G₁
    ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = twoCoreIn G₁ := by
  let := d.finite_left
  let := d.finite_right
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let R : Subgroup G₂ := (twoCoreIn G₁).subgroupOf G₂
  let L : Subgroup G₂ := pResidual 2 G₂ ⊔ R
  let H : Subgroup G := (pResidual 2 G₂).map G₂.subtype ⊔ twoCoreIn G₁
  have hR : IsPGroup 2 R :=
    (pCore_isPGroup (p := 2) (G := G₁)).map G₁.subtype |>.comap_subtype
  have hcomm : ⁅pCore 2 G₂, pResidual 2 G₂⁆ ≤ R := by
    intro x hx
    change (x : G) ∈ twoCoreIn G₁
    apply hc
    have hh := mem_map_of_mem G₂.subtype hx
    rw [map_commutator] at hh
    exact hh
  obtain ⟨S, hS⟩ := Subgroup.exists_sylow_residual_sup_of_core_commutator R hR
    (Nat.coprime_two_left.mpr hodd) hcomm
  have himage : L.map G₂.subtype = H := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le d.left_core_le_right]
  let e : L ≃* H := (L.equivMapOfInjective G₂.subtype G₂.subtype_injective).trans
    (MulEquiv.subgroupCongr himage)
  have hcomp : H.subtype.comp e.toMonoidHom = G₂.subtype.comp L.subtype := by
    ext x
    rfl
  let S' : Sylow 2 H := S.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨S', ?_⟩
  change ((S : Subgroup L).map e.toMonoidHom).map H.subtype = twoCoreIn G₁
  rw [map_map, hcomp, ← map_map, hS, map_subgroupOf_eq_of_le d.left_core_le_right]

end CFSG.Quasithin.ChapterD

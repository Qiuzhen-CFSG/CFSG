module
public import Stellmacher.TwoResidualFixedCentralizer

/-!
# Detecting a residual action modulo a normal subgroup

Let `E` and a two-subgroup `Q` normalize `V`, with `⁅Q, E⁆ ≤ V`.
For a normal subgroup `Z`, suppose the image of `V` in `G ⧸ Z` is
an elementary abelian two-group. If the two-residual of `E` centralizes,
modulo `Z`, the elements of `V` fixed by `Q` modulo `Z`, it centralizes
all of `V` modulo `Z`.

The lifted fixed subgroup is the intersection of `V` with the preimage
of the centralizer of the image of `Q`. Its image is exactly the
Q-fixed subgroup of the image of `V`. Normalization and commutators
pass to the quotient; the image of `⁅Q, E⁆` centralizes the elementary
image of `V`. Residual functoriality and
`twoResidual_centralizes_of_commuting_fixed` then give a trivial quotient
commutator, which lifts to containment in `Z`.

This is the central-quotient action transfer used before the seed
construction in Stellmacher (9.1), relation (3),
`refs/latex/stellmacher-n-group.tex`. Only normality of `Z` is required
for the general adapter; the application has a central kernel.
-/

namespace Stellmacher

/-- Fixed points modulo a normal subgroup detect the residual action on an
elementary abelian quotient image. -/
public theorem twoResidual_commutator_le_of_commuting_fixed_modulo
    {G : Type*} [Group G] [Finite G] (E Q V Z : Subgroup G) [Z.Normal]
    [IsElementaryAbelian 2 (V.map (QuotientGroup.mk' Z))]
    (hQ : IsPGroup 2 Q)
    (hEN : E ≤ Subgroup.normalizer (V : Set G))
    (hQN : Q ≤ Subgroup.normalizer (V : Set G))
    (hcomm : ⁅Q, E⁆ ≤ V)
    (hfix : ⁅V ⊓ (Subgroup.centralizer
        ((Q.map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) : Set (G ⧸ Z))).comap
          (QuotientGroup.mk' Z), twoResidualAmbient E⁆ ≤ Z) :
    ⁅V, twoResidualAmbient E⁆ ≤ Z := by
  let q := QuotientGroup.mk' Z
  let Ebar := E.map q
  let Qbar := Q.map q
  let Vbar := V.map q
  let F := V ⊓ (Subgroup.centralizer (Qbar : Set (G ⧸ Z))).comap q
  have hEbarN : Ebar ≤ Subgroup.normalizer (Vbar : Set (G ⧸ Z)) :=
    (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map q)
  have hQbarN : Qbar ≤ Subgroup.normalizer (Vbar : Set (G ⧸ Z)) :=
    (Subgroup.map_mono hQN).trans (Subgroup.le_normalizer_map q)
  have hcommbar : ⁅Qbar, Ebar⁆ ≤ Subgroup.centralizer (Vbar : Set (G ⧸ Z)) := by
    have h : ⁅Qbar, Ebar⁆ ≤ Vbar := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.map_mono hcomm
    exact h.trans Vbar.le_centralizer
  have hFmap : F.map q = Vbar ⊓ Subgroup.centralizer (Qbar : Set (G ⧸ Z)) := by
    apply le_antisymm
    · rintro x ⟨v, hv, rfl⟩
      exact ⟨Subgroup.mem_map_of_mem q hv.1, hv.2⟩
    · rintro x ⟨⟨v, hv, rfl⟩, hc⟩
      exact ⟨v, ⟨hv, hc⟩, rfl⟩
  have hRmap : (twoResidualAmbient E).map q = twoResidualAmbient Ebar :=
    map_twoResidualAmbient_of_subgroup_image E q Ebar rfl
  have hfixbar : ⁅Vbar ⊓ Subgroup.centralizer (Qbar : Set (G ⧸ Z)),
      twoResidualAmbient Ebar⁆ = ⊥ := by
    rw [← hFmap, ← hRmap, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    simpa only [q, QuotientGroup.ker_mk'] using hfix
  have hresult := twoResidual_centralizes_of_commuting_fixed Ebar Qbar Vbar
    (hQ.map q) hEbarN hQbarN hcommbar hfixbar
  rw [← hRmap, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff] at hresult
  simpa only [q, QuotientGroup.ker_mk'] using hresult
end Stellmacher

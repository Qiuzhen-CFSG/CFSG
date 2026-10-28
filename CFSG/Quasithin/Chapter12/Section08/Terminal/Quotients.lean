module

public import CFSG.Quasithin.Chapter12.Section08.SourceGeometry
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The literal dotted quotient and the conjugate center

Conjugation by H acts on U/Z(U). The dotted group is H divided by the
kernel of this action, and dotted subgroups are images under its quotient
map. Restricting this map after right conjugation identifies the image of
Z(U)^g with Z(U)/V₁ when the restricted kernel is V₁^g.

The input kernel identity is the specialization of 12.8.10(6) after the
center calculation in 12.8.13(3). These constructions retain the actual
element map; they do not replace the quotient with an abstract group tag.
The action is determined by its evaluation on the original quotient, so
it can be compared directly with the preliminary branch's action API.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.13(3), printed pp.855–856.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

@[expose] public def terminalHatAction (F : InvariantFlag T V n) : F.H →* MulAut F.Uhat :=
  (quotientAut (center F.U)).comp
    (F.U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy V F.H)))

public abbrev TerminalHdot (F : InvariantFlag T V n) := F.H ⧸ F.terminalHatAction.ker

@[expose] public def terminalDot (F : InvariantFlag T V n) (A : Subgroup G) : Subgroup F.TerminalHdot :=
  (A.subgroupOf F.H).map (QuotientGroup.mk' F.terminalHatAction.ker)

public instance terminalZU_commutative (F : InvariantFlag T V n) : IsMulCommutative F.ZU :=
  map_isMulCommutative (center F.U) F.U.subtype

public noncomputable def terminalConjugateCenterEquiv (F : InvariantFlag T V n)
    (g : G) (hGH : conjugate F.ZU g ≤ F.H) :
    F.ZU ≃* (conjugate F.ZU g).subgroupOf F.H :=
  ((MulAut.conj g⁻¹).subgroupMap F.ZU).trans (subgroupOfEquivOfLe hGH).symm

public noncomputable def terminalCenterImageMap (F : InvariantFlag T V n)
    (g : G) (hGH : conjugate F.ZU g ≤ F.H) :
    F.ZU →* F.terminalDot (conjugate F.ZU g) :=
  ((QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap
    ((conjugate F.ZU g).subgroupOf F.H)).comp
    (F.terminalConjugateCenterEquiv g hGH).toMonoidHom

public theorem terminalCenterImageMap_surjective (F : InvariantFlag T V n)
    (g : G) (hGH : conjugate F.ZU g ≤ F.H) :
    Function.Surjective (F.terminalCenterImageMap g hGH) :=
  ((QuotientGroup.mk' F.terminalHatAction.ker).subgroupMap_surjective _).comp
    (F.terminalConjugateCenterEquiv g hGH).surjective

public theorem terminalCenterImageMap_ker (F : InvariantFlag T V n)
    (g : G) (hGH : conjugate F.ZU g ≤ F.H)
    (hk : conjugate F.ZU g ⊓ F.terminalHatAction.ker.map F.H.subtype =
      conjugate (F.Vi 1) g) :
    (F.terminalCenterImageMap g hGH).ker = (F.Vi 1).subgroupOf F.ZU := by
  ext z
  change F.terminalCenterImageMap g hGH z = 1 ↔ (z : G) ∈ F.Vi 1
  constructor
  · intro hz
    have hq := congrArg Subtype.val hz
    have ha : (F.terminalConjugateCenterEquiv g hGH z : F.H) ∈ F.terminalHatAction.ker :=
      (QuotientGroup.eq_one_iff _).mp hq
    have hx : (MulAut.conj g⁻¹) (z : G) ∈ conjugate (F.Vi 1) g := by
      rw [← hk]
      exact ⟨mem_map_of_mem _ z.property, mem_map_of_mem F.H.subtype ha⟩
    obtain ⟨v, hv, he⟩ := hx
    exact (MulAut.conj g⁻¹).injective he ▸ hv
  · intro hz
    have hx : (MulAut.conj g⁻¹) (z : G) ∈
        conjugate F.ZU g ⊓ F.terminalHatAction.ker.map F.H.subtype := by
      rw [hk]
      exact mem_map_of_mem _ hz
    obtain ⟨a, ha, he⟩ := hx.2
    have he' : a = F.terminalConjugateCenterEquiv g hGH z := Subtype.ext he
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    exact he' ▸ ha

public noncomputable def terminalCenterQuotientEquiv (F : InvariantFlag T V n)
    (g : G) (hGH : conjugate F.ZU g ≤ F.H)
    (hk : conjugate F.ZU g ⊓ F.terminalHatAction.ker.map F.H.subtype =
      conjugate (F.Vi 1) g) :
    (F.ZU ⧸ (F.Vi 1).subgroupOf F.ZU) ≃* F.terminalDot (conjugate F.ZU g) :=
  (QuotientGroup.quotientMulEquivOfEq (F.terminalCenterImageMap_ker g hGH hk).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (F.terminalCenterImageMap g hGH)
      (F.terminalCenterImageMap_surjective g hGH))
/-- The defining conjugation equation on the actual quotient U/Z(U). -/
public theorem terminalHatAction_apply_mk (F : InvariantFlag T V n)
    (h : F.H) (u : F.U) :
    F.terminalHatAction h (QuotientGroup.mk' (center F.U) u) =
      QuotientGroup.mk' (center F.U)
        (F.U.normalizerMonoidHom
          ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u) := by
  exact quotientAut_apply_mk _ _ _

/-- Any earlier action with the same conjugation equation is this action. -/
public theorem terminalHatAction_unique (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u)) :
    ρ = F.terminalHatAction := by
  apply MonoidHom.ext
  intro h
  apply MulEquiv.ext
  intro u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (center F.U) u
  exact (hρ h v).trans (F.terminalHatAction_apply_mk h v).symm

/-- The center isomorphism is induced by right conjugation followed by
H → H/C_H(Uhat), preserving the source quotient map. -/
public theorem terminalCenterQuotientEquiv_apply_mk (F : InvariantFlag T V n)
    (g : G) (hGH : conjugate F.ZU g ≤ F.H)
    (hk : conjugate F.ZU g ⊓ F.terminalHatAction.ker.map F.H.subtype =
      conjugate (F.Vi 1) g) (z : F.ZU) :
    F.terminalCenterQuotientEquiv g hGH hk
        (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.ZU) z) =
      F.terminalCenterImageMap g hGH z := by
  rfl

/-- The exact restricted kernel makes a center strictly larger than the
point survive in the dotted quotient. -/
public theorem terminalDot_center_ne_bot (F : InvariantFlag T V n)
    (g : G) (hGH : conjugate F.ZU g ≤ F.H)
    (hk : conjugate F.ZU g ⊓ F.terminalHatAction.ker.map F.H.subtype =
      conjugate (F.Vi 1) g) (hproper : F.Vi 1 < F.ZU) :
    F.terminalDot (conjugate F.ZU g) ≠ ⊥ := by
  intro hbot
  apply not_le_of_gt hproper
  intro z hz
  have hi : F.terminalCenterImageMap g hGH ⟨z, hz⟩ = 1 := by
    apply Subtype.ext
    exact mem_bot.mp (hbot ▸ (F.terminalCenterImageMap g hGH ⟨z, hz⟩).property)
  have hm : (⟨z, hz⟩ : F.ZU) ∈ (F.terminalCenterImageMap g hGH).ker := hi
  rw [F.terminalCenterImageMap_ker g hGH hk] at hm
  exact hm

/-- The literal image map from the center to its tilded subgroup. -/
public noncomputable def terminalCenterTildeMap (F : InvariantFlag T V n)
    (hZH : F.ZU ≤ F.H) : F.ZU →* F.tilde F.ZU :=
  ((QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H)).subgroupMap
    (F.ZU.subgroupOf F.H)).comp (subgroupOfEquivOfLe hZH).symm.toMonoidHom

public theorem terminalCenterTildeMap_ker (F : InvariantFlag T V n)
    (hZH : F.ZU ≤ F.H) :
    (F.terminalCenterTildeMap hZH).ker = (F.Vi 1).subgroupOf F.ZU := by
  ext z
  change F.terminalCenterTildeMap hZH z = 1 ↔ (z : G) ∈ F.Vi 1
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

/-- The original Z(U)/V₁ quotient is the actual tilded center. -/
public noncomputable def terminalCenterTildeEquiv (F : InvariantFlag T V n)
    (hZH : F.ZU ≤ F.H) :
    (F.ZU ⧸ (F.Vi 1).subgroupOf F.ZU) ≃* F.tilde F.ZU :=
  (QuotientGroup.quotientMulEquivOfEq (F.terminalCenterTildeMap_ker hZH).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (F.terminalCenterTildeMap hZH)
      (((QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H)).subgroupMap_surjective _).comp
        (subgroupOfEquivOfLe hZH).symm.surjective))

public theorem terminalCenterTildeEquiv_apply_mk (F : InvariantFlag T V n)
    (hZH : F.ZU ≤ F.H) (z : F.ZU) :
    F.terminalCenterTildeEquiv hZH
        (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.ZU) z) =
      F.terminalCenterTildeMap hZH z := by
  rfl

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag

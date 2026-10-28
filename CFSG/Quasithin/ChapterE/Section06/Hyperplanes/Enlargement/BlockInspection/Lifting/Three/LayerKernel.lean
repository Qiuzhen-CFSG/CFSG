module

public import Theory.GroupTheory.CComponent.PrimeGroupOvergroup
public import Theory.GroupTheory.PResidual.PrimeSection
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport

/-!
# A characteristic-two envelope for the solvable lifting branch

Put N = C_H(E(H)) and R = NQ, with Q a two-subgroup and O(H) = 1.
The odd core of N is trivial by normality, and this passes to R because
R/N is a two-group. A component of R lies in N by perfectness. Subnormality
then makes it a component of H contained in C_H(E(H)), which is impossible.
Consequently F*(R) = O₂(R).

A short block X of R also lies in N, this time by two-perfection. Restriction
of its subnormal chain to N, followed by normality of N in H, proves that X
is a block of H. Thus the A₃ branch can work inside a characteristic-two
envelope once it proves that the original block centralizes E(H). No such
placement or block-existence assertion is assumed by these group lemmas.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
E.6.23, printed p.254 (PDF p.265). This is an independent reduction for the
solvable branch, replacing the unavailable direct use of 1.2.4.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem layer_normal : (componentLayer G).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  apply le_normalizer_iff.mpr
  intro g _ x hx
  have hm : (componentLayer G).map (MulAut.conj g).toMonoidHom ≤ componentLayer G := by
    apply (map_le_iff_le_comap).mpr
    apply sSup_le
    intro J hJ
    exact (map_le_iff_le_comap).mp (le_sSup (hJ.map_conj g))
  exact hm (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)

omit [Finite G] in
private theorem component_map_of_le_normal {N R : Subgroup G} [N.Normal]
    (hNR : N ≤ R) {J : Subgroup R} (hJ : IsComponent R J)
    (hJN : J ≤ N.subgroupOf R) : IsComponent G (J.map R.subtype) := by
  let X := J.map R.subtype
  have hXN : X ≤ N := by
    rintro x ⟨j, hj, rfl⟩
    exact hJN hj
  have hXR : X.subgroupOf R = J := by
    exact comap_map_eq_self_of_injective R.subtype_injective J
  have hsR : (X.subgroupOf R).IsSubnormal := hXR.symm ▸ hJ.1
  have hsN : (X.subgroupOf N).IsSubnormal := hsR.comap (inclusion hNR)
  let := hJ.2
  exact ⟨hsN.trans hXN (inferInstance : N.Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv (J.equivMapOfInjective R.subtype R.subtype_injective)⟩

omit [Finite G] in
private theorem no_component_in_layer_centralizer {X : Subgroup G}
    (hX : IsComponent G X) (hXC : X ≤ centralizer (componentLayer G : Set G)) : False := by
  have hXE : X ≤ componentLayer G := le_sSup hX
  let := hX.2
  have hc : ⁅X, X⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hXC.trans (centralizer_le hXE))
  rw [commutator_eq_self] at hc
  exact hX.isCComponent.ne_bot hc

/-- Adjoining a two-subgroup to the centralizer of the layer gives characteristic two
when the original group has trivial odd core. The two-subgroup need not be Sylow. -/
theorem layer_centralizer_sup_fitting (S : Subgroup G) (hS : IsPGroup 2 S)
    (ho : pPrimeCore 2 G = ⊥) :
    generalizedFitting ↥(centralizer (componentLayer G : Set G) ⊔ S) =
      pCore 2 ↥(centralizer (componentLayer G : Set G) ⊔ S) := by
  let N := centralizer (componentLayer G : Set G)
  let _ : (componentLayer G).Normal := layer_normal
  let _ : N.Normal := inferInstance
  let R := N ⊔ S
  have hNR : N ≤ R := le_sup_left
  let _ : (N.subgroupOf R).Normal := inferInstance
  have hgen : N.subgroupOf R ⊔ S.subgroupOf R = ⊤ := by
    rw [← subgroupOf_sup (show N ≤ R from le_sup_left) (show S ≤ R from le_sup_right)]
    exact subgroupOf_self R
  have hquot : IsPGroup 2 (R ⧸ N.subgroupOf R) :=
    isPGroup_quotient_of_sup_eq_top _ _ hS.comap_subtype hgen
  have hNo : pPrimeCore 2 N = ⊥ :=
    (inferInstance : N.Normal).isSubnormal.pPrimeCore_eq_bot ho
  have hNo' : pPrimeCore 2 (N.subgroupOf R) = ⊥ := by
    let e := subgroupOfEquivOfLe hNR
    apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
    rw [pPrimeCore_map_iso, hNo]
  have hRo : pPrimeCore 2 R = ⊥ :=
    pPrimeCore_eq_bot_of_isPGroup_quotient 2 _ hNo' hquot
  have hE : componentLayer R = ⊥ := by
    apply sSup_eq_bot.mpr
    intro J hJ
    let := hJ.2
    let : Group.IsNilpotent (R ⧸ N.subgroupOf R) := hquot.isNilpotent
    have hJN : J ≤ N.subgroupOf R :=
      (le_solvableResidual_of_isPerfect J).trans (solvableResidual_le_of_solvable_quotient _)
    exact (no_component_in_layer_centralizer
      (component_map_of_le_normal hNR hJ hJN) (by
        rintro x ⟨j, hj, rfl⟩
        exact hJN hj)).elim
  change generalizedFitting R = pCore 2 R
  rw [generalizedFitting, hE, sup_bot_eq, Fitting_eq_pcore R 2 hRo]

/-- Two-perfection puts the short subgroup in the normal kernel; restricting its
subnormal chain there then lifts the block to the original ambient group. -/
theorem block_lift_from_normal_sup {N S X : Subgroup G} [N.Normal]
    (hS : IsPGroup 2 S) (hX : X ≤ N ⊔ S)
    (hb : ChapterC.IsBlock (X.subgroupOf (N ⊔ S))) : ChapterC.IsBlock X := by
  have hs : ChapterC.IsShort X := hb.short.of_mulEquiv (subgroupOfEquivOfLe hX)
  have hXN : X ≤ N := le_normal_of_isPPerfect_of_le_sup_pGroup
    X N S hs.twoPerfect hS hX
  have hsub : (X.subgroupOf N).IsSubnormal :=
    hb.subnormal.comap (inclusion (show N ≤ N ⊔ S from le_sup_left))
  exact ⟨inferInstance, hs, hsub.trans hXN (inferInstance : N.Normal).isSubnormal⟩

/-- The actual centralizer of E(H), embedded in the ambient group. -/
@[expose] def layerKernel (H : Subgroup G) : Subgroup G :=
  (centralizer (componentLayer H : Set H)).map H.subtype

/-- The subgroup C_H(E(H))Q used for the solvable lifting branch. -/
@[expose] def layerEnvelope (H Q : Subgroup G) : Subgroup G := layerKernel H ⊔ Q

omit [Finite G] in
/-- The embedded layer centralizer is contained in H. -/
theorem layerKernel_le (H : Subgroup G) : layerKernel H ≤ H := map_subtype_le _

omit [Finite G] in
/-- Adjoining Q inside H stays inside H. -/
theorem layerEnvelope_le {H Q : Subgroup G} (hQ : Q ≤ H) : layerEnvelope H Q ≤ H :=
  sup_le (layerKernel_le H) hQ

/-- Characteristic two of the actual ambient envelope, with both intrinsic cores
transported through the same subgroup isomorphism. -/
theorem layerEnvelope_fitting {H Q : Subgroup G} (hQH : Q ≤ H) (hQ : IsPGroup 2 Q)
    (ho : pPrimeCore 2 H = ⊥) :
    generalizedFitting (layerEnvelope H Q) = pCore 2 (layerEnvelope H Q) := by
  let R := centralizer (componentLayer H : Set H) ⊔ Q.subgroupOf H
  have he : R.map H.subtype = layerEnvelope H Q := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hQH]
    rfl
  let e := (R.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr he)
  have hf := layer_centralizer_sup_fitting (Q.subgroupOf H) hQ.comap_subtype ho
  exact (map_generalizedFitting_equiv e).symm.trans
    ((congrArg (Subgroup.map e.toMonoidHom) hf).trans (pCore_map_iso 2 e))

/-- A block of C_H(E(H))Q is a block of H. This uses two-perfection and
relative subnormality, without treating the envelope itself as normal in H. -/
theorem block_lift_from_layerEnvelope {H Q X : Subgroup G}
    (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) (hX : X ≤ layerEnvelope H Q)
    (hb : ChapterC.IsBlock (X.subgroupOf (layerEnvelope H Q))) :
    ChapterC.IsBlock (X.subgroupOf H) := by
  let N := centralizer (componentLayer H : Set H)
  let R := N ⊔ Q.subgroupOf H
  have hRH : (layerEnvelope H Q) ≤ H := layerEnvelope_le hQH
  have hXH : X ≤ H := hX.trans hRH
  have he : R.map H.subtype = layerEnvelope H Q := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hQH]
    rfl
  let e : R ≃* layerEnvelope H Q :=
    (R.equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr he)
  have hXR : X.subgroupOf H ≤ R := by
    intro x hx
    have hxmap : (x : G) ∈ R.map H.subtype := he.symm ▸ hX hx
    obtain ⟨y, hy, hyx⟩ := hxmap
    exact (Subtype.ext hyx : y = x) ▸ hy
  have hsub : ((X.subgroupOf H).subgroupOf R).IsSubnormal :=
    hb.subnormal.comap e.toMonoidHom
  have hs : ChapterC.IsShort (X.subgroupOf H) :=
    (hb.short.of_mulEquiv (subgroupOfEquivOfLe hX)).of_mulEquiv
      (subgroupOfEquivOfLe hXH).symm
  have hs' : ChapterC.IsShort ((X.subgroupOf H).subgroupOf R) :=
    hs.of_mulEquiv (subgroupOfEquivOfLe hXR).symm
  let _ : (componentLayer H).Normal := layer_normal
  let _ : N.Normal := inferInstance
  exact block_lift_from_normal_sup hQ.comap_subtype hXR
    ⟨inferInstance, hs', hsub⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three

module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Actions
public import CFSG.Quasithin.ChapterF.Section09.Basic
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Source inputs for the faithful central-transvection action

The kernel of conjugation on the actual U/Z is exactly the commutator
centralizer in F.9, hence O₂(H). The centralizer of the order-two seed is
a two-local subgroup and supplies the SQTK cover. Finally a nontrivial
normal subgroup V-star of the Sylow image meets its center, supplying
the marked element required by the central clause of G.6.4.

Source: Aschbacher–Smith, Lemmas 15.3.48 and 15.3.52,
printed pp.1144–1145.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion
open Recognition FusionCore.CosetSetup
variable {G : Type*} [Group G] [Finite G]

 theorem centralizer_sqtk {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (Z : Subgroup G) (hZ : Nat.card Z = 2) : IsSQTK κ (centralizerH Z) := by
  apply hG.twoLocal_sqtk
  have he : centralizerH Z = normalizer (Z : Set G) :=
    le_antisymm (Subgroup.centralizer_le_normalizer _) (normalizer_le_centralizer_of_card_two Z hZ)
  rw [he]
  refine ⟨Z, ?_, IsPGroup.of_card_dvd_pow (n := 1) (by rw [hZ]; simp), rfl⟩
  intro hz
  rw [hz, card_bot] at hZ
  omega

omit [Finite G] in
 theorem quotientAction_kernel (Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [(Z.subgroupOf (centralizerH Z)).Normal]
    (hZS : ZS ≤ centralizerH Z) :
    (quotientAction Z ZS).ker = quotientCentralizer (centralizerH Z) (closureU Z ZS) Z := by
  ext x
  rw [mem_quotientCentralizer_iff _ _ _ (closureU_le_H hZS)]
  change quotientAction Z ZS x = 1 ↔ _
  constructor
  · intro hx u hu
    have he := congrArg (fun a : MulAut (VectorQuotient Z ZS) =>
      a (QuotientGroup.mk' _ ⟨u,hu⟩)) hx
    rw [quotientAction_mk] at he
    have hh := QuotientGroup.eq_iff_div_mem.mp he
    change (x : G) * u * (x : G)⁻¹ / u ∈ Z at hh
    rw [div_eq_mul_inv] at hh
    change ⁅(x : G),u⁆ ∈ Z at hh
    simpa only [commutatorElement_inv] using Z.inv_mem hh
  · intro hx
    apply MulEquiv.ext
    intro w
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (closureU Z ZS)) w
    rw [quotientAction_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (x : G) * (u : G) * (x : G)⁻¹ / (u : G) ∈ Z
    rw [div_eq_mul_inv]
    change ⁅(x : G),(u : G)⁆ ∈ Z
    simpa only [commutatorElement_inv] using Z.inv_mem (hx u u.property)

 theorem source_kernel (T : Sylow 2 G) (L V ZS Z : Subgroup G)
    (h : (⟨T,L,V,ZS,Z,centralizerH Z⟩ : ChapterF.Section09.Setup G).Hypothesis) :
    let := denominator_normal h.plus_le_H
    (quotientAction Z ZS).ker = pCore 2 (centralizerH Z) := by
  let := denominator_normal h.plus_le_H
  let := h.point_normal
  exact (quotientAction_kernel Z ZS h.plus_le_H).trans h.centralizerModulo_UH_eq_pCore

 theorem exists_central_mark (Z V : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ centralizerH Z) (hVT : V ≤ (T : Subgroup G))
    (hnorm : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : Recognition.actorImage Z V ≠ ⊥) :
    ∃ (t : ActorQuotient Z), t ∈ Recognition.actorImage Z V ∧ t ≠ 1 ∧
      t ∈ (center ((T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective _))).map
        (((T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective _) :
          Sylow 2 (ActorQuotient Z)) : Subgroup (ActorQuotient Z)).subtype := by
  let R : Sylow 2 (ActorQuotient Z) :=
    (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective _)
  let W := Recognition.actorImage Z V
  have hWR : W ≤ (R : Subgroup (ActorQuotient Z)) :=
    map_mono (fun _ hv => hVT hv)
  have hRN : (R : Subgroup (ActorQuotient Z)) ≤ normalizer (W : Set (ActorQuotient Z)) := by
    rintro _ ⟨t, ht, rfl⟩
    apply (V.subgroupOf (centralizerH Z)).le_normalizer_map (QuotientGroup.mk' _)
    apply mem_map_of_mem
    rw [← subgroupOf_normalizer_eq (hVT.trans hTH)]
    exact hnorm ht
  let N := W.subgroupOf (R : Subgroup (ActorQuotient Z))
  let : N.Normal := normal_subgroupOf_of_le_normalizer hRN
  let : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hne
  let : Nontrivial N := (subgroupOfEquivOfLe hWR).toEquiv.nontrivial
  let : Fact (IsPGroup 2 R) := ⟨R.isPGroup'⟩
  obtain ⟨x, hx, hc⟩ := exists_nontrivial_center_mem_normal (p := 2) N
  refine ⟨x.val.val, x.property, ?_, ⟨x.val,hc,rfl⟩⟩
  intro he
  apply hx
  apply Subtype.ext
  exact Subtype.ext he

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion

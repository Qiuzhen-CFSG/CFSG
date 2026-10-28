module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrioSections
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairCore

/-!
# Marking the original cocode pair factor

The component marking restricts to a surjection from N_L(U) onto the
native trio stabilizer, and hence maps its solvable residual onto the
native residual. The bound [R,I] ≤ O₂(R) and relative normality put [R,V]
inside B=V∩O₂(I). The selected quotient gives B rank nine; native trio
commutators fill a nine-space, identifying B with the actual pair space.
This supplies the markings consumed by MathieuTrioSections on the original
chosen pair in NonFFSourceMathieuM24Section.
Source: Aschbacher--Smith H.15.6(1,3), E.2.14 and 8.2.8(4),
printed pp.228,401,718, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
variable {G : Type*} [Group G] [Finite G]

/-- The original residual maps onto the native trio residual. -/
theorem plane_residual_marking (W L U : Subgroup G) [IsElementaryAbelian 2 W]
    (hLW : L ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (q : L →* M24) (hq : Function.Surjective q)
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (l : L) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w)) =
        cocodeRepresentation (q l) (F (Additive.ofMul w)))
    (hplane : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range) :
    let R := Chapter8.Section02.Normalizer.localResidual L U
    ∃ f : R →* trioStabilizer standardTrio,
      f.range = solvableResidual (trioStabilizer standardTrio) ∧
      ∀ r : R, (f r).val = q (inclusion
        ((Chapter8.Section02.Normalizer.localResidual_le L U).trans inf_le_left) r) := by
  let N := L ⊓ normalizer (U : Set G)
  let R₀ := solvableResidual N
  let R := Chapter8.Section02.Normalizer.localResidual L U
  have hn (n : N) : q (inclusion (show N ≤ L from inf_le_left) n) ∈
      trioStabilizer standardTrio := by
    rw [←plane_stabilizer_eq_trio]
    intro v
    obtain ⟨w,rfl⟩ := F.surjective v
    have he := hF (inclusion (show N ≤ L from inf_le_left) n) w.toMul
    simp only [ofMul_toMul] at he
    rw [←he,←hplane]
    have hp := hplane w.toMul
    simp only [ofMul_toMul] at hp
    rw [←hp]
    exact (mem_normalizer_iff.mp n.property.2 w.toMul.val).symm
  let fN : N →* trioStabilizer standardTrio :=
    (q.comp (inclusion inf_le_left)).codRestrict _ hn
  have hfN : Function.Surjective fN := by
    intro t
    obtain ⟨l,hl⟩ := hq t.val
    have ht : q l ∈ subspaceStabilizer cocodeRepresentation standardPlaneMap.range := by
      rw [hl,plane_stabilizer_eq_trio]
      exact t.property
    have hlU : l.val ∈ normalizer (U : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hxW := hUW hx
        have hh := (ht (F (Additive.ofMul ⟨x,hxW⟩))).mpr ((hplane _).mp hx)
        rw [←hF,←hplane] at hh
        exact hh
      · intro hx
        have hxW := (mem_normalizer_iff.mp (hLW l.property) x).mpr (hUW hx)
        apply (hplane ⟨x,hxW⟩).mpr
        apply (ht _).mp
        rw [←hF]
        exact (hplane _).mp hx
    exact ⟨⟨l,l.property,hlU⟩,Subtype.ext hl⟩
  let b : R₀ ≃* R := R₀.equivMapOfInjective N.subtype N.subtype_injective
  let f := (fN.comp R₀.subtype).comp b.symm.toMonoidHom
  refine ⟨f,?_,?_⟩
  · change ((fN.comp R₀.subtype).comp b.symm.toMonoidHom).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr b.symm.surjective,
      ←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype,
      map_solvableResidual_eq fN hfN]
  · intro r
    obtain ⟨r,rfl⟩ := b.surjective r
    change (fN (b.symm (b r)).val).val = _
    rw [b.symm_apply_apply]
    rfl

/-- The original commutator containment and dimension identify B with the
native nine-dimensional pair space, in the given cocode coordinates. -/
theorem pair_space_marking (W R B : Subgroup G) [IsElementaryAbelian 2 W]
    (hBW : B ≤ W) (hRW : R ≤ normalizer (W : Set G))
    (hcomm : ⁅R,W⁆ ≤ B) (hdim : rank B = 9)
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (f : R →* trioStabilizer standardTrio)
    (hf : f.range = solvableResidual (trioStabilizer standardTrio))
    (hF : ∀ (r : R) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨r,hRW r.property⟩ w)) =
        cocodeRepresentation (f r).val (F (Additive.ofMul w))) :
    ∀ w : W, (w : G) ∈ B ↔ F (Additive.ofMul w) ∈ standardPairSpace := by
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBW
  let j : Additive B →ₗ[ZMod 2] Cocode := F.toLinearMap.comp
    ((inclusion hBW).toAdditive.toZModLinearMap 2)
  have hj : Function.Injective j := F.injective.comp (inclusion_injective hBW)
  have hle : standardPairSpace ≤ j.range := by
    change (⨆ C ∈ standardTrio.parts, supportedPairSpace C) ≤ j.range
    rw [standard_pairSpace_eq_residual_commutator]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,⟨t,ht,rfl⟩,v,_,rfl⟩
    rw [←hf] at ht
    obtain ⟨r,hr⟩ := ht
    obtain ⟨w,rfl⟩ := F.surjective v
    let z : B := ⟨⁅r.val,w.toMul.val⁆,
      hcomm (commutator_mem_commutator r.property w.toMul.property)⟩
    refine ⟨Additive.ofMul z,?_⟩
    have hz : (inclusion hBW z : W) =
        W.normalizerMonoidHom ⟨r,hRW r.property⟩ w.toMul / w.toMul := by
      apply Subtype.ext
      simp only [z,commutatorElement_def,div_eq_mul_inv]
      rfl
    change F (Additive.ofMul (inclusion hBW z)) = _
    rw [hz]
    change F (Additive.ofMul (W.normalizerMonoidHom ⟨r,hRW r.property⟩ w.toMul) - w) = _
    rw [map_sub,hF,hr]
    rfl
  have heq : standardPairSpace = j.range := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [LinearMap.finrank_range_of_inj hj,←Chapter7.log_card_eq_finrank B]
    exact (finrank_pairSpace standardTrio).trans hdim.symm
  intro w
  rw [heq]
  constructor
  · intro hw
    exact ⟨Additive.ofMul ⟨w.val,hw⟩,rfl⟩
  · rintro ⟨b,hb⟩
    have he : inclusion hBW b.toMul = w := F.injective hb
    exact (congrArg Subtype.val he) ▸ b.toMul.property

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair
open ChapterE Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]

/-- The selected degree two pair meets V in a nine-dimensional core factor. -/
theorem selected_two_intersection_rank {H T M V I : Subgroup G}
    [IsElementaryAbelian 2 V] {i : I} {S : Sylow 2 I}
    (s : Selected H T M V I 2 i S) (hV : rank V = 11) :
    rank (V ⊓ I.pCoreIn 2 : Subgroup G) = 9 := by
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hr := s.rank_eq
  change Nat.log 2 (Nat.card ((V.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)))) = 2 at hr
  rw [←relIndex_ker,QuotientGroup.ker_mk'] at hr
  have hi := relIndex_map_map_of_injective (pCore 2 I) (V.subgroupOf I) I.subtype_injective
  rw [map_subgroupOf_eq_of_le hVI] at hi
  have hc : subgroupCorank V (V ⊓ I.pCoreIn 2) = 2 := by
    rw [subgroupCorank,inf_relIndex_left]
    exact hi ▸ hr
  have hd := offender_corank_add (B := (⊥ : Subgroup G)) bot_le
    (show V ⊓ I.pCoreIn 2 ≤ V from inf_le_left)
  simp only [subgroupCorank,relIndex_bot_left] at hd
  change rank V = _ + rank (V ⊓ I.pCoreIn 2 : Subgroup G) at hd
  change Nat.log 2 ((V ⊓ I.pCoreIn 2).relIndex V) = 2 at hc
  omega

omit [Finite G] in
/-- The component commutator bound forces all residual displacement of V
into the actual pair core, using only relative normality. -/
theorem residual_commutator_le_pair_factor (R I V : Subgroup G)
    (hVI : V ≤ I) (hRI : R ≤ normalizer (I : Set G))
    (hIR : I ≤ normalizer (R : Set G)) (hRV : R ≤ normalizer (V : Set G))
    (hc : ⁅R,I⁆ ≤ R.pCoreIn 2) : ⁅R,V⁆ ≤ V ⊓ I.pCoreIn 2 := by
  have hIQ : I ≤ normalizer (R.pCoreIn 2 : Set G) :=
    hIR.trans (normalizer_le_normalizer_characteristic_image R (pCore 2 R))
  have hQI : R.pCoreIn 2 ⊓ I ≤ I.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 R).to_le inf_le_left) inf_le_right
      ((le_inf hIQ I.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  exact le_inf (le_normalizer_iff_commutator_le_right.mp hRV)
    ((le_inf ((commutator_mono le_rfl hVI).trans hc)
      ((commutator_mono le_rfl hVI).trans
        (le_normalizer_iff_commutator_le_right.mp hRI))).trans hQI)

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPair

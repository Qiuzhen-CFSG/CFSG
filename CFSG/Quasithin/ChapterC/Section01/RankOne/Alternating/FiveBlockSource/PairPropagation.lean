module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.MarkedSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.ShortSeedPropagation
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.EasyCases
public import Theory.GroupTheory.PResidual.SylowSupplement
/-!
# Propagating the original selected pair to the A₅ component

The first two local alternatives extend using the literal generation YR=H:
C₁ is already central in R, and the second member is characteristic in
Baumann(R). In the third case the selected target's residual is identified
with the original cubic Y. The shared short-seed theorem then proves every
block clause for L, with its noncentral image and core normalization derived
from the actual marked A₅ quotient.

Source: C.1.21(2), C.1.23(1), printed pp.128–130.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open ChapterB
universe u v
variable {H : Type u} [Group H] [Finite H]

omit [Finite H] in
/-- The central and normal alternatives propagate on the original pair.
The first subgroup may be the smaller C₁ of an external two-group. -/
theorem local_pair_ambient_alternatives
    (R Y C : Subgroup H) (hgen : Y ⊔ R = ⊤)
    (D : GlaubermanNiles.CharacteristicPair (baumann R))
    (hC : C ≤ (center R).map R.subtype) (hCD : C ≤ D.first.map (baumann R).subtype)
    {A : Type v} [Group A] (k : A →* H) (j : baumann R →* A)
    (hkj : k.comp j = (baumann R).subtype)
    (hY : Y ≤ k.range)
    (hAlt : GlaubermanNiles.Alternatives D.first D.second j) :
    C ≤ center H ∨ (D.second.map (baumann R).subtype).Normal ∨ GlaubermanNiles.BlockAlternative A := by
  rcases hAlt with hfirst | hsecond | hblock
  · left
    have hYC : Y ≤ centralizer (C : Set H) := by
      intro y hy c hc
      obtain ⟨a,ha⟩ := hY hy
      obtain ⟨b,hb,hbc⟩ := hCD hc
      have hz := hfirst (mem_map_of_mem j hb)
      have hh := congrArg k ((mem_center_iff.mp hz) a)
      have hjb : k (j b) = (b : H) := DFunLike.congr_fun hkj b
      change (b : H) = c at hbc
      simpa only [map_mul,hjb,ha,hbc] using hh.symm
    have hRC : R ≤ centralizer (C : Set H) := by
      intro r hr c hc
      obtain ⟨z,hz,hzc⟩ := hC hc
      have hh := congrArg R.subtype ((mem_center_iff.mp hz) ⟨r,hr⟩)
      change (z : H) = c at hzc
      change r * (z : H) = (z : H) * r at hh
      simpa only [hzc] using hh.symm
    have hall : (⊤ : Subgroup H) ≤ centralizer (C : Set H) := hgen ▸ sup_le hYC hRC
    intro c hc
    exact mem_center_iff.mpr (fun g => (hall (mem_top g) c hc).symm)
  · right; left
    let : D.second.Characteristic := D.second_characteristic
    let : (D.second.map j).Normal := hsecond
    have he : (D.second.map j).map k = D.second.map (baumann R).subtype := by
      rw [map_map,hkj]
    have ha : k.range ≤ normalizer (D.second.map (baumann R).subtype : Set H) := by
      have hh := (D.second.map j).le_normalizer_map k
      rwa [normalizer_eq_top,←MonoidHom.range_eq_map,he] at hh
    have hr : R ≤ normalizer (D.second.map (baumann R).subtype : Set H) :=
      (R.le_normalizer.trans (normalizer_le_normalizer_baumann R)).trans
        (normalizer_le_normalizer_characteristic_image _ D.second)
    apply normalizer_eq_top_iff.mp
    exact top_le_iff.mp (hgen ▸ sup_le (hY.trans ha) hr)
  · exact Or.inr (Or.inr hblock)

/-- The selected target's two-residual has exactly the original ambient
image; this transports the short group asserted by C.1.18. -/
theorem selected_local_block_short
    (N : Subgroup H) (A : Subgroup N) (Y B : Subgroup H)
    (hA : A.map N.subtype = Y ⊔ B)
    (hY : IsPPerfect 2 Y) (hB : IsPGroup 2 B)
    (hn : B ≤ normalizer (Y : Set H))
    (hb : GlaubermanNiles.BlockAlternative A) : IsShort Y := by
  let k : A →* H := N.subtype.comp A.subtype
  have hk : Function.Injective k := N.subtype_injective.comp A.subtype_injective
  have hm : (pResidual 2 A).map k = Y := by
    rw [←map_map,map_embedded_pResidual,hA,embedded_pResidual_join_pGroup Y B hY hB hn]
  exact hb.1.short.of_mulEquiv
    (((pResidual 2 A).equivMapOfInjective k hk).trans (MulEquiv.subgroupCongr hm))



private theorem subnormal_characteristic_fitting (L : Subgroup H)
    (hL : L.IsSubnormal) (hf : generalizedFitting H = pCore 2 H) :
    generalizedFitting L = pCore 2 L := by
  have hm : (generalizedFitting L).map L.subtype ≤ pCore 2 H :=
    (generalizedFitting_map_subtype_le_of_isSubnormal L hL).trans_eq hf
  have hp : IsPGroup 2 ((generalizedFitting L).map L.subtype) := pCore_isPGroup.to_le hm
  have hp' : IsPGroup 2 (generalizedFitting L) := hp.of_equiv
    ((generalizedFitting L).equivMapOfInjective L.subtype L.subtype_injective).symm
  exact le_antisymm (le_sSup ⟨inferInstance,hp'⟩)
    ((pCore_le_fitting L 2).trans (fitting_le_generalizedFitting L))

private theorem perfect_twoPerfect {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] : IsPPerfect 2 G := by
  intro N hn hq
  let : N.Normal := hn
  by_contra hne
  let : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (G ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (G ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (G ⧸ N) inferInstance

open Theory.SpecificGroups.SymmetricFive Theory.SpecificGroups.SymmetricFive.CubicSelection
/-- The original selected cubic is noncentral in the original component
quotient. Its nontrivial three-image excludes containment in the two-core. -/
theorem selected_cubic_core_noncentral
    (q : H →* Equiv.Perm (Fin 5)) (L : Subgroup H)
    (hL : L.map q = alternatingGroup (Fin 5))
    (hz : center (L ⧸ pCore 2 L) = ⊥) :
    ¬ ((selectedResidual q L).subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) ≤
      center (L ⧸ pCore 2 L) := by
  let Y := selectedResidual q L
  have hYL : Y ≤ L := selectedResidual_le q L
  intro hc
  rw [hz] at hc
  have hcore : Y.subgroupOf L ≤ pCore 2 L := by
    have hh := map_le_iff_le_comap.mp hc
    rwa [MonoidHom.comap_bot,QuotientGroup.ker_mk'] at hh
  have hYC : Y ≤ (pCore 2 L).map L.subtype := by
    have hh := map_mono (f:=L.subtype) hcore
    rwa [map_subgroupOf_eq_of_le hYL] at hh
  have hbot : Y = ⊥ := bot_unique
    (le_normal_of_isPPerfect_of_le_sup_pGroup Y ⊥ ((pCore 2 L).map L.subtype)
      (selectedResidual_twoPerfect q L) (pCore_isPGroup.map L.subtype)
      (by simpa only [bot_sup_eq] using hYC))
  have hi := selectedResidual_image q L hL
  change Y.map q = cubic at hi
  rw [hbot,Subgroup.map_bot] at hi
  have hc3 := cubic_card
  have hc1 : Nat.card cubic = 1 := by rw [←hi]; simp
  omega



/-- The actual cubic local block propagates to the original component. -/
theorem selected_local_block_propagates
    (R : Sylow 2 H) (hfit : generalizedFitting H = pCore 2 H)
    (L : Subgroup H) [L.Normal] (hcomp : L.IsCComponent)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hL : L.map q = alternatingGroup (Fin 5))
    (hBi : (baumann (R : Subgroup H)).map q = OuterFourGeometry.four)
    (A : Subgroup (cubicLocalGroup q))
    (hA : A.map (cubicLocalGroup q).subtype = selectedResidual q L ⊔ baumann (R : Subgroup H))
    (hb : GlaubermanNiles.BlockAlternative A) : IsBlock L := by
  let Y := selectedResidual q L
  let B := baumann (R : Subgroup H)
  let N := cubicLocalGroup q
  have hBY : B ≤ normalizer (Y : Set H) :=
    (map_le_iff_le_comap.mp hBi.le).trans (selectedResidual_normalized q L hL)
  have hshort : IsShort Y := selected_local_block_short N A Y B hA
    (selectedResidual_twoPerfect q L) (R.isPGroup'.to_le inf_le_left) hBY hb
  have hQ : pCore 2 H ≤ q.ker := by
    rw [←MonoidHom.comap_bot]
    apply map_le_iff_le_comap.mp
    rw [←Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot]
    exact le_sSup ⟨Subgroup.Normal.map inferInstance q hq,pCore_isPGroup.map q⟩
  have hQY : pCore 2 H ≤ normalizer (Y : Set H) := by
    apply le_trans hQ
    apply le_trans (MonoidHom.ker_le_comap q OuterFourGeometry.four)
    exact selectedResidual_normalized q L hL
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply eL.injective
    rw [map_one]
    have hx' : eL x ∈ center (alternatingGroup (Fin 5)) := by
      apply mem_center_iff.mpr
      intro a
      obtain ⟨y,rfl⟩ := eL.surjective a
      simpa only [map_mul] using congrArg eL ((mem_center_iff.mp hx) y)
    simpa only [alternatingGroup.center_eq_bot (α := Fin 5) (by simp),mem_bot] using hx'
  let : Group.IsPerfect L := hcomp.perfect
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (L ⧸ pCore 2 L) := eL.isSimpleGroup
  let : Group.IsPerfect (L ⧸ pCore 2 L) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (L ⧸ pCore 2 L) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  exact GlaubermanArgument.isBlock_of_short_seed Y L (selectedResidual_le q L)
    hshort hcomp.subnormal perfect_twoPerfect (subnormal_characteristic_fitting L hcomp.subnormal hfit)
    hQY (selected_cubic_core_noncentral q L hL hz)

open Representation Representation.BinaryOffender
open scoped IsMulCommutative
/-- The covered marked S₅ branch of Glauberman's argument, retaining the
original pair and any original central subgroup inside its first member. -/
theorem marked_quotient_block_alternatives
    (R : Sylow 2 H) (hfit : generalizedFitting H = pCore 2 H)
    (L : Subgroup H) [L.Normal] (hcomp : L.IsCComponent)
    (hprod : L ⊔ (R : Subgroup H) = ⊤)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (hR : (R : Subgroup H).map q = OuterFourGeometry.eight)
    (hL : L.map q = alternatingGroup (Fin 5))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v)
    (hJ : ¬ elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (U : Set H))
    (D : GlaubermanNiles.CharacteristicPair (baumann (R : Subgroup H)))
    (hD : D.Universal.{u,u}) (C : Subgroup H)
    (hC : C ≤ (center (R : Subgroup H)).map (R : Subgroup H).subtype)
    (hCD : C ≤ D.first.map (baumann (R : Subgroup H)).subtype) :
    C ≤ center H ∨ (D.second.map (baumann (R : Subgroup H)).subtype).Normal ∨ IsBlock L := by
  have hc := Nat.card_congr eL.toEquiv
  obtain ⟨A,j,hA,hj,hclass,halt⟩ := marked_quotient_original_pair R hfit L hprod hc U
    q hq hk hR hL p hp he hfix hJ D hD
  let Y := selectedResidual q L
  let B := baumann (R : Subgroup H)
  let N := cubicLocalGroup q
  let k : A →* H := N.subtype.comp A.subtype
  have hkp := action_kernel_twoGroup q L R hprod R.isPGroup' hL hc
  have hgen : Y ⊔ (R : Subgroup H) = ⊤ :=
    selectedResidual_generates q L R hL hR (hkp.le_sylow_of_normal R)
  have hrange : k.range = Y ⊔ B := by
    rw [MonoidHom.range_comp,range_subtype]
    exact hA
  have hYr : Y ≤ k.range := hrange.symm ▸ le_sup_left
  have hab : C ≤ center H ∨ (D.second.map (baumann (R : Subgroup H)).subtype).Normal ∨
      GlaubermanNiles.BlockAlternative A :=
    @local_pair_ambient_alternatives H inferInstance (R : Subgroup H) Y C hgen D hC hCD
      A inferInstance k j hj hYr halt
  rcases hab with hf | hn | hb
  · exact Or.inl hf
  · exact Or.inr (Or.inl hn)
  · right; right
    have hUR : U ≤ R := (show U ≤ pCore 2 H from
      le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩).trans
        (pCore_isPGroup.le_sylow_of_normal R)
    have hBi := (marked_quotient_images R U hUR q hq hk hR p hp he hfix hJ).2
    exact selected_local_block_propagates R hfit L hcomp eL q hq hL hBi A hA hb

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource

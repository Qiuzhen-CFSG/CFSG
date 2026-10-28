module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ProjectionOrder
public import CFSG.Quasithin.Chapter4.Section04.OddActorOddCore

/-!
# The actual covering residual in a component central quotient

Central projection kills only vectors fixed by the original L. Its elementary
image therefore retains V/C_V(L), and the image modulo its two-core is still
the full original L/O₂(L). In particular the cubic center of SL₃ is retained.
The image is perfect and normalizes an elementary subgroup of order at least
64; its odd prime rank is at least two. All maps come from the original
residual inclusion in the literal N_G(A).

ImageModels uses these data for the remaining moved-component exclusions.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The central image of a covering residual, with its original full quotient
and an elementary subgroup retaining the original central-quotient module. -/
@[expose] def NaturalCoverImage (D : ChosenModule T L V) (Q : Type*) [Group Q] : Prop :=
  ∃ X U : Subgroup Q, Group.IsPerfect X ∧ IsElementaryAbelian 2 U ∧
    U ≤ X.pCoreIn 2 ∧ X ≤ normalizer (U : Set Q) ∧
    Nat.card D.chosenCentralQuotient ∣ Nat.card U ∧
    Nonempty ((X ⧸ pCore 2 X) ≃* (L ⧸ pCore 2 L))

include D S

theorem natural_cover_image {B : Subgroup G} [Group.IsPerfect B] (hBL : B ≤ L)
    (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    {Q : Type*} [Group Q] [Finite Q] (f : B →* Q)
    (hk : IsPGroup 2 f.ker) (hz : f.ker ≤ center B) : NaturalCoverImage D Q := by
  have hVB' : V ≤ B := hVB.trans (pCoreIn_le 2 B)
  let g := f.comp (inclusion hVB')
  have hgker : g.ker ≤ D.toCentralQuotient.ker := by
    intro v hv
    apply (quotient_eq_one_iff D v).mpr
    have hb : (v : G) ∈ centralizer (B : Set G) := by
      intro b hb
      exact congrArg Subtype.val ((mem_center_iff.mp (hz
        (show inclusion hVB' v ∈ f.ker from hv))) ⟨b,hb⟩)
    have hq : (v : G) ∈ centralizer (L.pCoreIn 2 : Set G) :=
      le_centralizer_iff.mp ((centralizer_eq_core D S).ge.trans inf_le_right) v.property
    intro l hl
    obtain ⟨b,hb',q,hq',rfl⟩ := hc ▸ hl
    calc
      b * q * (v : G) = b * ((v : G) * q) := by rw [mul_assoc, hq q hq']
      _ = (v : G) * (b * q) := by rw [←mul_assoc, hb b hb', mul_assoc]
  let j := QuotientGroup.lift g.ker D.toCentralQuotient hgker
  have hj : Function.Surjective j := QuotientGroup.lift_surjective_of_surjective
    g.ker D.toCentralQuotient D.toCentralQuotient_surjective hgker
  have hd : Nat.card D.chosenCentralQuotient ∣ Nat.card g.range := by
    have hd := card_dvd_of_surjective j hj
    rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at hd
  have hnorm : (⊤ : Subgroup B) ≤ normalizer (V.subgroupOf B : Set B) := by
    intro b _ v
    exact D.normalizes (hBL b.property) (v : G)
  have hg : g.range = (V.subgroupOf B).map f := by
    change (f.comp (inclusion hVB')).range = _
    rw [MonoidHom.range_comp,inclusion_range]
  have hUn : f.range ≤ normalizer (g.range : Set Q) := by
    rw [hg]
    simpa only [← MonoidHom.range_eq_map] using
      (map_mono (f := f) hnorm).trans ((V.subgroupOf B).le_normalizer_map f)
  have hUcore : g.range ≤ f.range.pCoreIn 2 := by
    rintro _ ⟨v,rfl⟩
    have hpre := f.rangeRestrict.comap_pCore_of_ker_isPGroup (p := 2)
      f.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hk)
    have hv : inclusion hVB' v ∈ pCore 2 B := by
      obtain ⟨b,hb,he⟩ := hVB v.property
      exact (Subtype.ext he : b = inclusion hVB' v) ▸ hb
    have hmem : f.rangeRestrict (inclusion hVB' v) ∈ pCore 2 f.range := by
      change inclusion hVB' v ∈ (pCore 2 f.range).comap f.rangeRestrict
      rwa [hpre]
    exact mem_map_of_mem f.range.subtype hmem
  obtain ⟨e,_⟩ := cover_quotient hBL hc.subset
  let eq := (f.rangeRestrict.quotientPCoreEquivOfSurjective
    f.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hk)).symm.trans e
  let := D.elementary
  exact ⟨f.range,g.range,Group.IsPerfect.range f,
    IsElementaryAbelian.of_surjective g.rangeRestrict g.rangeRestrict_surjective,
    hUcore,hUn,hd,⟨eq⟩⟩

omit S [Finite G] in
theorem NaturalCoverImage.of_equiv {Q Q' : Type*} [Group Q] [Finite Q]
    [Group Q'] [Finite Q'] (h : NaturalCoverImage D Q) (e : Q ≃* Q') :
    NaturalCoverImage D Q' := by
  obtain ⟨X,U,hX,hU,hUX,hN,hcard,⟨a⟩⟩ := h
  let := hX
  let := hU
  refine ⟨X.map e.toMonoidHom,U.map e.toMonoidHom,Group.IsPerfect.map _,
    IsElementaryAbelian.map _,?_,?_,?_,?_⟩
  · have hh := map_mono (f := e.toMonoidHom) hUX
    rwa [map_pCoreIn_of_injective 2 _ _ e.injective] at hh
  · exact (map_mono hN).trans (U.le_normalizer_map e.toMonoidHom)
  · rwa [card_map_of_injective e.injective]
  · exact ⟨(QuotientGroup.congr _ _ (e.subgroupMap X)
      (pCore_map_iso 2 (e.subgroupMap X))).symm.trans a⟩

theorem NaturalCoverImage.local_data {Q : Type*} [Group Q] [Finite Q]
    (h : NaturalCoverImage D Q) :
    ∃ X U : Subgroup Q, Group.IsPerfect X ∧ IsElementaryAbelian 2 U ∧
      U ≤ X.pCoreIn 2 ∧ U ≠ ⊥ ∧ X ≤ normalizer (U : Set Q) ∧ 64 ≤ Nat.card U ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 ≤ primeRank p X := by
  obtain ⟨X,U,hX,hU,hUX,hN,hcard,⟨a⟩⟩ := h
  have hd : 64 ∣ Nat.card U := (natural_two_parts D S).1.trans hcard
  have hsize := Nat.le_of_dvd (Nat.card_pos (α := U)) hd
  have hne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hsize; omega
  obtain ⟨p,hp,ho,hr⟩ := exists_odd_rank_two D S
  let : Fact p.Prime := ⟨hp⟩
  have hrX : 2 ≤ primeRank p X := by
    rw [←primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 X) pCore_isPGroup,
      primeRank_congr p a]
    exact hr
  exact ⟨X,U,hX,hU,hUX,hne,hN,hsize,p,hp,ho,hrX⟩

theorem NaturalCoverImage.twoRank_ge_six {Q : Type*} [Group Q] [Finite Q]
    (h : NaturalCoverImage D Q) : 6 ≤ primeRank 2 Q := by
  obtain ⟨X,U,hX,hU,hUX,hne,hN,hsize,hr⟩ := h.local_data D S
  by_contra! hlt
  have hb := (primeRank_le_iff_elementary_card_le Q).mp (show primeRank 2 Q ≤ 5 by omega) U hU
  norm_num at hb
  omega

open Chapter4.Section04
/-- The actual residual in N(A) supplies the image through the literal central
quotient. The covering center is retained in its full two-core quotient. -/
theorem placed_residual_natural_cover_image {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hf : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    NaturalCoverImage D (K ⧸ center K) := by
  let N := normalizer (A : Set G)
  let F := oddActorResidual L A
  have hFL : F ≤ L := (oddActorResidual_le L A).trans inf_le_left
  have hFN : F ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hFK : F.subgroupOf N ≤ K := by
    intro x hx
    obtain ⟨k,hk,hkx⟩ := hf hx
    exact (Subtype.ext hkx : k = x) ▸ hk
  let ef : (F.subgroupOf N).subgroupOf K ≃* F :=
    (subgroupOfEquivOfLe hFK).trans (subgroupOfEquivOfLe hFN)
  let j : F →* K := ((F.subgroupOf N).subgroupOf K).subtype.comp ef.symm.toMonoidHom
  have hj : Function.Injective j :=
    ((F.subgroupOf N).subgroupOf K).subtype_injective.comp ef.symm.injective
  let f := (QuotientGroup.mk' (center K)).comp j
  have hcentral : f.ker ≤ center F := by
    intro b hb
    apply mem_center_iff.mpr
    intro c
    apply hj
    simpa only [map_mul] using
      (mem_center_iff.mp ((QuotientGroup.eq_one_iff (j b)).mp hb)) (j c)
  obtain ⟨hc,_,hVcore,_⟩ := actor_cover D S hA hodd
  have hVF : V ≤ F := hVcore.trans (pCoreIn_le 2 F)
  have hker : f.ker ≤ (L.pCoreIn 2).comap F.subtype := by
    intro b hb
    apply (centralizer_eq_core D S).le
    refine ⟨hFL b.property,?_⟩
    intro v hv
    exact congrArg Subtype.val ((mem_center_iff.mp (hcentral hb)) ⟨v,hVF hv⟩)
  have hk : IsPGroup 2 f.ker := ((isPGroup_pCoreIn 2 L).comap_subtype).to_le hker
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  exact natural_cover_image D S hFL hc hVcore f hk hcentral
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

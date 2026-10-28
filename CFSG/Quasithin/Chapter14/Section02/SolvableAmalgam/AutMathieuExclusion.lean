module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.InnerOverlapFusion
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.M12.Aut
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Source
public import Theory.GroupTheory.AbelianWeakClosureFusion
public import Stellmacher.ElementaryAbelianMaxFusion
public import Theory.GroupTheory.InvolutionTransfer

/-!
# Excluding the marked outer Mathieu amalgam

For the actual Aut(M₁₂) pair, the elementary Thompson subgroup has order
sixteen and is normal in the second vertex. When that vertex is a maximal
two-local, it equals the ambient normalizer of the Thompson subgroup.
Burnside fusion therefore preserves the transported inner Mathieu subgroup.
The checked two-step local fusion paths carry every inner involution to
that subgroup's intersection with the Thompson sixteen. An outer involution
cannot fuse into the inner overlap, contradicting Thompson transfer in the
nonabelian simple ambient group.

The final theorem applies this argument to the literal original pair (H,YT).
Its remaining equality M = YT is supplied by the preceding 14.2.21; all
intersection and Sylow data come from `source_hypothesis_F_1_1`.

Source: Aschbacher–Smith, 14.2.22(1), printed p.989.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.AutMathieuExclusion
open Sporadic.Mathieu.M12ExceptionalExtension
open InnerOverlapFusion

private theorem no_index_two {G : Type*} [Group G] [Finite G] {K : GroupClass}
    (hG : IsSimpleQTKE K G) (N : Subgroup G) (hN : N.Normal) :
    N.index ≠ 2 := by
  let := hG.simple
  rcases hN.eq_bot_or_eq_top with h | h
  · rw [h,index_bot]
    intro hc
    let : IsCyclic G := isCyclic_of_prime_card hc
    exact hG.nonabelian inferInstance
  · simp [h]

private theorem fusion_transfer {G : Type*} [Group G] [Finite G] {K : GroupClass}
    (hG : IsSimpleQTKE K G) (T : Sylow 2 G)
    (M A N R : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hA : A = elementaryAbelianMaxJ (T : Subgroup G))
    [IsElementaryAbelian 2 A] (hA0 : A ≠ ⊥)
    (hMA : M ≤ normalizer (A : Set G)) (hMN : M ≤ normalizer (N : Set G))
    (hR : (R.subgroupOf (T : Subgroup G)).index = 2)
    (j : T) (hj : (j : G) ∈ A) (hjN : (j : G) ∉ N) (hjo : orderOf j = 2)
    (hf : ∀ x : T, x ∈ R.subgroupOf (T : Subgroup G) → (x : G)^2 = 1 →
      ∃ y ∈ A, y ∈ N ∧ IsConj (x : G) y) : False := by
  have hAT : A ≤ (T : Subgroup G) := hA ▸ sSup_le (fun _ h => h.1)
  have hloc : IsTwoLocal (normalizer (A : Set G)) :=
    ⟨A,hA0,(inferInstance : IsElementaryAbelian 2 A).isPGroup,rfl⟩
  have hNA : normalizer (A : Set G) ≤ M := (hM.eq_of_le hloc hMA).ge
  obtain ⟨x,hjx,hx⟩ := T.exists_isConj_mem_of_index_two (no_index_two hG)
    (R.subgroupOf (T : Subgroup G)) hR j hjo
  have hxp : (x : G)^2 = 1 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hjx
    rw [←hg]
    change (MulAut.conj g) (j : G) ^ 2 = 1
    rw [←map_pow]
    have hjp : (j : G)^2 = 1 := congrArg Subtype.val (hjo ▸ pow_orderOf_eq_one j)
    rw [hjp,map_one]
  obtain ⟨y,hy,hyN,hxy⟩ := hf x hx hxp
  have hw (g : G) (hg : A.conjBy g ≤ (T : Subgroup G)) : A.conjBy g = A := by
    apply mem_normalizer_iff_map_conj_eq.mp
    rw [hA] at hg ⊢
    exact maxJ_weakly_closed_normalizer T g hg
  obtain ⟨m,hm,he⟩ := T.normalizer_fuses_of_abelian_weakly_closed A hAT hw hj hy (hjx.trans hxy)
  change m * (j : G) * m⁻¹ = y at he
  apply hjN
  apply (mem_normalizer_iff.mp (hMN (hNA hm)) (j : G)).mpr
  rwa [he]

variable {G : Type*} [Group G] {H M S : Subgroup G}
  {hSH : S ≤ H} {hSM : S ≤ M}
private abbrev Pair := RankTwoAmalgam.Iso VerifiedPair.amalgam
  (RankTwoAmalgam.ofSubgroups H S M hSH hSM)
private def middleMap (e : Pair (hSH := hSH) (hSM := hSM)) : overlap →* G :=
  S.subtype.comp e.middle.toMonoidHom
private def leftMap (e : Pair (hSH := hSH) (hSM := hSM)) : firstParabolic →* G :=
  H.subtype.comp e.left.toMonoidHom
private def rightMap (e : Pair (hSH := hSH) (hSM := hSM)) : secondParabolic →* G :=
  M.subtype.comp e.right.toMonoidHom
private theorem middle_injective (e : Pair (hSH := hSH) (hSM := hSM)) :
    Function.Injective (middleMap e) := S.subtype_injective.comp e.middle.injective
private theorem right_injective (e : Pair (hSH := hSH) (hSM := hSM)) :
    Function.Injective (rightMap e) := M.subtype_injective.comp e.right.injective
private theorem middle_range (e : Pair (hSH := hSH) (hSM := hSM)) :
    (middleMap e).range = S := by
  ext x
  constructor
  · rintro ⟨b,rfl⟩
    exact (e.middle b).property
  · intro hx
    exact ⟨e.middle.symm ⟨x,hx⟩,congrArg Subtype.val (e.middle.apply_symm_apply _)⟩
private theorem right_range (e : Pair (hSH := hSH) (hSM := hSM)) :
    (rightMap e).range = M := by
  ext x
  constructor
  · rintro ⟨b,rfl⟩
    exact (e.right b).property
  · intro hx
    exact ⟨e.right.symm ⟨x,hx⟩,congrArg Subtype.val (e.right.apply_symm_apply _)⟩
private theorem left_middle (e : Pair (hSH := hSH) (hSM := hSM)) (b : overlap) :
    leftMap e ⟨b.val,b.property.1⟩ = middleMap e b := congrArg Subtype.val (e.left_commutes b)
private theorem right_middle (e : Pair (hSH := hSH) (hSM := hSM)) (b : overlap) :
    rightMap e ⟨b.val,b.property.2⟩ = middleMap e b := congrArg Subtype.val (e.right_commutes b)

private theorem marked_J_image (e : Pair (hSH := hSH) (hSM := hSM)) :
    (J.subgroupOf overlap).map (middleMap e) =
      (J.subgroupOf secondParabolic).map (rightMap e) := by
  ext x
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨⟨b.val,b.property.2⟩,hb,right_middle e b⟩
  · rintro ⟨b,hb,rfl⟩
    let t : overlap := ⟨b.val,VerifiedPair.secondGeometry.toGeometry.A_le hb⟩
    exact ⟨t,hb,(right_middle e t).symm⟩

private theorem marked_J_eq (e : Pair (hSH := hSH) (hSM := hSM)) :
    (J.subgroupOf overlap).map (middleMap e) = elementaryAbelianMaxJ S := by
  have htop : J.subgroupOf overlap = elementaryAbelianMaxJ (⊤ : Subgroup overlap) := by
    have hm := elementaryAbelianMaxJ_map_injective overlap.subtype overlap.subtype_injective
      (⊤ : Subgroup overlap)
    rw [←MonoidHom.range_eq_map,range_subtype,VerifiedPair.secondGeometry.toGeometry.thompson_eq] at hm
    have hh := congrArg (Subgroup.comap overlap.subtype) hm
    rw [comap_map_eq_self_of_injective overlap.subtype_injective] at hh
    exact hh
  rw [htop,←elementaryAbelianMaxJ_map_injective (middleMap e) (middle_injective e),
    ←MonoidHom.range_eq_map,middle_range]

private theorem marked_inner_image_le (e : Pair (hSH := hSH) (hSM := hSM)) :
    (inner.subgroupOf overlap).map (middleMap e) ≤
      (inner.subgroupOf secondParabolic).map (rightMap e) := by
  rintro _ ⟨b,hb,rfl⟩
  exact ⟨⟨b.val,b.property.2⟩,hb,right_middle e b⟩

private theorem transport_fusion (e : Pair (hSH := hSH) (hSM := hSM))
    (x y z : overlap) (a : secondParabolic) (b : firstParabolic)
    (ha : (a : Carrier)*x*(a : Carrier)⁻¹ = z)
    (hb : (b : Carrier)*z*(b : Carrier)⁻¹ = y) :
    IsConj (middleMap e x) (middleMap e y) := by
  have h1 : IsConj (middleMap e x) (middleMap e z) := by
    apply isConj_iff.mpr
    refine ⟨rightMap e a,?_⟩
    have he := congrArg (rightMap e)
      (show a * (⟨x.val,x.property.2⟩ : secondParabolic) * a⁻¹ = ⟨z.val,z.property.2⟩ from Subtype.ext ha)
    simpa only [map_mul,map_inv,right_middle] using he
  have h2 : IsConj (middleMap e z) (middleMap e y) := by
    apply isConj_iff.mpr
    refine ⟨leftMap e b,?_⟩
    have he := congrArg (leftMap e)
      (show b * (⟨z.val,z.property.1⟩ : firstParabolic) * b⁻¹ = ⟨y.val,y.property.1⟩ from Subtype.ext hb)
    simpa only [map_mul,map_inv,left_middle] using he
  exact h1.trans h2

private theorem inner_index_two : (inner.subgroupOf overlap).index = 2 := by
  let : Sporadic.Mathieu.M12ExceptionalExtension.inner.Normal := normal_of_index_eq_two inner_index
  have hd := inner.relIndex_dvd_index_of_normal (K := overlap)
  rw [inner_index] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · have ht : overlap ≤ Sporadic.Mathieu.M12ExceptionalExtension.inner := relIndex_eq_one.mp h
    exact (SecondCoordinates.swap_not_inner
      (ht (SecondCoordinates.movement_swap ▸ SecondCoordinates.movement_mem_overlap QuaternionSwapModel.swap))).elim
  · exact h

variable [Finite G]

/-- A marked outer Mathieu pair with full Sylow overlap and maximal second
vertex cannot occur in the simple ambient group. -/
theorem false_of_maximal_second {K : GroupClass}
    (hG : IsSimpleQTKE K G) (T : Sylow 2 G)
    (H M : Subgroup G) (hTH : (T : Subgroup G) ≤ H) (hTM : (T : Subgroup G) ≤ M)
    (hM : IsMaximalTwoLocal M)
    (hmodel : ChapterF.GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups H (T : Subgroup G) M hTH hTM)) : False := by
  classical
  obtain ⟨r⟩ := hmodel
  let e : Pair (hSH := hTH) (hSM := hTM) :=
    ((r.trans ChapterF.GreenBook.AutMathieuTwelve.ambientIso.symm).trans
      ChapterF.GreenBook.AutMathieuTwelve.concreteIso).symm
  let f := middleMap e
  let q := rightMap e
  let A := (J.subgroupOf overlap).map f
  let N := (inner.subgroupOf secondParabolic).map q
  let R := (inner.subgroupOf overlap).map f
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.map SecondCoordinates.movement
  let : IsElementaryAbelian 2 (J.subgroupOf overlap) :=
    IsElementaryAbelian.subgroupOf VerifiedPair.secondGeometry.toGeometry.A_le
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  have hA : A = elementaryAbelianMaxJ (T : Subgroup G) := marked_J_eq e
  have hAc : Nat.card A = 16 := by
    rw [card_map_of_injective (middle_injective e),
      Nat.card_congr (subgroupOfEquivOfLe (show J ≤ overlap from VerifiedPair.secondGeometry.toGeometry.A_le)).toEquiv]
    change Nat.card (QuaternionSwapModel.A.map SecondCoordinates.movement) = 16
    rw [card_map_of_injective SecondCoordinates.movement_injective,QuaternionSwapModel.card_A]
  have hA0 : A ≠ ⊥ := by intro h; rw [h,card_bot] at hAc; omega
  have hMA : M ≤ normalizer (A : Set G) := by
    rw [show A = (J.subgroupOf secondParabolic).map q from marked_J_image e]
    let : (J.subgroupOf secondParabolic).Normal := VerifiedPair.secondGeometry.A_normal
    have hh := (J.subgroupOf secondParabolic).le_normalizer_map q
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,right_range] at hh
    exact hh
  have hMN : M ≤ normalizer (N : Set G) := by
    let : Sporadic.Mathieu.M12ExceptionalExtension.inner.Normal := normal_of_index_eq_two inner_index
    have hh := (inner.subgroupOf secondParabolic).le_normalizer_map q
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,right_range] at hh
    exact hh
  have hRi : (R.subgroupOf (T : Subgroup G)).index = 2 := by
    change R.relIndex (T : Subgroup G) = 2
    rw [←middle_range e,MonoidHom.range_eq_map]
    change ((inner.subgroupOf overlap).map f).relIndex ((⊤ : Subgroup overlap).map f) = 2
    rw [relIndex_map_map_of_injective _ _ (middle_injective e),relIndex_top_right]
    exact inner_index_two
  let s : overlap := ⟨SecondCoordinates.swap,
    SecondCoordinates.movement_swap ▸ SecondCoordinates.movement_mem_overlap QuaternionSwapModel.swap⟩
  have hsJ : s.val ∈ J := by
    change SecondCoordinates.swap ∈ J
    rw [←SecondCoordinates.movement_swap]
    exact mem_map_of_mem _ QuaternionSwapModel.swap_mem_A
  have hsN : f s ∉ N := by
    rintro ⟨x,hx,he⟩
    have he' : x = ⟨s.val,s.property.2⟩ := (right_injective e)
      (he.trans (right_middle e s).symm)
    rw [he'] at hx
    exact SecondCoordinates.swap_not_inner hx
  have hso : orderOf s = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact show SecondCoordinates.swap ^ 2 = 1 from by
        rw [pow_two,SecondCoordinates.swap_square]
    · intro he
      apply hsN
      rw [he,map_one]
      exact N.one_mem
  apply fusion_transfer hG T M A N R hM hA hA0 hMA hMN hRi (e.middle s)
    (mem_map.mpr ⟨s,hsJ,rfl⟩) hsN ((e.middle.orderOf_eq s).trans hso)
  intro x hx hxs
  obtain ⟨b,hb,he⟩ := (show (x : G) ∈ R from hx)
  have hbs : (b : Carrier)^2 = 1 := by
    have hp : b^2 = 1 := (middle_injective e) (by
      change f (b^2) = f 1
      rw [map_pow,map_one,he,hxs])
    exact congrArg (fun w : overlap => (w : Carrier)) hp
  obtain ⟨y,z,a,c,hy,hyI,h1,h2⟩ := inner_fusion b hbs hb
  refine ⟨f y,mem_map.mpr ⟨y,hy,rfl⟩,?_,?_⟩
  · exact ⟨⟨y.val,y.property.2⟩,hyI,right_middle e y⟩
  · rw [←he]
    exact transport_fusion e b y z a c h1 h2

/-- The marked row on a literal intersection is impossible when the second
vertex is a maximal two-local and the intersection is the full Sylow. -/
theorem false_of_maximal_second_intersection {K : GroupClass}
    (hG : IsSimpleQTKE K G) (T : Sylow 2 G) (H M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hHM : H ⊓ M = (T : Subgroup G))
    (hmodel : ChapterF.GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups H (H ⊓ M) M inf_le_left inf_le_right)) : False := by
  have hTH : (T : Subgroup G) ≤ H := hHM ▸ inf_le_left
  have hTM : (T : Subgroup G) ≤ M := hHM ▸ inf_le_right
  obtain ⟨e⟩ := hmodel
  let i := RankTwoAmalgam.ofSubgroupsIso (MulEquiv.refl G)
    hTH hTM (inf_le_left : H ⊓ M ≤ H) (inf_le_right : H ⊓ M ≤ M)
    (by simp) (by simpa using hHM.symm) (by simp)
  exact false_of_maximal_second hG T H M hTH hTM hM ⟨i.trans e⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.AutMathieuExclusion

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The Aut(M₁₂) row of original 14.2.22(1), after 14.2.21 supplies `M = YT`.
All amalgam maps are the literal inclusions used by `source_hypothesis_F_1_1`. -/
theorem source_autMathieu_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hq : SmallSolvableModel (H ⧸ pCore 2 H))
    (hMX : M = sourceResidual M Mc ⊔ (T : Subgroup G))
    (hmodel : ChapterF.GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups H (H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)))
        (sourceResidual M Mc ⊔ (T : Subgroup G)) inf_le_left inf_le_right)) : False := by
  have hHX := (source_hypothesis_F_1_1 hG T hempty hM hu hmany hcard e H hH hq).2.1
  apply AutMathieuExclusion.false_of_maximal_second_intersection hG T H
    (sourceResidual M Mc ⊔ (T : Subgroup G)) (hMX ▸ hM.1.1) hHX hmodel

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam

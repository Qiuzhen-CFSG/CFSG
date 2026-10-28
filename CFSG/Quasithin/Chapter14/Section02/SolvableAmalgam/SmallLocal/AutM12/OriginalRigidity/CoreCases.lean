module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceRigidity
public import Theory.GroupTheory.PCoreCentralQuotientImage

/-!
# The corrected invariant-core reduction for Aut(M₁₂)

Recognition of the actual first parabolic transports its nonsplit other core
and square functional. The source centralizer chain makes conjugation on the
quotient faithful; preservation of the functional bounds the larger group by
the already embedded parabolic. Thus the third core alternative forces equality.
The remaining two alternatives make the original marked quaternion base normal
in the larger characteristic-two group, without assuming containment in advance.

Source: Aschbacher--Smith, proof of 14.2.21, printed pp.988--989, with the
corrected nonsplit first-core calculation in SourceModel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity
open SourceModel.Transport
variable {D B R : Type*} [Group D] [Finite D] [Group B] [Group R]

/-- The actual other core, marked through the recognized first parabolic,
forces equality with its characteristic-two overgroup. -/
theorem nonsplit_rigidity
    (H Q Z : Subgroup D) [Q.Normal] [Z.Normal]
    {α : RankTwoAmalgam H B R}
    (r : RankTwoAmalgam.Iso α ChapterF.GreenBook.AutMathieuTwelve.autAmalgam)
    (hQ : Q = (otherCore r).map (H.subtype.comp (pCore 2 H).subtype))
    (hZ : Z = (markedCore r).map (H.subtype.comp (pCore 2 H).subtype))
    (hZcentral : Z ≤ center D)
    (hchain : centralizer (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z)) : H = ⊤ := by
  let k : pCore 2 H →* D := H.subtype.comp (pCore 2 H).subtype
  have hk : Function.Injective k := H.subtype_injective.comp (pCore 2 H).subtype_injective
  have hmA : markedCore r ≤ otherCore r := by
    intro x hx
    change wreathMap r x ∈ FourWreathTwo.other
    have he : wreathMap r x = 1 := by
      apply MonoidHom.mem_ker.mp
      rwa [wreathMap_ker]
    rw [he]
    exact one_mem _
  have hZQ : Z ≤ Q := by rw [hZ,hQ]; exact map_mono hmA
  have hQH : Q ≤ H := by
    rw [hQ]
    rintro _ ⟨x,hx,rfl⟩
    exact x.val.property
  let j : otherCore r ≃* Q :=
    ((otherCore r).equivMapOfInjective k hk).trans (MulEquiv.subgroupCongr hQ.symm)
  have hj (x : otherCore r) : (j x : D) = k x := rfl
  have hjZ : (otherZ r).map j.toMonoidHom = Z.subgroupOf Q := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      change (j a : D) ∈ Z
      rw [hj,hZ]
      exact ⟨a.val,ha,rfl⟩
    · intro hx
      change (x : D) ∈ Z at hx
      rw [hZ] at hx
      obtain ⟨z,hz,he⟩ := hx
      refine ⟨⟨z,hmA hz⟩,hz,?_⟩
      apply Subtype.ext
      exact he
  let jq : (otherCore r ⧸ otherZ r) ≃* (Q ⧸ Z.subgroupOf Q) :=
    QuotientGroup.congr (otherZ r) (Z.subgroupOf Q) j hjZ
  let jz : markedCore r ≃* Z.subgroupOf Q :=
    (subgroupOfEquivOfLe hmA).symm.trans
      ((j.subgroupMap (otherZ r)).trans (MulEquiv.subgroupCongr hjZ))
  have hjz (z : markedCore r) : (((jz z : Z.subgroupOf Q) : Q) : D) = k z := rfl
  let s : (Q ⧸ Z.subgroupOf Q) →* Z.subgroupOf Q :=
    jz.toMonoidHom.comp ((squareMap r).comp jq.symm.toMonoidHom)
  have hs (q : Q) : (((s (QuotientGroup.mk' (Z.subgroupOf Q) q) : Z.subgroupOf Q) : Q) : D) =
      (q : D)^2 := by
    obtain ⟨x,rfl⟩ := j.surjective q
    have he : jq.symm (QuotientGroup.mk' (Z.subgroupOf Q) (j x)) =
        QuotientGroup.mk' (otherZ r) x := by
      apply jq.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    change (((jz (squareMap r (jq.symm (QuotientGroup.mk' (Z.subgroupOf Q) (j x)))) :
      Z.subgroupOf Q) : Q) : D) = _
    rw [he,hjz,squareMap_mk,hj,map_pow]
  let : IsElementaryAbelian 2 (Q ⧸ Z.subgroupOf Q) := {
    is_comm := ⟨fun a b => jq.symm.injective (by
      rw [map_mul,map_mul]
      exact mul_comm _ _)⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply jq.symm.injective
      rw [map_pow,map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (otherCore r ⧸ otherZ r)) _) }
  obtain ⟨ρ,hρ⟩ := SourceRigidity.quotient_conjugation_action_of_normal Q Z
  refine SourceRigidity.nonsplit_third_branch_eq H Q Z hQH hZQ ?_ ?_ ?_ ?_ ρ hρ hchain s ?_ ?_
  · exact (Nat.card_congr j.toEquiv).symm.trans (otherCore_card r)
  · exact first_card r
  · exact (Nat.card_congr jq.toEquiv).symm.trans (quotient_card r)
  · rw [hZ,card_map_of_injective hk]
    exact (Nat.card_congr (markedEquiv r).toEquiv).trans
      Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic.card_distinguished
  · exact jz.surjective.comp ((squareMap_surjective r).comp jq.symm.surjective)
  · intro a x
    obtain ⟨d,rfl⟩ := QuotientGroup.mk'_surjective Q a
    obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf Q) x
    apply Subtype.ext
    apply Subtype.ext
    rw [hρ,hs,hs]
    change (d * (q : D) * d⁻¹)^2=(q : D)^2
    have hz : (q : D)^2 ∈ Z := (hs q) ▸ (s (QuotientGroup.mk' (Z.subgroupOf Q) q)).property
    calc
      (d * (q : D) * d⁻¹)^2 = d * (q : D)^2 * d⁻¹ := (map_pow (MulAut.conj d) (q : D) 2).symm
      _ = (q : D)^2 := by
        rw [mem_center_iff.mp (hZcentral hz) d, mul_assoc, mul_inv_cancel, mul_one]

/-- The actual source core either equals the nonsplit order-sixteen core,
which forces equality, or its marked quaternion base is normal in the larger
characteristic-two group. No elementary preimage is postulated. -/
theorem normal_quaternion_or_eq
    (H : Subgroup D) {α : RankTwoAmalgam H B R}
    (r : RankTwoAmalgam.Iso α ChapterF.GreenBook.AutMathieuTwelve.autAmalgam)
    (S : Sylow 2 D) (hSH : (S : Subgroup D) ≤ H)
    (hZcentral : (markedCore r).map (H.subtype.comp (pCore 2 H).subtype) ≤ center D)
    (hc : centralizer (pCore 2 D : Set D) ≤ pCore 2 D) :
    H = ⊤ ∨ ((FourWreathTwo.base.comap (wreathMap r)).map
      (H.subtype.comp (pCore 2 H).subtype)).Normal := by
  let QH := (pCore 2 H).map H.subtype
  let k : pCore 2 H →* D := H.subtype.comp (pCore 2 H).subtype
  let Z := (markedCore r).map k
  let QK := (FourWreathTwo.base.comap (wreathMap r)).map k
  let A := (otherCore r).map k
  let : Z.Normal := ⟨fun a ha b => by
    rw [mem_center_iff.mp (hZcentral ha) b,mul_assoc,mul_inv_cancel,mul_one]
    exact ha⟩
  have hZQ : Z ≤ pCore 2 D := (hZcentral.trans (center_le_centralizer _)).trans hc
  have hQQH : pCore 2 D ≤ QH := by
    have hQH : pCore 2 D ≤ H := (pCore_isPGroup.le_sylow_of_normal S).trans hSH
    have hpre : (pCore 2 D).comap H.subtype ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective H.subtype H.subtype_injective⟩
    simpa only [map_comap_eq_self (show pCore 2 D ≤ H.subtype.range by
      simpa only [range_subtype] using hQH)] using map_mono (f := H.subtype) hpre
  let j : pCore 2 H ≃* QH := (pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let f : QH →* FourWreathTwo.Wreath := (wreathMap r).comp j.symm.toMonoidHom
  have hj (x : pCore 2 H) : (j x : D) = k x := rfl
  have hfj : f.comp j.toMonoidHom = wreathMap r := by
    apply MonoidHom.ext
    intro x
    exact congrArg (wreathMap r) (j.symm_apply_apply x)
  have hf : Function.Surjective f := (wreathMap_surjective r).comp j.symm.surjective
  have hker : f.ker = Z.subgroupOf QH := by
    ext x
    obtain ⟨a,rfl⟩ := j.surjective x
    change f (j a) = 1 ↔ (j a : D) ∈ Z
    rw [show f (j a) = wreathMap r a from DFunLike.congr_fun hfj a,hj]
    rw [←MonoidHom.mem_ker,wreathMap_ker]
    constructor
    · exact mem_map_of_mem k
    · rintro ⟨z,hz,he⟩
      have hk : Function.Injective k := H.subtype_injective.comp (pCore 2 H).subtype_injective
      exact hk he ▸ hz
  have hmap (W : Subgroup FourWreathTwo.Wreath) :
      (W.comap f).map QH.subtype = (W.comap (wreathMap r)).map k := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      obtain ⟨b,rfl⟩ := j.surjective a
      refine ⟨b,?_,rfl⟩
      change wreathMap r b ∈ W
      change f (j b) ∈ W at ha
      rwa [show f (j b) = wreathMap r b from DFunLike.congr_fun hfj b] at ha
    · rintro ⟨a,ha,rfl⟩
      refine ⟨j a,?_,rfl⟩
      change f (j a) ∈ W
      rw [show f (j a) = wreathMap r a from DFunLike.congr_fun hfj a]
      exact ha
  let h : D := (cubic r : H)
  have hn : h ∈ normalizer (QH : Set D) := by
    apply (pCore 2 H).le_normalizer_map H.subtype
    exact ⟨cubic r,by rw [normalizer_eq_top]; trivial,rfl⟩
  have hact (x : QH) :
      f ⟨h * (x : D) * h⁻¹,(hn x).mp x.property⟩ = FourWreathTwo.cubic (f x) := by
    obtain ⟨a,rfl⟩ := j.surjective x
    have he : (⟨h * (j a : D) * h⁻¹,(hn (j a)).mp (j a).property⟩ : QH) =
        j (MulAut.conjNormal (cubic r) a) := by apply Subtype.ext; rfl
    rw [he]
    change wreathMap r (j.symm (j (MulAut.conjNormal (cubic r) a))) =
      FourWreathTwo.cubic (wreathMap r (j.symm (j a)))
    rw [j.symm_apply_apply,j.symm_apply_apply]
    exact cubic_conjugation r a
  have hchain := centralizer_image_pCore_le_of_central_quotient Z hZcentral hc
  obtain hwhole | hbase | hother := SourceCoreAction.core_trichotomy_with_relative_normality
    Z (pCore 2 D) QH QK A hZQ hQQH f hf hker (hmap _).symm (hmap _).symm h hn hact hchain
  · exact Or.inr hwhole.2
  · exact Or.inr hbase.2
  · exact Or.inl (nonsplit_rigidity H (pCore 2 D) Z r hother rfl hZcentral hchain)

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity
end

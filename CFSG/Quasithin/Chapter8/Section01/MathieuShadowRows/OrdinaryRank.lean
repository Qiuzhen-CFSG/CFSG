module
public import Theory.Representation.PSL3Four.SmallTwoGroupAction
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.PointNative
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Binary rank of an ordinary component above the original point residual

The actual PSL₃(4) action on the moved elementary module descends to its
image in any containing central quotient. It remains nontrivial, because
the original residual moves the whole module. The binary degree-nine gap
therefore gives rank at least nine in that central quotient. The original
module may meet the containing center; its full kernel is retained.

Source: Aschbacher--Smith C.3.1 and 8.1.1, pp.149,712, with the proved
PSL₃(4) degree theorem (GLS III §§2.8.6--10).
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Matrix.PSL3Four

/-- The actual moved module gives a degree-nine elementary image in a
containing central quotient, through its original point-action map. -/
theorem point_residual_elementary_image_card
    {G : Type*} [Group G] [Finite G]
    (F K W : Subgroup G) [IsElementaryAbelian 2 W]
    (hFK : F ≤ K) (hWF : W ≤ F) (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (f : F →* PSL) (hf : Function.Surjective f)
    (hker : f.ker ≤ (centralizer (W : Set G)).subgroupOf F) :
    512 ≤ Nat.card ((W.subgroupOf K).map (QuotientGroup.mk' (center K))) := by
  let q := QuotientGroup.mk' (center K)
  let A := F.subgroupOf K
  let U := W.subgroupOf K
  have hWK := hWF.trans hFK
  let w : U ≃* W := subgroupOfEquivOfLe hWK
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf (hWF.trans hFK)
  let E := U.map q
  let B := A.map q
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hmove : E = ⁅E,B⁆ := by
    change U.map q = ⁅U.map q,A.map q⁆
    rw [←map_commutator]
    apply congrArg (map q)
    apply map_injective K.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWK,map_subgroupOf_eq_of_le hFK]
    exact hcomm
  have hEne : E ≠ ⊥ := by
    intro hb
    have hc : U ≤ center K := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff U).mp hb
    have hWC : W ≤ centralizer (F : Set G) := by
      intro v hv f hf
      exact congrArg K.subtype (mem_center_iff.mp (hc (show (⟨v,hWK hv⟩ : K) ∈ U from hv))
        ⟨f,hFK hf⟩)
    exact hne (hcomm.trans (commutator_eq_bot_iff_le_centralizer.mpr hWC))
  let r : F →* (K ⧸ center K) := q.comp (inclusion hFK)
  have hr : r.range = B := by
    rw [MonoidHom.range_comp]
    congr 1
    ext k
    constructor
    · rintro ⟨f,rfl⟩; exact f.property
    · intro hk; exact ⟨⟨k,hk⟩,rfl⟩
  have hn : B ≤ normalizer (E : Set (K ⧸ center K)) :=
    le_normalizer_iff_commutator_le_left.mpr hmove.symm.le
  let t : F →* normalizer (E : Set (K ⧸ center K)) := r.codRestrict _
    (fun f => hn (hr ▸ (show r f ∈ r.range from ⟨f,rfl⟩)))
  let act : F →* MulAut E := E.normalizerMonoidHom.comp t
  have hact : act ≠ 1 := by
    intro he
    apply hEne
    rw [hmove]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro v hv b hb
    obtain ⟨f,hf⟩ := hr.symm ▸ hb
    have hh := congrArg (fun z : MulAut E => ((z ⟨v,hv⟩ : E) : K ⧸ center K))
      (DFunLike.congr_fun he f)
    change r f * v * (r f)⁻¹ = v at hh
    rw [mul_inv_eq_iff_eq_mul] at hh
    simpa only [hf] using hh
  have hkill : f.ker ≤ act.ker := by
    intro c hc
    apply MulEquiv.ext
    intro v
    obtain ⟨w,hw,hwv⟩ := v.property
    apply Subtype.ext
    change r c * (v : K ⧸ center K) * (r c)⁻¹ = (v : K ⧸ center K)
    rw [←hwv]
    change q (inclusion hFK c) * q w * (q (inclusion hFK c))⁻¹ = q w
    rw [←map_inv,←map_mul,←map_mul]
    apply congrArg q
    apply Subtype.ext
    change (c : G) * (w : G) * (c : G)⁻¹ = (w : G)
    rw [mul_inv_eq_iff_eq_mul]
    exact (mem_centralizer_iff.mp (hker hc) w hw).symm
  let b : PSL →* MulAut E := f.liftOfSurjective hf ⟨act,hkill⟩
  have hb (c : F) : b (f c) = act c := f.liftOfRightInverse_comp_apply _ _ _ c
  have hbne : b ≠ 1 := by
    intro he
    apply hact
    ext c
    rw [←hb,he]
    rfl
  obtain ⟨c,hc⟩ : ∃ c, b c ≠ 1 := by
    by_contra! hn
    exact hbne (MonoidHom.ext hn)
  let ρ := FrattiniAction.ofAutomorphismHom b
  have hr : ∃ c, ρ c ≠ 1 := by
    by_contra! hn
    exact FrattiniAction.ofAutomorphismHom_ne_one b c hc (MonoidHom.ext hn)
  have hp : pCore 2 PSL = ⊥ := by
    have hz : center PSL = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot
      (Matrix.SpecialLinearGroup (Fin 3) Matrix.PSL3Four.F)
    exact le_bot_iff.mp ((IsQuasisimple.pCore_le_center 2).trans_eq hz)
  let e : (PSL ⧸ pCore 2 PSL) ≃* PSL :=
    (QuotientGroup.quotientMulEquivOfEq hp).trans QuotientGroup.quotientBot
  have hd := Representation.PSL3Four.perfect_core_quotient_finrank_ge_nine
    e Matrix.PSL3Four.card_F ρ hr
  have hcard : Nat.card E = 2 ^ Module.finrank (ZMod 2) (Additive E) := by
    change Nat.card (Additive E) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E))
  change 512 ≤ Nat.card E
  rw [hcard]
  exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hd

/-- The same original module supplies the rank required in the ordinary
field-four component sieve. -/
theorem point_residual_central_quotient_twoRank
    {G : Type*} [Group G] [Finite G]
    (F K W : Subgroup G) [IsElementaryAbelian 2 W]
    (hFK : F ≤ K) (hWF : W ≤ F) (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (f : F →* PSL) (hf : Function.Surjective f)
    (hker : f.ker ≤ (centralizer (W : Set G)).subgroupOf F) :
    9 ≤ primeRank 2 (K ⧸ center K) := by
  let U := W.subgroupOf K
  let w : U ≃* W := subgroupOfEquivOfLe (hWF.trans hFK)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf (hWF.trans hFK)
  let E := U.map (QuotientGroup.mk' (center K))
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hl := point_residual_elementary_image_card F K W hFK hWF hne hcomm f hf hker
  by_contra hb
  have hc : Nat.card E ≤ 2^8 :=
    (primeRank_le_iff_elementary_card_le (K ⧸ center K)).mp (by omega) E inferInstance
  change 512 ≤ Nat.card E at hl
  norm_num at hc
  omega

end CFSG.Quasithin.Chapter8.MathieuShadowRows

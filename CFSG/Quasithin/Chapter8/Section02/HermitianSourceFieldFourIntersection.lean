module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourWeakImage

/-!
# Strict intersections in the field-four zero-closure case

The plane radical acts quadratically on the eight-dimensional Hermitian
hyperplane with bottom diagonal coordinate zero: every displacement lies
in its rank-four fixed space. If this fixed subgroup lay in a returning
whole conjugate, that entire hyperplane would normalize the conjugate.
The checked reverse-normalizer bound of five excludes such containment.

Consequently every moving whole conjugate meets V in rank at most three.
Its full centralizer kernel still has rank five, so adjoining that kernel
to V gives an elementary subgroup of the original Sylow of rank at least
eleven. The companion Chapter 12 module applies this to the literal chosen
orbit and half-field tensor. These restrictions do not yet exclude zero
closure or establish the normalizer/centralizer argument through 8.2.13.

Source: the Hermitian coordinates and paired-action argument in
Aschbacher--Smith H.4.2--5, E.3.28--32 and 7.5.6, printed pp.380--382,
237--238,701; refs/quasithin.pdf (1 March 2004 manuscript).
-/


open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Matrix.PSL3Even.UnipotentGeometry
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE
public noncomputable section

private theorem plane_displacement_fixed (a b : F 1) (u v w : E 1)
    (q : Space 1 ≃ₗ[ZMod 2] Space 1) (hq : q ∈ UnipotentRadicals.plane 1) :
    q ((HermitianTensorThree.coordinates 1).symm (![a,b,0], ![u,v,w])) -
      (HermitianTensorThree.coordinates 1).symm (![a,b,0], ![u,v,w]) ∈
        fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.plane 1) := by
  obtain ⟨z,hz,rfl⟩ := hq
  have hx : z.x = 0 := (mem_V₂ (E 1) z).mp hz
  apply (UnipotentRadicals.mem_plane_fixed_iff 1 _).mpr
  let X := (HermitianTensorThree.coordinates 1).symm (![a,b,0], ![u,v,w])
  change (matrix (E 1) z * X.val * adjoint 1 (matrix (E 1) z)) 2 2 - X.val 2 2 = 0 ∧
    (matrix (E 1) z * X.val * adjoint 1 (matrix (E 1) z)) 1 2 - X.val 1 2 = 0 ∧
    (matrix (E 1) z * X.val * adjoint 1 (matrix (E 1) z)) 0 2 - X.val 0 2 = 0
  simp [X,HermitianTensorThree.coordinates,matrix,hx,adjoint,Matrix.mul_apply,
    Fin.sum_univ_three]

private theorem normalizes_of_displacement_fixed
    {G : Type*} [Group G] [Finite G]
    (V W : Subgroup G) [IsElementaryAbelian 2 V]
    (hWN : W ≤ normalizer (V : Set G))
    (hUW : V ⊓ centralizer (W : Set G) ≤ W)
    (x : Additive V)
    (hx : ∀ w : W, automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict ⟨w.val,hWN w.property⟩) x - x ∈
        fixedSpace (automizerRepresentation V) (inducedAutomizer V W)) :
    (x.toMul : G) ∈ normalizer (W : Set G) := by
  have hc (w : G) (hw : w ∈ W) : ⁅w,(x.toMul : G)⁆ ∈ W := by
    let y := automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict ⟨w,hWN hw⟩) x - x
    have hy : (y.toMul : G) ∈ V ⊓ centralizer (W : Set G) :=
      ⟨y.toMul.property,(mem_fixedSpace_inducedAutomizer V W hWN y).mp (hx ⟨w,hw⟩)⟩
    change w * (x.toMul : G) * w⁻¹ / (x.toMul : G) ∈ _ at hy
    simpa only [div_eq_mul_inv,commutatorElement_def] using hUW hy
  have hi : (x.toMul : G)⁻¹ = (x.toMul : G) := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (A := V) (p := 2)
      (x.toMul : G) x.toMul.property
  have hconj (w : G) (hw : w ∈ W) : (x.toMul : G) * w * (x.toMul : G)⁻¹ ∈ W := by
    have hh := W.mul_mem (W.inv_mem (hc w hw)) hw
    simpa only [commutatorElement_def,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,
      mul_one] using hh
  apply mem_normalizer_iff.mpr
  intro w
  refine ⟨hconj w,fun hw => ?_⟩
  have hh := hconj _ hw
  have heq : (x.toMul : G) * ((x.toMul : G) * w * (x.toMul : G)⁻¹) *
      (x.toMul : G)⁻¹ = w := by
    calc
      _ = ((x.toMul : G)⁻¹ * (x.toMul : G)) * w *
          ((x.toMul : G)⁻¹ * (x.toMul : G)) := by rw [hi]; group
      _ = w := by simp
  rwa [heq] at hh

variable {G : Type*} [Group G] [Finite G]
  (V : Subgroup G) [IsElementaryAbelian 2 V]
  (e : Additive V ≃ₗ[ZMod 2] Space 1)
  (j : Automizer V →* binaryNormalizer 1) (hj : Function.Injective j)
  (he : ∀ a v, e (automizerRepresentation V a v) =
    overgroupAction 1 (binaryNormalizer 1) (j a) (e v))

include hj he in
/-- Containment of the plane's fixed subgroup in the acting subgroup forces
an eight-dimensional subgroup into the reverse normalizer. -/
theorem field_four_reverse_rank_ge_eight_of_fixed_le
    (W : Subgroup G) (hWN : W ≤ normalizer (V : Set G))
    (hW : inducedAutomizer V W ∈ fixedSpaceFamily (automizerRepresentation V) 3)
    (hUW : V ⊓ centralizer (W : Set G) ≤ W) :
    8 ≤ rank (V ⊓ normalizer (W : Set G)) := by
  obtain ⟨_,_,c,hc⟩ := field_four_third_family_plane V e j hj he _ hW
  let d := binaryActionHom 1 c
  let e' := e.trans d
  let f := (binaryNormalizer 1).subtype.comp j
  let l := (MulAut.conj d).toMonoidHom.comp f
  have him : (inducedAutomizer V W).map l = UnipotentRadicals.plane 1 := by
    rw [←map_map]
    exact hc
  have he' (a : Automizer V) (v : Additive V) :
      e' (automizerRepresentation V a v) = l a (e' v) := by
    change d (e (automizerRepresentation V a v)) = d (f a (d.symm (d (e v))))
    rw [d.symm_apply_apply]
    exact congrArg d (he a v)
  have hfixed (y : Additive V)
      (hy : e' y ∈ fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.plane 1)) :
      y ∈ fixedSpace (automizerRepresentation V) (inducedAutomizer V W) := by
    intro a
    apply e'.injective
    change e' (automizerRepresentation V a.val y) = e' y
    rw [he']
    exact hy ⟨l a.val,him ▸ mem_map_of_mem l a.property⟩
  let coords (z : (F 1 × F 1) × (Fin 3 → E 1)) :=
    (HermitianTensorThree.coordinates 1).symm
      (![z.1.1,z.1.2,0], ![z.2 0,z.2 1,z.2 2])
  have hnorm (z : (F 1 × F 1) × (Fin 3 → E 1)) :
      ((e'.symm (coords z)).toMul : G) ∈ normalizer (W : Set G) := by
    apply normalizes_of_displacement_fixed V W hWN hUW
    intro w
    apply hfixed
    rw [map_sub,he',e'.apply_symm_apply]
    exact plane_displacement_fixed _ _ _ _ _ _ (him ▸
      mem_map_of_mem l (mem_map_of_mem V.normalizerMonoidHom.rangeRestrict w.property))
  let k : ((F 1 × F 1) × (Fin 3 → E 1)) → (V ⊓ normalizer (W : Set G) : Subgroup G) :=
    fun z => ⟨(e'.symm (coords z)).toMul,
      (e'.symm (coords z)).toMul.property,hnorm z⟩
  have hk : Function.Injective k := by
    intro x y hxy
    have hv : (e'.symm (coords x)).toMul = (e'.symm (coords y)).toMul :=
      Subtype.ext (congrArg (fun z : (V ⊓ normalizer (W : Set G) : Subgroup G) => (z : G)) hxy)
    have hh := congrArg (fun a => HermitianTensorThree.coordinates 1 (e' (Additive.ofMul a))) hv
    change HermitianTensorThree.coordinates 1 (e' (e'.symm (coords x))) =
      HermitianTensorThree.coordinates 1 (e' (e'.symm (coords y))) at hh
    simp only [e'.apply_symm_apply,coords,LinearEquiv.apply_symm_apply] at hh
    apply Prod.ext
    · exact Prod.ext (congrArg (fun z => z.1 0) hh) (congrArg (fun z => z.1 1) hh)
    · ext i
      fin_cases i
      · exact congrArg (fun z => z.2 0) hh
      · exact congrArg (fun z => z.2 1) hh
      · exact congrArg (fun z => z.2 2) hh
  have hcard := Nat.card_le_card_of_injective k hk
  simp only [Nat.card_prod,Nat.card_fun,Nat.card_fin,card_F,card_E] at hcard
  have hlog := Nat.log_mono_right (b := 2) hcard
  norm_num at hlog
  exact hlog

include hj he in
/-- A moving whole conjugate in the zero branch cannot contain its
rank-four fixed subgroup. -/
theorem field_four_zero_fixed_not_le_return
    (T : Sylow 2 G) (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hr : 3 ≤ globalR V) (hm : 3 ≤ localM V) (hw : globalW V T = 0)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hmove : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    ¬ V ⊓ centralizer (indexedWeakClosure V T 0 : Set G) ≤
      V.map (MulAut.conj g).toMonoidHom := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hWN : W ≤ normalizer (V : Set G) := hg.trans hT.normalizes
  have hA : offenderNormalizer V g = W := inf_eq_left.mpr hWN
  have hOff : IsWOffenderAt V T g := by
    refine ⟨?_,?_⟩
    · intro hc
      exact hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
    · rw [hA,hw]
      simp [subgroupCorank,W]
  have hs := (field_four_zero_weak_closure V e j hj he T hT hFF hr hm hw).2.1
  have hf := (offender_fixedSpaceFamily_of_lt_globalS hOff (by rw [hw,hs]; decide)).2
  rw [hw,hs,hA] at hf
  obtain ⟨hfix,_⟩ := field_four_third_family_fixed_normal V e j hj he T hT W hg hf
  have hWr : rank W = 9 := by
    rw [rank_map_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hAr := (field_four_fixed_family_three_rank V e j hj he _ hf).1
  have hsum := offender_corank_add (W := W) (A := W ⊓ centralizer (V : Set G)) bot_le inf_le_left
  have hsum' : rank W = rank (inducedAutomizer V W) + rank (W ⊓ centralizer (V : Set G)) := by
    rw [rank_inducedAutomizer V W hWN]
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hsum
  have hker : 5 ≤ rank (W ⊓ centralizer (V : Set G)) := by omega
  have hupper := field_four_reverse_normalizer_rank V e j hj he g hWN hfix hker
  intro hu
  have hUeq := (field_four_zero_closure_fixed V e j hj he T hT hFF hr hm hw).2.2 g hg hmove
  rw [←hUeq] at hu
  have hlower := field_four_reverse_rank_ge_eight_of_fixed_le V e j hj he W hWN hf hu
  change 8 ≤ rank (V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) at hlower
  omega

private theorem elementary_card_pow_rank (A : Subgroup G) [IsElementaryAbelian 2 A] :
    Nat.card A = 2 ^ rank A := by
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [rank,hk,Nat.log_pow Nat.one_lt_two]

include hj he in
/-- Every moving whole conjugate intersects V in rank at most three;
the common rank-four fixed subgroup is never their intersection. -/
theorem field_four_zero_intersection_rank
    (T : Sylow 2 G) (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hr : 3 ≤ globalR V) (hm : 3 ≤ localM V) (hw : globalW V T = 0)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hmove : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    rank (V ⊓ V.map (MulAut.conj g).toMonoidHom) ≤ 3 := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let U := V ⊓ centralizer (indexedWeakClosure V T 0 : Set G)
  let J := V ⊓ W
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ V from inf_le_left)
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.of_le (show J ≤ V from inf_le_left)
  obtain ⟨hu,_,hfix⟩ := field_four_zero_closure_fixed V e j hj he T hT hFF hr hm hw
  have hJU : J ≤ U := by
    change V ⊓ W ≤ V ⊓ centralizer (indexedWeakClosure V T 0 : Set G)
    rw [←hfix g hg hmove]
    exact le_inf inf_le_left (inf_le_right.trans W.le_centralizer)
  have hle : rank J ≤ 4 :=
    (Nat.log_mono_right (Nat.card_le_card_of_injective (inclusion hJU)
      (inclusion_injective hJU))).trans_eq hu
  have hne : rank J ≠ 4 := by
    intro hj4
    have hcard : Nat.card U ≤ Nat.card J := by
      rw [elementary_card_pow_rank U,elementary_card_pow_rank J,hj4]
      change rank U = 4 at hu
      rw [hu]
    have heq : J = U := eq_of_le_of_card_ge hJU hcard
    have hUW : U ≤ W := heq ▸ (show J ≤ W from inf_le_right)
    exact field_four_zero_fixed_not_le_return V e j hj he T hT hFF hr hm hw g hg hmove hUW
  change rank J ≤ 3
  omega

include hj he in
/-- The full rank-five kernel and the strict intersection bound force
an elementary subgroup of the original Sylow of rank at least eleven. -/
theorem field_four_zero_sylow_rank_ge_eleven
    (T : Sylow 2 G) (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hr : 3 ≤ globalR V) (hm : 3 ≤ localM V) (hw : globalW V T = 0) :
    11 ≤ primeRank 2 T := by
  obtain ⟨_,_,g,hg,hOff,_,_,hker⟩ := field_four_zero_weak_closure
    V e j hj he T hT hFF hr hm hw
  let W := V.map (MulAut.conj g).toMonoidHom
  let K := W ⊓ centralizer (V : Set G)
  let J := V ⊔ K
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le (show K ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  let : IsElementaryAbelian 2 (V ⊓ K : Subgroup G) := IsElementaryAbelian.of_le
    (show V ⊓ K ≤ V from inf_le_left)
  have hmove : ¬ W ≤ centralizer (V : Set G) := by
    intro hc
    exact hOff.1 (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  have hinter := field_four_zero_intersection_rank V e j hj he T hT hFF hr hm hw g hg hmove
  have hVK : V ⊓ K = V ⊓ W := by
    apply le_antisymm (inf_le_inf_left V inf_le_left)
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans V.le_centralizer))
  have hdim : rank V = 9 := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes V K
    ((show K ≤ centralizer (V : Set G) from inf_le_right).trans
      (Subgroup.centralizer_le_normalizer _))
  rw [elementary_card_pow_rank V,elementary_card_pow_rank K,
    elementary_card_pow_rank (V ⊓ K),elementary_card_pow_rank (V ⊔ K),
    ←pow_add,←pow_add] at hc
  have hadd := Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  change rank K = 5 at hker
  change rank V + rank K = rank (V ⊓ K) + rank J at hadd
  rw [hVK,hdim,hker] at hadd
  change rank (V ⊓ W) ≤ 3 at hinter
  have hJrank : 11 ≤ rank J := by omega
  have hJT : J ≤ T := sup_le hT.le_sylow (inf_le_left.trans hg)
  let : IsElementaryAbelian 2 (J.subgroupOf T) := IsElementaryAbelian.subgroupOf hJT
  have hsub : rank (J.subgroupOf T) = rank J :=
    congrArg (Nat.log 2) (Nat.card_congr (subgroupOfEquivOfLe hJT).toEquiv)
  have hb := offender_rank_le_primeRank (J.subgroupOf T)
  rw [hsub] at hb
  exact hJrank.trans hb

end
end CFSG.Quasithin.Chapter8.Section02.HermitianSource

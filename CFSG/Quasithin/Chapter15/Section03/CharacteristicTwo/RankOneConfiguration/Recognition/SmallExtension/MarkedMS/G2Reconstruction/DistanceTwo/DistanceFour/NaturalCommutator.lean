module
public import Theory.Representation.FirstCohomologyG2Natural.Commutant
public import Theory.ThreeSubgroups
public import Theory.Representation.G2BinaryPointFlagDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Pairing
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Pairing
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour.Radius

/-!
# The order-two bound in the fixed-derived G₂ radius branch

Suppose the derived radius is fixed by the vertex residual. The relative
three-subgroups lemma and residual commutator idempotence give
[Vcirc,V] = [Vcirc,Vcirc], without a separate supplement decomposition.
If the whole central quotient Vcirc/Z(Vcirc) is the natural six-space for
the literal residual actor, its derived subgroup has at most two elements.

For the latter bound, the proved scalar commutant makes every invariant
bilinear form a multiple of the octonion polar form. Scalar specializations
of the actual commutator pairing therefore inject the dual of the derived
subgroup into F₂. This bounds the whole derived subgroup, including central
attachments. The existing critical-radius lower bound is eight.

The fixed-derived hypothesis and the whole moving central-quotient marking
remain source obligations of qt-e-ms-small-g2-reconstruction. This module
proves their order-two consequence, not their existence or C.1.32 itself.
The internal pairing constructor is reused with `import all`; its private
name does not occur in any public statement.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(3.8), printed pp.878--879; Aschbacher--Smith C.1.31--32, pp.135--136.
The octonion commutant uses the attributed ATLAS port; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour
open ChapterC BinaryMS.MS93 BinaryMS.MS93.NaturalStructure.Exclusion
private abbrev W := Fin 6 → ZMod 2
private abbrev rho := Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2)
private abbrev polar := Atlas.G2.Natural.BinaryPointFlag.pairing

private theorem polar_ext {v w : W} (h : ∀ x, polar v x = polar w x) : v = w := by
  have h0 := h (Pi.single 0 1)
  have h1 := h (Pi.single 1 1)
  have h2 := h (Pi.single 2 1)
  have h3 := h (Pi.single 3 1)
  have h4 := h (Pi.single 4 1)
  have h5 := h (Pi.single 5 1)
  simp only [Atlas.G2.Natural.BinaryPointFlag.pairing_apply, Pi.single_apply] at *
  ext i
  fin_cases i <;> simp_all

private theorem invariant_form_scalar (B : LinearMap.BilinForm (ZMod 2) W)
    (hi : ∀ (g : commutator (Atlas.G2.Model (ZMod 2))) v w,
      B (rho g.val v) (rho g.val w) = B v w) :
    ∃ c : ZMod 2, ∀ v w, B v w = c * polar v w := by
  let f : W →+ W := {
    toFun v := ![B v (Pi.single 5 1), B v (Pi.single 4 1), B v (Pi.single 3 1),
      B v (Pi.single 2 1), B v (Pi.single 1 1), B v (Pi.single 0 1)]
    map_zero' := by ext i; fin_cases i <;> simp
    map_add' v w := by ext i; fin_cases i <;> simp }
  have hf (v w : W) : polar (f v) w = B v w := by
    have hw : w = ∑ i : Fin 6, w i • Pi.single i (1 : ZMod 2) := by
      ext i
      rw [Fin.sum_univ_six]
      fin_cases i <;> simp
    conv_rhs => rw [hw]
    simp [f, Atlas.G2.Natural.BinaryPointFlag.pairing_apply, Fin.sum_univ_six]
    ring
  have hcomm (g : commutator (Atlas.G2.Model (ZMod 2))) (v : W) :
      f (rho g.val v) = rho g.val (f v) := by
    apply polar_ext
    intro w
    obtain ⟨w, rfl⟩ := (rho.apply_bijective g.val).2 w
    rw [hf, hi, Atlas.G2.Natural.BinaryPointFlag.pairing_invariant, hf]
  obtain ⟨c,hc⟩ := Atlas.G2.Natural.Commutant.coordinate_additive_commutant_scalar f hcomm
  refine ⟨c, fun v w => ?_⟩
  rw [←hf,hc,map_smul,LinearMap.smul_apply]
  rfl

private theorem invariant_form_zero (B : LinearMap.BilinForm (ZMod 2) W)
    (hi : ∀ (g : commutator (Atlas.G2.Model (ZMod 2))) v w,
      B (rho g.val v) (rho g.val w) = B v w)
    (hz : B (Pi.single 0 1) (Pi.single 5 1) = 0) : B = 0 := by
  obtain ⟨c,hc⟩ := invariant_form_scalar B hi
  have hc0 : c = 0 := by
    simpa [hc,Atlas.G2.Natural.BinaryPointFlag.pairing_apply] using hz
  ext v w
  simp [hc,hc0]

private theorem central_quotient_derived_bound
    {P : Type*} [Group P] [Finite P] [IsElementaryAbelian 2 (P ⧸ center P)]
    (e : Additive (P ⧸ center P) ≃ₗ[ZMod 2] W)
    (hlift : ∀ g : commutator (Atlas.G2.Model (ZMod 2)), ∃ a : MulAut P,
      (∀ d : commutator P, a d = d) ∧
      ∀ v, e (Additive.ofMul (quotientAut (center P) a v.toMul)) = rho g.val (e v)) :
    Nat.card (commutator P) ≤ 2 := by
  let hq : IsElementaryAbelian 2 (P ⧸ center P) := inferInstance
  let := hq.derived_of_central_quotient
  obtain ⟨pairing, heval⟩ := exists_derived_pairing hq.commutator_le_center_of_central_quotient
  let scalar (f : Module.Dual (ZMod 2) (Additive (commutator P))) :
      LinearMap.BilinForm (ZMod 2) W :=
    AddMonoidHom.toZModLinearMap 2 {
      toFun := fun v => AddMonoidHom.toZModLinearMap 2 {
        toFun := fun w => f (Additive.ofMul (pairing (e.symm v).toMul (e.symm w).toMul))
        map_zero' := by simp
        map_add' := by intros; simp }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hinv (f : Module.Dual (ZMod 2) (Additive (commutator P)))
      (g : commutator (Atlas.G2.Model (ZMod 2))) (v w : W) :
      scalar f (rho g.val v) (rho g.val w) = scalar f v w := by
    obtain ⟨a,ha,he⟩ := hlift g
    have htransport (v : W) :
        (e.symm (rho g.val v)).toMul = quotientAut (center P) a (e.symm v).toMul := by
      apply Additive.ofMul.injective
      apply e.injective
      simp only [ofMul_toMul,LinearEquiv.apply_symm_apply,he]
    change f (Additive.ofMul (pairing (e.symm (rho g.val v)).toMul
      (e.symm (rho g.val w)).toMul)) =
        f (Additive.ofMul (pairing (e.symm v).toMul (e.symm w).toMul))
    rw [htransport,htransport]
    congr 2
    apply Subtype.ext
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (center P) (e.symm v).toMul
    obtain ⟨y,hy⟩ := QuotientGroup.mk'_surjective (center P) (e.symm w).toMul
    rw [←hx,←hy,quotientAut_apply_mk,quotientAut_apply_mk,heval,heval,
      ←map_commutatorElement]
    exact ha ⟨⁅x,y⁆,commutator_mem_commutator (mem_top x) (mem_top y)⟩
  let ev : Module.Dual (ZMod 2) (Additive (commutator P)) →ₗ[ZMod 2] ZMod 2 := {
    toFun f := scalar f (Pi.single 0 1) (Pi.single 5 1)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hinj : Function.Injective ev := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro f hf
    have hzero : scalar f = 0 := invariant_form_zero _ (hinv f) hf
    let fm : commutator P →* Multiplicative (ZMod 2) :=
      AddMonoidHom.toMultiplicativeRight f.toAddMonoidHom
    have hk : commutator P ≤ fm.ker.map (commutator P).subtype := by
      change ⁅(⊤ : Subgroup P),⊤⁆ ≤ _
      apply commutator_le.mpr
      intro x _ y _
      let d : commutator P := ⟨⁅x,y⁆,commutator_mem_commutator (mem_top x) (mem_top y)⟩
      refine ⟨d,?_,rfl⟩
      have hz := congrArg (fun B : LinearMap.BilinForm (ZMod 2) W =>
        B (e (Additive.ofMul (QuotientGroup.mk' (center P) x)))
          (e (Additive.ofMul (QuotientGroup.mk' (center P) y)))) hzero
      change f (Additive.ofMul (pairing
        (e.symm (e (Additive.ofMul (QuotientGroup.mk' (center P) x)))).toMul
        (e.symm (e (Additive.ofMul (QuotientGroup.mk' (center P) y)))).toMul)) = 0 at hz
      simp only [LinearEquiv.symm_apply_apply,toMul_ofMul] at hz
      have heq : pairing (QuotientGroup.mk' (center P) x)
          (QuotientGroup.mk' (center P) y) = d := Subtype.ext (heval x y)
      rw [heq] at hz
      exact hz
    change f = 0
    ext d
    obtain ⟨k,hk,hkd⟩ := hk d.toMul.property
    have heq : k = d.toMul := Subtype.ext hkd
    subst k
    exact hk
  have hc := Nat.card_le_card_of_injective ev hinj
  rw [Nat.card_zmod] at hc
  have heq : Nat.card (Module.Dual (ZMod 2) (Additive (commutator P))) =
      Nat.card (commutator P) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Subspace.dual_finrank_eq,
      ←Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (commutator P))]
    rfl
  rwa [heq] at hc

open Stellmacher.PushingUp.AmalgamGraph
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => R.subgroupOf (L ⊔ R)

/-- In the fixed-derived branch the full moving commutator is already the
moving group's own derived subgroup. Only relative normality is used. -/
theorem moving_commutator_eq_derived_of_fixed
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (hb : 2 < (geometry h).b T) (a : Vertex T) (ha : color T a = false)
    (hfixed : ⁅V T a,V T a⁆ ≤ fixedCore T a) :
    ⁅Vcirc T a,V T a⁆ = ⁅Vcirc T a,Vcirc T a⁆ := by
  have hm : Vcirc T a ≤ V T a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have hV : V T a ≤ stabilizer T a :=
    ((geometry h).V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hn : stabilizer T a ≤ normalizer (⁅Vcirc T a,Vcirc T a⁆ : Subgroup (FreeAmalgam T)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (Vcirc_normalized a hx)]
  have hrot₁ : ⁅⁅Ltilde T a,V T a⁆,Vcirc T a⁆ ≤ ⁅Vcirc T a,Vcirc T a⁆ := by
    rw [commutator_comm (Ltilde T a) (V T a)]
    exact le_rfl
  have hrot₂ : ⁅⁅V T a,Vcirc T a⁆,Ltilde T a⁆ ≤ ⁅Vcirc T a,Vcirc T a⁆ := by
    have hf := (commutator_mono le_rfl hm).trans hfixed
    rw [commutator_eq_bot_iff_le_centralizer.mpr (hf.trans inf_le_right)]
    exact bot_le
  have hrot := commutator_commutator_le_of_rotate_of_le_normalizer
    ((hm.trans hV).trans hn) ((Ltilde_le_stabilizer a).trans hn) (hV.trans hn) hrot₁ hrot₂
  rw [moving_full_commutation h hb a ha] at hrot
  exact le_antisymm hrot (commutator_mono le_rfl hm)

/-- The literal moving central quotient is marked by six octonion coordinates.
The actor is the existing endpoint marking; only its residual is required. -/
structure MovingCentralModel (a : Vertex T) (d : Comparison.EndpointModel T a) where
  coordinates : ((Vcirc T a) ⧸ center (Vcirc T a)) ≃* Multiplicative (Fin 6 → ZMod 2)
  intertwines : ∀ (g : stabilizer T a), g ∈ pResidual 2 (stabilizer T a) → ∀ v,
    coordinates (movingQuotientAction a g v) =
      Multiplicative.ofAdd (Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2)
        (d.actor g) (coordinates v).toAdd)

/-- The natural central quotient bounds the actual moving commutator, including
all central attachments, when the derived radius is fixed by the residual. -/
theorem moving_commutator_card_le_two_of_natural
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (hb : 2 < (geometry h).b T) (a : Vertex T) (ha : color T a = false)
    (hfixed : ⁅V T a,V T a⁆ ≤ fixedCore T a)
    (d : Comparison.EndpointModel T a) (m : MovingCentralModel a d) :
    Nat.card (⁅Vcirc T a,V T a⁆ : Subgroup (FreeAmalgam T)) ≤ 2 := by
  let P := Vcirc T a
  let := finite_moving (geometry h) hb a ha
  let := moving_central_quotient_elementary (geometry h) (by omega) a ha hfixed
  let f : Additive (P ⧸ center P) →ₗ[ZMod 2] W :=
    (MonoidHom.toAdditiveLeft m.coordinates.toMonoidHom).toZModLinearMap 2
  let eP : Additive (P ⧸ center P) ≃ₗ[ZMod 2] W :=
    LinearEquiv.ofBijective f m.coordinates.bijective
  have hbnd : Nat.card (commutator P) ≤ 2 := by
    apply central_quotient_derived_bound eP
    intro g
    obtain ⟨s,hs,hsg⟩ := (show g.val ∈
        ((Ltilde T a).subgroupOf (stabilizer T a)).map d.actor from
      d.actor_residual.symm ▸ g.property)
    have hs' : s ∈ pResidual 2 (stabilizer T a) := by
      obtain ⟨k,hk,hks⟩ := hs
      have he : k = s := Subtype.ext hks
      exact he ▸ hk
    refine ⟨movingAction a s,?_,?_⟩
    · intro x
      apply Subtype.ext
      rw [movingAction_apply]
      have hx : (x.val.val : FreeAmalgam T) ∈ ⁅Vcirc T a,Vcirc T a⁆ := by
        rw [←map_subtype_commutator]
        exact mem_map_of_mem P.subtype x.property
      have hm : P ≤ V T a := le_normalizer_iff_commutator_le_left.mp
        ((Ltilde_le_stabilizer a).trans (V_normalized a))
      have hxf := hfixed (commutator_mono hm hm hx)
      have hsl : s.val ∈ Ltilde T a := mem_map_of_mem (stabilizer T a).subtype hs'
      rw [hxf.2 s.val hsl,mul_inv_cancel_right]
    · intro v
      have hi := congrArg Multiplicative.toAdd (m.intertwines s hs' v.toMul)
      change (m.coordinates (movingQuotientAction a s v.toMul)).toAdd =
        rho g.val (m.coordinates v.toMul).toAdd
      simpa only [toAdd_ofAdd,hsg] using hi
  rw [moving_commutator_eq_derived_of_fixed h hb a ha hfixed,
    ←map_subtype_commutator,card_map_of_injective (Vcirc T a).subtype_injective]
  exact hbnd

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour

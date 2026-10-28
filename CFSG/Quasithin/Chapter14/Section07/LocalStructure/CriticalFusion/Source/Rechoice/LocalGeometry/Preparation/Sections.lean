module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Sections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.Selection
public import Theory.ElementaryAbelian.BinaryQuotientRank

/-!
# Opening commutator calculations for 14.7.70

The literal order-two image in H/O₂(H) makes each Uα actor act either trivially
or as one chosen nonidentity lift. Taking commutator coordinates therefore
identifies [U,Uα]/V₁ with that lift's displacement. The critical rank selection
and69 give index two for U∩Qα; the literal star kernel gives index two for
Uα∩O₂(H). Images of index-two subgroups have codimension at most one.

The reciprocal section is obtained by pulling the original coordinates back
along the actual critical conjugator. Fixed-point lifting and the square-zero
natural involution calculation prove displacement rank two for every nontrivial
alternating involution. Thus no element swapping the endpoints, no second
projection, and no reciprocal upper marking are needed. Applying F.9.13(6) on
both sections gives both point containments. The same-p complement then gives
commutator order eight and intersection with U₀ equal to V₁. Centrality of the
chosen star image implies T-normalization. Earlier68(1) excludes Zα≤U₀.

`UpperMarking` explicitly identifies the literal R₁-image under d.qH with the
chosen upper four-group. It is compatible earlier65 data, not a consequence of
an arbitrary initial S₅ marking. `RankSelection` is the actual selection from
Notation14.7.1 and is transported by the same permitted rechoice. The explicit
reciprocal placement and alternating-image premises are the earlier39/66
implications on the original opposite actor. Their producer and final discharge
owner is qt-14-07. The68 and69 producers are respectively
qt-14-07-critical-residual-fusion and qt-14-07-critical-order-two. The action
centralization used by the consumers is14.5.15(4), owned by qt-14-05.

The marked V-spanning calculation and construction of the permitted rechoice
remain separate obligations. No result here asserts the completion of70.
Source: Aschbacher–Smith, combined manuscript, 1 March2004,
14.7.1,39,64–65 and proof of70, printed pp.1043,1060,1069–1070,1073–1074.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open Subgroup Representation Chapter12.Section08
open scoped commutatorElement IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

variable (d : Data T L V F W)

theorem qH_image_card (A : Subgroup G) :
    Nat.card ((A.subgroupOf F.H).map d.qH) = Nat.card (star F A) := by
  change Nat.card ((A.subgroupOf F.H).map (d.model.toMonoidHom.comp (starMap F))) = _
  rw [← map_map]
  exact card_map_of_injective d.model.injective

theorem order_two_action_dichotomy (c : CriticalPath (L := L) F)
    (s : d.ActionDescent) (h69 : Nat.card (star F c.Uα) = 2)
    (h : F.H) (hh : (h : G) ∈ c.Uα) (hne : d.qH h ≠ 1)
    (a : F.H) (ha : (a : G) ∈ c.Uα) :
    d.action a = 1 ∨ d.action a = d.action h := by
  let A := (c.Uα.subgroupOf F.H).map d.qH
  have hc : Nat.card A = 2 := (qH_image_card d c.Uα).trans h69
  obtain ⟨b, _, hb⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hc
  have hmem : d.qH h ∈ A := mem_map_of_mem d.qH hh
  have hamem : d.qH a ∈ A := mem_map_of_mem d.qH ha
  by_cases haz : d.qH a = 1
  · left
    rw [← s.original a, haz, map_one]
  · right
    have he : (⟨d.qH a, hamem⟩ : A) = ⟨d.qH h, hmem⟩ :=
      (hb _ (fun he => haz (congrArg Subtype.val he))).trans
        (hb _ (fun he => hne (congrArg Subtype.val he))).symm
    rw [← s.original a, ← s.original h]
    exact congrArg s.action (congrArg Subtype.val he)

theorem commutator_image (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (s : d.ActionDescent)
    (h69 : Nat.card (star F c.Uα) = 2)
    (h : F.H) (hh : (h : G) ∈ c.Uα) (hne : d.qH h ≠ 1) :
    tilde d (Fcomm c) = (d.action h - LinearMap.id).range := by
  let R := (d.action h - LinearMap.id).range
  let B : Subgroup F.U := R.toAddSubgroup.toSubgroup.comap d.conjugationSection.coordinates
  have hbound : Fcomm c ≤ B.map F.U.subtype := by
    rw [Fcomm, commutator_comm]
    apply commutator_le.mpr
    intro a ha b hb
    let aH : F.H := ⟨a, c.Uα_le_H earlier ha⟩
    let bU : F.U := ⟨b, hb⟩
    let ab : F.U := (⟨a * b * a⁻¹,
      (mem_normalizer_iff.mp (d.conjugationSection.normalized aH.property) b).mp hb⟩ : F.U) * bU⁻¹
    refine ⟨ab, ?_, rfl⟩
    change (d.conjugationSection.coordinates ab).toAdd ∈ R
    have he : (d.conjugationSection.coordinates ab).toAdd =
        d.action aH (d.conjugationSection.coordinates bU).toAdd -
          (d.conjugationSection.coordinates bU).toAdd := by
      rw [map_mul, map_inv]
      change (d.conjugationSection.coordinates _).toAdd +
        -(d.conjugationSection.coordinates bU).toAdd = _
      rw [d.conjugationSection.equivariant aH bU, sub_eq_add_neg]
    rw [he]
    rcases order_two_action_dichotomy d c s h69 h hh hne aH ha with hz | heq
    · rw [hz]
      simp
    · rw [heq]
      exact ⟨(d.conjugationSection.coordinates bU).toAdd, rfl⟩
  apply le_antisymm
  · intro w hw
    obtain ⟨a, ha, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
    obtain ⟨b, hb, he⟩ := hbound ha
    have he' : b = a := Subtype.ext he
    subst b
    exact hb
  · exact d.conjugationSection.displacement_range_le_imageSpace_of_commutator_le
      c.Uα (Fcomm c) (by rw [Fcomm, commutator_comm]) h hh

/-- A subgroup of index at most two has image of codimension at most one
under the literal section map, even if it does not contain the section kernel. -/
theorem section_codimension {H A E : Subgroup G}
    {ρ : Representation (ZMod 2) H W} (a : BinaryConjugationSection H A E ρ)
    (D : Subgroup G) (hi : D.relIndex A ≤ 2) :
    Module.finrank (ZMod 2) (a.imageSpace D) + 1 ≥ Module.finrank (ZMod 2) W := by
  let : Finite W := Finite.of_surjective (fun x : A => (a.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp a.onto)
  let B := (D.subgroupOf A).map a.coordinates
  have hidx : B.index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := D.subgroupOf A))) ((D.subgroupOf A).index_map_dvd a.onto)).trans hi
  have hc : Nat.card W ≤ Nat.card B * 2 := by
    have he := B.card_mul_index
    change Nat.card B * B.index = Nat.card W at he
    exact he.symm.trans_le (Nat.mul_le_mul_left _ hidx)
  change Nat.card W ≤ Nat.card (a.imageSpace D) * 2 at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := a.imageSpace D),
    Nat.card_zmod, ← pow_succ] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

include d in
theorem original_index_two (c : CriticalPath (L := L) F)
    (selection : c.RankSelection) (h69 : Nat.card (star F c.Uα) = 2) :
    (F.U ⊓ c.Qα).relIndex F.U = 2 := by
  let := d.U_elementary
  have hp := selection.positive
  have hc := selection.comparison
  rw [relIndex_eq_two_pow_quotient_finrank, Nat.log_pow Nat.one_lt_two] at hp hc
  rw [h69] at hc
  norm_num at hc
  rw [relIndex_eq_two_pow_quotient_finrank, show Module.finrank (ZMod 2)
    (Additive (F.U ⧸ (F.U ⊓ c.Qα).subgroupOf F.U)) = 1 by omega]
  rfl

theorem original_codimension (c : CriticalPath (L := L) F)
    (selection : c.RankSelection) (h69 : Nat.card (star F c.Uα) = 2) :
    Module.finrank (ZMod 2) (tilde d (F.U ⊓ c.Qα)) + 1 ≥ Module.finrank (ZMod 2) W :=
  section_codimension d.conjugationSection _ (original_index_two d c selection h69).le

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- Pull a right-conjugated subgroup back by its actual conjugator. -/
def conjugateBack (A : Subgroup G) (g : G) : conjugate A g ≃* A where
  toFun x := ⟨g * x * g⁻¹, by
    obtain ⟨a, ha, he⟩ := x.property
    change g⁻¹ * a * (g⁻¹)⁻¹ = x at he
    rw [← he]
    simpa [mul_assoc] using ha⟩
  invFun a := ⟨g⁻¹ * a * g, by
    exact ⟨a, a.property, by simp⟩⟩
  left_inv x := by apply Subtype.ext; simp [mul_assoc]
  right_inv a := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

omit [Finite G] in
theorem conjugateBack_mem (A B : Subgroup G) (g : G) (x : conjugate A g) :
    (conjugateBack A g x : G) ∈ B ↔ (x : G) ∈ conjugate B g := by
  constructor
  · intro hx
    exact ⟨_, hx, by change g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x; simp [mul_assoc]⟩
  · rintro ⟨b, hb, he⟩
    change g⁻¹ * b * (g⁻¹)⁻¹ = x at he
    change g * x * g⁻¹ ∈ B
    rw [← he]
    simpa [mul_assoc] using hb

variable (d : Data T L V F W) (c : CriticalPath (L := L) F)

def reciprocalAction : Representation (ZMod 2) (conjugate F.H c.conjugator) W :=
  d.action.comp (conjugateBack F.H c.conjugator).toMonoidHom

def reciprocalSection : BinaryConjugationSection (conjugate F.H c.conjugator)
    c.Uα c.Zα (reciprocalAction d c) where
  section_le := map_mono d.conjugationSection.section_le
  kernel_le := map_mono d.conjugationSection.kernel_le
  normalized := (map_mono d.conjugationSection.normalized).trans (le_normalizer_map _)
  coordinates := d.conjugationSection.coordinates.comp
    (conjugateBack F.U c.conjugator).toMonoidHom
  onto := d.conjugationSection.onto.comp (conjugateBack F.U c.conjugator).surjective
  kernel_eq := by
    ext x
    change d.conjugationSection.coordinates (conjugateBack F.U c.conjugator x) = 1 ↔ _
    rw [d.conjugationSection.coordinates_eq_one_iff]
    exact conjugateBack_mem F.U (F.Vi 1) c.conjugator x
  equivariant h a := by
    change (d.conjugationSection.coordinates (conjugateBack F.U c.conjugator _)).toAdd =
      d.action (conjugateBack F.H c.conjugator h)
        (d.conjugationSection.coordinates (conjugateBack F.U c.conjugator a)).toAdd
    rw [← d.conjugationSection.equivariant]
    congr 2
    apply Subtype.ext
    change c.conjugator * ((h : G) * a * (h : G)⁻¹) * c.conjugator⁻¹ =
      (c.conjugator * h * c.conjugator⁻¹) * (c.conjugator * a * c.conjugator⁻¹) *
        (c.conjugator * h * c.conjugator⁻¹)⁻¹
    group

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open Subgroup Representation Chapter12.Section08
open SL2FourNatural

private theorem natural_involution_displacement (g : SL) (hg : g ≠ 1) (hg2 : g * g = 1) :
    Module.finrank (ZMod 2) (naturalRepresentation g - LinearMap.id).range = 2 := by
  let a : V →ₗ[F] V := (Matrix.SpecialLinearGroup.toLin' g).toLinearMap - LinearMap.id
  have haa (v : V) : a (a v) = 0 := by
    change (Matrix.SpecialLinearGroup.toLin' g)
      ((Matrix.SpecialLinearGroup.toLin' g) v - v) -
        ((Matrix.SpecialLinearGroup.toLin' g) v - v) = 0
    rw [map_sub, ← LinearEquiv.mul_apply, ← map_mul, hg2, map_one]
    change v - (Matrix.SpecialLinearGroup.toLin' g) v -
      ((Matrix.SpecialLinearGroup.toLin' g) v - v) = 0
    have hz (w : V) : w + w = 0 := by funext i; exact CharTwo.add_self_eq_zero _
    calc
      _ = (v + v) - ((Matrix.SpecialLinearGroup.toLin' g) v +
        (Matrix.SpecialLinearGroup.toLin' g) v) := by abel
      _ = 0 := by rw [hz, hz, sub_self]
  have hn : a.range ≠ ⊥ := by
    intro hz
    have hz' : a = 0 := LinearMap.range_eq_bot.mp hz
    apply hg
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [map_one]
    apply LinearEquiv.ext
    intro v
    exact sub_eq_zero.mp (LinearMap.congr_fun hz' v)
  have hle : a.range ≤ a.ker := by rintro _ ⟨v, rfl⟩; exact haa v
  have hd := a.finrank_range_add_finrank_ker
  have hm := Submodule.finrank_mono hle
  have hp : 0 < Module.finrank F a.range := Nat.pos_of_ne_zero (fun h => hn (Submodule.finrank_eq_zero.mp h))
  have hV : Module.finrank F V = 2 := by simp [V]
  rw [hV] at hd
  have hr : Module.finrank F a.range = 1 := by omega
  have hc : Nat.card a.range = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := F), hr, pow_one,
      Nat.card_eq_fintype_card, card_field]
  have he : Nat.card (naturalRepresentation g - LinearMap.id).range = Nat.card a.range := by
    apply Nat.card_congr
    exact Equiv.refl _
  rw [hc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at he
  exact Nat.pow_right_injective (by decide : 1 < 2) (he.trans (by decide : 4 = 2 ^ 2))

/-- The displacement rank on the same cover for any nontrivial alternating
involution, with no alignment of that involution to the original upper group. -/
theorem cover_involution_displacement {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] {σ : Representation (ZMod 2) SL W}
    (p : σ.IntertwiningMap naturalRepresentation) (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ Representation.OneCohomology.fixed σ)
    (g : SL) (hg : g ≠ 1) (hg2 : g * g = 1) :
    Module.finrank (ZMod 2) (σ g - LinearMap.id).range = 2 := by
  let a := σ g - LinearMap.id
  let b := (naturalRepresentation g - LinearMap.id).comp p.toLinearMap
  have hker : a.ker = b.ker := by
    ext w
    change σ g w - w = 0 ↔ naturalRepresentation g (p w) - p w = 0
    rw [sub_eq_zero, sub_eq_zero]
    constructor
    · intro h
      exact (LinearMap.congr_fun (p.isIntertwining' g) w).symm.trans (congrArg p h)
    · intro h
      apply SL2NaturalFixedLifting.fixed_lift_of_fixed_kernel σ p.toLinearMap.toAddMonoidHom hp
        (fun g w => LinearMap.congr_fun (p.isIntertwining' g) w)
        (fun w hw g => hk hw g) g w
      exact (LinearMap.congr_fun (p.isIntertwining' g) w).trans h
  have hrange : b.range = (naturalRepresentation g - LinearMap.id).range := by
    exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hp)
  have h1 := a.finrank_range_add_finrank_ker
  have h2 := b.finrank_range_add_finrank_ker
  rw [hker] at h1
  rw [hrange, natural_involution_displacement g hg hg2] at h2
  exact Nat.add_right_cancel (h1.trans h2.symm)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open Subgroup Representation Chapter12.Section08
open Matrix.SpecialLinearGroup
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W)

/-- Compatibility of the chosen natural marking with the literal R₁-image.
This is earlier 14.7.65 data, and is not implied by an arbitrary S₅ marking. -/
def UpperMarking : Prop :=
  ((F.Ri L 1).subgroupOf F.H).map d.qH =
    (upperUnipotent SL2FourNatural.F).map (alternatingActor d.naturalQuotient)

private theorem upper_zero : SL2FourNatural.upper 0 = 1 := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [SL2FourNatural.upper]

private theorem alternatingActor_injective : Function.Injective (alternatingActor d.naturalQuotient) :=
  Subtype.val_injective.comp d.naturalQuotient.marking.injective

theorem upper_actor_ne_one (h : F.H) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) : d.qH h ≠ 1 := by
  intro hz
  have he := (alternatingActor_injective d) ((hh.symm.trans hz).trans
    (alternatingActor d.naturalQuotient).map_one.symm)
  have he' := congrArg (fun a : SL2FourNatural.SL => a.val 0 1) he
  exact ht (by simpa [SL2FourNatural.upper] using he')

theorem exists_upper_actor (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (mark : UpperMarking d)
    (h69 : Nat.card (star F c.Uα) = 2) :
    ∃ h : F.H, (h : G) ∈ c.Uα ∧ ∃ t : SL2FourNatural.F,
      t ≠ 0 ∧ d.qH h = alternatingActor d.naturalQuotient (SL2FourNatural.upper t) := by
  let A := (c.Uα.subgroupOf F.H).map d.qH
  have hc : Nat.card A = 2 := (qH_image_card d _).trans h69
  obtain ⟨a, ha, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hc
  obtain ⟨h, hh, he⟩ := a.property
  have hn : d.qH h ≠ 1 := by intro hz; exact ha (Subtype.ext (he.symm.trans hz))
  have hm : d.qH h ∈ (upperUnipotent SL2FourNatural.F).map
      (alternatingActor d.naturalQuotient) := by
    rw [← mark]
    exact mem_map_of_mem d.qH (earlier.placement hh)
  obtain ⟨g, hg, hge⟩ := hm
  obtain ⟨t, ht⟩ := (mem_upperUnipotent SL2FourNatural.F g).mp hg
  have hgt : g = SL2FourNatural.upper t :=
    ht.symm.trans (SL2FourCentralCover.upper_transvection t).symm
  refine ⟨h, hh, t, ?_, (hgt ▸ hge).symm⟩
  intro hz
  subst t
  rw [hgt, upper_zero, map_one] at hge
  exact hn hge.symm

omit [Finite G] in
theorem R₁_le_T : F.Ri L 1 ≤ (T : Subgroup G) :=
  (pCoreIn_le_sylow (group F L) (T.subtype le_sup_right)).trans_eq
    (map_subgroupOf_eq_of_le le_sup_right)

theorem upper_mem_actorT (mark : UpperMarking d) (t : SL2FourNatural.F) :
    alternatingActor d.naturalQuotient (SL2FourNatural.upper t) ∈
      (actorT (F := F)).map d.qH := by
  have hm : alternatingActor d.naturalQuotient (SL2FourNatural.upper t) ∈
      ((F.Ri L 1).subgroupOf F.H).map d.qH := by
    rw [mark]
    apply mem_map_of_mem
    exact (mem_upperUnipotent SL2FourNatural.F _).mpr
      ⟨t, (SL2FourCentralCover.upper_transvection t).symm⟩
  exact map_mono (subgroupOf_mono F.H R₁_le_T) hm

/-- Application of the original rank-selection calculation to F.9.13(6).
No codimension or D-commutator conclusion is assumed. -/
theorem original_point_in_commutator (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (s : d.ActionDescent) (mark : UpperMarking d)
    (selection : c.RankSelection) (h69 : Nat.card (star F c.Uα) = 2)
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα) :
    ⁅F.U ⊓ c.Qα, c.Uα⁆ = c.Zα ∧ c.Zα ≤ Fcomm c := by
  obtain ⟨h, hh, t, ht, he⟩ := exists_upper_actor d c earlier mark h69
  exact D_commutator_eq_Zα c
    (D_commutator_ne_bot d c s h hh t ht he (original_codimension d c selection h69)) hF9

/-- Quotient centrality gives the exact commutation premise of the original
fixed-line consumer. -/
theorem actorT_commutes (c : CriticalPath (L := L) F)
    (hc : star F c.Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G)))
    (h : F.H) (hh : (h : G) ∈ c.Uα) (t : actorT (F := F)) :
    Commute (d.qH (t : F.H)) (d.qH h) := by
  have hm := hc (mem_map_of_mem (starMap F) hh)
  rw [centerIn_eq_inf_centralizer] at hm
  have he := hm.2 (starMap F (t : F.H)) (mem_map_of_mem (starMap F) t.property)
  change d.model (starMap F (t : F.H)) * d.model (starMap F h) =
    d.model (starMap F h) * d.model (starMap F (t : F.H))
  simpa only [map_mul] using congrArg d.model he

/-- Nonidentity quotient image prevents the source point from returning to
U₀, by the literal fusion assertion 14.7.68(1). -/
theorem point_not_le_U₀ (c : CriticalPath (L := L) F)
    (h69 : Nat.card (star F c.Uα) = 2)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z}) : ¬ c.Zα ≤ d.U₀ := by
  intro hZ
  have hz : c.conjugator⁻¹ * d.z * c.conjugator ∈ c.Zα := by
    apply mem_map.mpr
    exact ⟨d.z, d.point ▸ mem_zpowers d.z, by simp⟩
  have hconj : IsConj d.z (c.conjugator⁻¹ * d.z * c.conjugator) :=
    isConj_iff.mpr ⟨c.conjugator⁻¹, by simp⟩
  have he : c.conjugator⁻¹ * d.z * c.conjugator = d.z :=
    Set.mem_singleton_iff.mp (h68 ▸ (show _ ∈ {x : G | IsConj d.z x} ∩ (d.U₀ : Set G)
      from ⟨hconj, hZ hz⟩))
  have hg : c.conjugator ∈ F.H := by
    rw [d.centralizer_eq, mem_centralizer_singleton_iff]
    symm
    calc
      d.z * c.conjugator = c.conjugator * (c.conjugator⁻¹ * d.z * c.conjugator) := by group
      _ = c.conjugator * d.z := by rw [he]
  have hU : c.Uα = F.U := (conjugate_eq_iff F.U c.conjugator).mpr
    (d.conjugationSection.normalized hg)
  have hUQ : F.U ≤ F.H.pCoreIn 2 := by
    let := d.U_elementary
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 F.U)
      d.conjugationSection.section_le d.conjugationSection.normalized
  have hb : (F.U.subgroupOf F.H).map d.qH = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [d.qH_ker]
    exact subgroupOf_mono F.H hUQ
  have hc := qH_image_card d F.U
  rw [hU] at h69
  rw [← hc, hb, card_bot] at h69
  contradiction

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- S₅ coordinates on the quotient by O₂(Gα), transported by the actual
critical conjugator. -/
def reciprocalQuotient : (conjugate F.H c.conjugator) →* ChapterJ.S5 :=
  d.qH.comp (conjugateBack F.H c.conjugator).toMonoidHom

theorem reciprocalQuotient_ker : (reciprocalQuotient d c).ker =
    c.Qα.subgroupOf (conjugate F.H c.conjugator) := by
  have hQ : c.Qα = conjugate (F.H.pCoreIn 2) c.conjugator :=
    (map_pCoreIn_of_injective 2 F.H _ (MulAut.conj c.conjugator⁻¹).injective).symm
  ext x
  change d.qH (conjugateBack F.H c.conjugator x) = 1 ↔ (x : G) ∈ c.Qα
  rw [← MonoidHom.mem_ker, d.qH_ker, hQ]
  exact conjugateBack_mem F.H (F.H.pCoreIn 2) c.conjugator x

include d in
theorem reciprocal_index_two (earlier : c.EarlierImages)
    (h69 : Nat.card (star F c.Uα) = 2) :
    (c.Uα ⊓ F.H.pCoreIn 2).relIndex c.Uα = 2 := by
  rw [inf_relIndex_left, ← relIndex_subgroupOf (c.Uα_le_H earlier),
    ← d.qH_ker, relIndex_ker, qH_image_card, h69]

theorem reciprocal_codimension (earlier : c.EarlierImages)
    (h69 : Nat.card (star F c.Uα) = 2) :
    Module.finrank (ZMod 2) ((reciprocalSection d c).imageSpace (c.Uα ⊓ F.H.pCoreIn 2)) + 1 ≥
      Module.finrank (ZMod 2) W :=
  section_codimension (reciprocalSection d c) _ (reciprocal_index_two d c earlier h69).le

theorem opposite_image_card (hUH : F.U ≤ conjugate F.H c.conjugator)
    (selection : c.RankSelection) (h69 : Nat.card (star F c.Uα) = 2) :
    Nat.card ((F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c)) = 2 := by
  rw [← relIndex_ker, reciprocalQuotient_ker, relIndex_subgroupOf hUH,
    ← inf_relIndex_left, original_index_two d c selection h69]

/-- The earlier reciprocal placement and residual-image assertion of
14.7.39/66 supply an actual opposite actor. Its displacement rank is derived
on the transported section, without a swapping element or a new projection. -/
theorem exists_opposite_actor (s : d.ActionDescent)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (selection : c.RankSelection) (h69 : Nat.card (star F c.Uα) = 2)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5)) :
    ∃ y : conjugate F.H c.conjugator, (y : G) ∈ F.U ∧
      Module.finrank (ZMod 2) (reciprocalAction d c y - LinearMap.id).range = 2 := by
  let := finite_original d
  let A := (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c)
  have hc : Nat.card A = 2 := opposite_image_card d c hUH selection h69
  obtain ⟨a, ha, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hc
  obtain ⟨y, hy, he⟩ := a.property
  have hn : reciprocalQuotient d c y ≠ 1 := by
    intro hz
    exact ha (Subtype.ext (he.symm.trans hz))
  have hsq : reciprocalQuotient d c y * reciprocalQuotient d c y = 1 := by
    have hp : a ^ Nat.card A = 1 := pow_card_eq_one'
    rw [hc, pow_two] at hp
    have hp' : (a : ChapterJ.S5) * a = 1 := congrArg Subtype.val hp
    rwa [← he] at hp'
  have hmem : reciprocalQuotient d c y ∈ alternatingGroup (Fin 5) :=
    heven (mem_map_of_mem _ hy)
  let g := d.naturalQuotient.marking.symm ⟨reciprocalQuotient d c y, hmem⟩
  have hg : alternatingActor d.naturalQuotient g = reciprocalQuotient d c y :=
    congrArg Subtype.val (d.naturalQuotient.marking.apply_symm_apply _)
  have hg1 : g ≠ 1 := by intro hz; apply hn; rw [← hg, hz, map_one]
  have hg2 : g * g = 1 := by
    apply (Subtype.val_injective.comp d.naturalQuotient.marking.injective)
    change alternatingActor d.naturalQuotient (g * g) = alternatingActor d.naturalQuotient 1
    rw [map_mul, map_one, hg, hsq]
  refine ⟨y, hy, ?_⟩
  change Module.finrank (ZMod 2)
    (d.action (conjugateBack F.H c.conjugator y) - LinearMap.id).range = 2
  rw [← s.original]
  change Module.finrank (ZMod 2) (s.action (reciprocalQuotient d c y) - LinearMap.id).range = 2
  rw [← hg]
  exact cover_involution_displacement (restrictedProjection d.naturalQuotient s.projection)
    d.projection_onto s.kernel_fixed g hg1 hg2

/-- Both point containments and both D-commutator identities in the opening
paragraph of 14.7.70. The only source inputs beyond Data, rank selection and69
are the compatible65 marking, reciprocal39/66 placement and the two F.9.13(6)
bounds. In particular no displacement or codimension conclusion is assumed. -/
theorem opening_commutators (earlier : c.EarlierImages) (s : d.ActionDescent)
    (mark : UpperMarking d) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα)
    (hF9α : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1) :
    ⁅F.U ⊓ c.Qα, c.Uα⁆ = c.Zα ∧
      ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ = F.Vi 1 ∧
      c.Zα ≤ Fcomm c ∧ F.Vi 1 ≤ Fcomm c := by
  obtain ⟨hZ, hZF⟩ := original_point_in_commutator d c earlier s mark selection h69 hF9
  obtain ⟨y, hy, hr⟩ := exists_opposite_actor d c s hUH selection h69 heven
  obtain ⟨_, hP, hPF⟩ := reciprocal_commutator_eq_point c (reciprocalAction d c)
    (reciprocalSection d c) y hy hr (reciprocal_codimension d c earlier h69) hF9α
  exact ⟨hZ, hP, hZF, hPF⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W)

/-- Saturation through the original point kernel, for a literal subgroup of U. -/
theorem coordinate_mem_iff (A : Subgroup G) (hpoint : F.Vi 1 ≤ A) (x : F.U) :
    (d.conjugationSection.coordinates x).toAdd ∈ tilde d A ↔ (x : G) ∈ A := by
  constructor
  · intro hx
    obtain ⟨a, ha, he⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hx
    have hk : ((x / a : F.U) : G) ∈ F.Vi 1 := by
      apply (d.conjugationSection.coordinates_eq_one_iff _).mp
      rw [map_div, Multiplicative.toAdd.injective he, div_self']
    have hm := A.mul_mem (hpoint hk) ha
    simpa using hm
  · intro hx
    exact (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨x, hx, rfl⟩

include d in
/-- Earlier reciprocal geodesic placement supplies the second normalization. -/
theorem commutator_le_intersection (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (hUH : F.U ≤ conjugate F.H c.conjugator) :
    Fcomm c ≤ F.U ⊓ c.Uα := by
  have hnorm : F.U ≤ normalizer (c.Uα : Set G) :=
    hUH.trans ((map_mono d.conjugationSection.normalized).trans (le_normalizer_map _))
  exact le_inf (Fcomm_le_U d c earlier) (le_normalizer_iff_commutator_le_right.mp hnorm)

theorem commutator_card (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (s : d.ActionDescent) (mark : UpperMarking d)
    (h69 : Nat.card (star F c.Uα) = 2) (hpoint : F.Vi 1 ≤ Fcomm c) :
    Nat.card (Fcomm c) = 8 := by
  let := finite_original d
  obtain ⟨h, hh, t, ht, he⟩ := exists_upper_actor d c earlier mark h69
  rw [card_eq_tilde_mul d _ (Fcomm_le_U d c earlier) hpoint,
    commutator_image d c earlier s h69 h hh (upper_actor_ne_one d h t ht he),
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    displacement_finrank d s h t ht he]
  norm_num

theorem commutator_inf_U₀ (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (s : d.ActionDescent) (mark : UpperMarking d)
    (h69 : Nat.card (star F c.Uα) = 2) (hpoint : F.Vi 1 ≤ Fcomm c) :
    Fcomm c ⊓ d.U₀ = F.Vi 1 := by
  obtain ⟨h, hh, t, ht, he⟩ := exists_upper_actor d c earlier mark h69
  have himage := commutator_image d c earlier s h69 h hh (upper_actor_ne_one d h t ht he)
  have hd := (s.original_upper_complement h t ht he).1
  apply le_antisymm
  · intro a ha
    let aU : F.U := ⟨a, d.U₀_le_U ha.2⟩
    apply (d.conjugationSection.coordinates_eq_one_iff aU).mp
    apply Multiplicative.toAdd.injective
    change (d.conjugationSection.coordinates aU).toAdd = 0
    apply Submodule.disjoint_def.mp hd
    · rw [← himage]
      exact (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨aU, ha.1, rfl⟩
    · exact (d.mem_U₀ aU).mp ha.2
  · exact le_inf hpoint d.point_le_U₀

theorem T_normalizes_commutator (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (s : d.ActionDescent) (mark : UpperMarking d)
    (h69 : Nat.card (star F c.Uα) = 2) (hpoint : F.Vi 1 ≤ Fcomm c)
    (hcentral : star F c.Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G))) :
    (T : Subgroup G) ≤ normalizer (Fcomm c : Set G) := by
  obtain ⟨h, hh, t, ht, he⟩ := exists_upper_actor d c earlier mark h69
  have himage := commutator_image d c earlier s h69 h hh (upper_actor_ne_one d h t ht he)
  apply le_normalizer_iff.mpr
  intro x hx a ha
  let xH : F.H := ⟨x, F.invariant 1 hx⟩
  let xT : actorT (F := F) := ⟨xH, hx⟩
  let aU : F.U := ⟨a, Fcomm_le_U d c earlier ha⟩
  let b : F.U := ⟨x * a * x⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized xH.property) a).mp aU.property⟩
  apply (coordinate_mem_iff d (Fcomm c) hpoint b).mp
  rw [d.conjugationSection.equivariant xH aU, himage]
  apply displacement_invariant d s h (actorT_commutes d c hcentral h hh) xT
  rw [← himage]
  exact (coordinate_mem_iff d (Fcomm c) hpoint aU).mpr ha

/-- All ambient commutator data required by the independent rank-three
consumer, except the marked V-disjointness calculation. These deductions hold
also at smaller rank; rank three is only needed by that subsequent consumer. -/
theorem preliminary_geometry (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (s : d.ActionDescent) (mark : UpperMarking d)
    (selection : c.RankSelection) (h69 : Nat.card (star F c.Uα) = 2)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (hF9 : ⁅F.U ⊓ c.Qα, c.Uα⁆ ≤ c.Zα)
    (hF9α : ⁅c.Uα ⊓ F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1)
    (hcentral : star F c.Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G))) :
    Fcomm c ≤ F.U ⊓ c.Uα ∧ c.Zα ≤ Fcomm c ∧ F.Vi 1 ≤ Fcomm c ∧
      (T : Subgroup G) ≤ normalizer (Fcomm c : Set G) ∧
      Nat.card (Fcomm c) = 8 ∧ Fcomm c ⊓ d.U₀ = F.Vi 1 := by
  obtain ⟨_, _, hZ, hP⟩ := opening_commutators d c earlier s mark selection h69 hUH heven hF9 hF9α
  exact ⟨commutator_le_intersection d c earlier hUH, hZ, hP,
    T_normalizes_commutator d c earlier s mark h69 hP hcentral,
    commutator_card d c earlier s mark h69 hP,
    commutator_inf_U₀ d c earlier s mark h69 hP⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W)

omit [Finite G] in
private theorem conjugate_product (A : Subgroup G) (g h : G) :
    conjugate A (g * h) = conjugate (conjugate A g) h := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite G] in
theorem reselect_Qα (c : CriticalPath (L := L) F) (n : group F L) :
    (c.reselect n).Qα = conjugate c.Qα n := by
  rw [CriticalPath.Qα, c.reselect_conjugator, conjugate_product]
  exact (map_pCoreIn_of_injective 2 (conjugate F.H c.conjugator) _
    (MulAut.conj (n : G)⁻¹).injective).symm

include d in
theorem reselect_index (c : CriticalPath (L := L) F) (n : group F L) :
    (F.U ⊓ (c.reselect n).Qα).relIndex F.U = (F.U ⊓ c.Qα).relIndex F.U := by
  have hU : conjugate F.U n = F.U := (conjugate_eq_iff F.U n).mpr
    (d.conjugationSection.normalized (group_le_H n.property))
  have hD : F.U ⊓ (c.reselect n).Qα = conjugate (F.U ⊓ c.Qα) n := by
    have hm : conjugate (F.U ⊓ c.Qα) n = conjugate F.U n ⊓ conjugate c.Qα n :=
      map_inf _ _ _ (MulAut.conj (n : G)⁻¹).injective
    rw [reselect_Qα, hm, hU]
  calc
    _ = (conjugate (F.U ⊓ c.Qα) n).relIndex (conjugate F.U n) := by rw [hD, hU]
    _ = _ := relIndex_map_map_of_injective _ _ (MulAut.conj (n : G)⁻¹).injective

include d in
/-- Rank selection is preserved together with the original path and the
literal order-two image by the same permitted rechoice. -/
theorem reselect_rankSelection (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (selection : c.RankSelection) (n : group F L) :
    (c.reselect n).RankSelection where
  positive := by rw [reselect_index d]; exact selection.positive
  comparison := by rw [reselect_index d, c.reselect_star_card earlier]; exact selection.comparison

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation

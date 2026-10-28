module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.FaithfulMoved.Coordinates
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.MaxElementaryOffender
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import Stellmacher.BaumannMap
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.SwappingBound
/-!
# The Baumann subgroup preserves the two definite planes

For a normal elementary sixteen with a compatible orthogonal action, a maximum
order elementary subgroup cannot interchange the two planes: its replacement
inequality contradicts the strict fixed-vector/order bound for a swapping actor.
Thus the elementary Thompson subgroup preserves each plane. Its two-group action
fixes a nonidentity vector in the first plane. That vector belongs to the omega
center of the Thompson subgroup, so the Baumann subgroup fixes it and cannot
interchange the planes either.

The final application uses the actual moved subgroup and the orthogonal
coordinates constructed from the genuine earlier 15.4.11 inputs and clause (3).
Source: Aschbacher--Smith, 15.4.12(6), printed pp.1160--1161, combined
manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped Pointwise IsMulCommutative
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BaumannPair
open BinaryNormalizer
set_option synthInstance.maxSize 10000
def firstPlane : Subgroup ModelSpace where
  carrier := {v | v.toAdd.2 = 0}
  one_mem' := rfl
  mul_mem' := by intro x y hx hy; change x.toAdd.2 + y.toAdd.2 = 0; rw [hx,hy,add_zero]
  inv_mem' := by intro x hx; change -x.toAdd.2 = 0; rw [hx,neg_zero]
def base : Subgroup OrthogonalFourBinary.IsometryGroup :=
  (MulAction.stabilizer (MulAut ModelSpace) firstPlane).comap vectorAction
private theorem firstPlane_card : Nat.card firstPlane = 4 := by
  change Nat.card {v : Space // v.2 = 0} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel
theorem base_iff (g : OrthogonalFourBinary.IsometryGroup) :
    g ∈ base ↔ (codeEquiv.symm g).2.2 = false := by
  obtain ⟨k,rfl⟩ := codeMap_bijective.surjective g
  have hk : codeEquiv.symm (codeMap k) = k := codeEquiv.symm_apply_apply k
  rw [hk]
  have hf : (∀ v : Space, v.2 = 0 → (eval k v).2 = 0) ↔ k.2.2 = false := by
    exact (show ∀ k : Code,
      (∀ v : Space, v.2 = 0 → (eval k v).2 = 0) ↔ k.2.2 = false by decide +kernel) k
  constructor
  · intro hg
    apply hf.mp
    intro v hv
    have he : firstPlane.map (vectorAction (codeMap k)).toMonoidHom = firstPlane := hg
    have hm := he.le (mem_map.mpr ⟨Multiplicative.ofAdd v,hv,rfl⟩)
    simpa only [candidate_eval] using (show (candidate k v).2 = 0 from hm)
  · intro h
    change firstPlane.map (vectorAction (codeMap k)).toMonoidHom = firstPlane
    apply eq_of_le_of_card_ge
    · rintro _ ⟨v,hv,rfl⟩
      change (candidate k v.toAdd).2 = 0
      rw [candidate_eval]
      exact hf.mpr h v.toAdd hv
    · exact (card_map_of_injective (f := (vectorAction (codeMap k)).toMonoidHom)
        (K := firstPlane) (vectorAction (codeMap k)).injective).ge
private theorem fixed_first_nonzero_base (g : OrthogonalFourBinary.IsometryGroup) (v : ModelSpace)
    (hv : v ∈ firstPlane) (hne : v ≠ 1) (hfix : vectorAction g v = v) : g ∈ base := by
  apply (base_iff g).mpr
  obtain ⟨k,rfl⟩ := codeMap_bijective.surjective g
  rw [show codeEquiv.symm (codeMap k) = k from codeEquiv.symm_apply_apply k]
  have hh : ∀ k : Code, ∀ v : Space, v.2 = 0 → v ≠ 0 → eval k v = v →
      k.2.2 = false := by decide +kernel
  exact hh k v.toAdd hv hne ((candidate_eval k v.toAdd).symm.trans hfix)

variable {G : Type*} [Group G]
/-- A compatible natural orthogonal action of the specified group on W. -/
structure Action (W : Subgroup G) where
  coordinates : W ≃* ModelSpace
  actor : G →* OrthogonalFourBinary.IsometryGroup
  intertwines : ∀ (g : G) (w : W),
    (coordinates.symm (vectorAction (actor g) (coordinates w)) : G) = g * (w : G) * g⁻¹
namespace Action
variable {W : Subgroup G} (d : Action W)
private theorem ker_eq : d.actor.ker = centralizer (W : Set G) := by
  ext g
  constructor
  · intro hg w hw
    have hh := d.intertwines g ⟨w,hw⟩
    rw [show d.actor g = 1 from hg, map_one] at hh
    change (d.coordinates.symm (d.coordinates ⟨w,hw⟩) : G) = g*w*g⁻¹ at hh
    rw [d.coordinates.symm_apply_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · intro hg
    apply vectorAction_injective
    apply MulEquiv.ext
    intro v
    let w := d.coordinates.symm v
    have hh := d.intertwines g w
    rw [d.coordinates.apply_symm_apply] at hh
    have he : g * (w : G) * g⁻¹ = w := mul_inv_eq_iff_eq_mul.mpr (hg w w.property).symm
    have hcv : d.coordinates.symm (vectorAction (d.actor g) v) = d.coordinates.symm v :=
      Subtype.ext (hh.trans he)
    exact d.coordinates.symm.injective hcv
variable [Finite G]
omit [Finite G] in
private theorem fixed_card_bound (A : Subgroup G) :
    Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) ≤
      Nat.card (FixedVectors (A.map d.actor)) := by
  let f : (W ⊓ centralizer (A : Set G) : Subgroup G) → FixedVectors (A.map d.actor) :=
    fun w => ⟨(d.coordinates ⟨w,w.property.1⟩).toAdd, by
      rintro _ ⟨a,ha,rfl⟩
      change vectorAction (d.actor a) (d.coordinates ⟨w,w.property.1⟩) =
        d.coordinates ⟨w,w.property.1⟩
      apply d.coordinates.symm.injective
      apply Subtype.ext
      rw [d.coordinates.symm_apply_apply]
      exact (d.intertwines a ⟨w,w.property.1⟩).trans
        (mul_inv_eq_iff_eq_mul.mpr (w.property.2 a ha))⟩
  apply Nat.card_le_card_of_injective f
  intro a b h
  exact Subtype.ext (congrArg (fun w : W => (w : G)) (d.coordinates.injective
    (congrArg (fun z : FixedVectors (A.map d.actor) => z.val) h)))
omit [Finite G] in
noncomputable def plane : Subgroup G :=
  (firstPlane.map d.coordinates.symm.toMonoidHom).map W.subtype
omit [Finite G] in
private theorem plane_card : Nat.card d.plane = 4 := by
  rw [plane,card_map_of_injective W.subtype_injective,
    card_map_of_injective d.coordinates.symm.injective,firstPlane_card]
omit [Finite G] in
private theorem plane_le : d.plane ≤ W := map_subtype_le _
private theorem plane_normalizes {g : G} (hg : d.actor g ∈ base) :
    g ∈ normalizer (d.plane : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨w,hw,rfl⟩
    obtain ⟨u,hu,rfl⟩ := hw
    obtain ⟨v,hv,rfl⟩ := hu
    have hp : vectorAction (d.actor g) v ∈ firstPlane :=
      (show firstPlane.map (vectorAction (d.actor g)).toMonoidHom = firstPlane from hg).le
        (mem_map.mpr ⟨v,hv,rfl⟩)
    refine mem_map.mpr ⟨d.coordinates.symm (vectorAction (d.actor g) v),
      mem_map.mpr ⟨_,hp,rfl⟩,?_⟩
    have he := d.intertwines g (d.coordinates.symm v)
    change (d.coordinates.symm (vectorAction (d.actor g) v) : G) =
      g * (d.coordinates.symm v : G) * g⁻¹
    simpa only [d.coordinates.apply_symm_apply] using he
  · rw [card_map_of_injective (MulAut.conj g).injective]
/-- Maximum elementary subgroups cannot interchange the two coordinate planes. -/
theorem maximum_family_base [W.Normal] [IsElementaryAbelian 2 W]
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G)) :
    A ≤ base.comap d.actor := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A.map d.actor) := hA.2.1.map d.actor
  have hcard : Nat.card W = 16 := by
    rw [Nat.card_congr d.coordinates.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hlo := maxElementary_card_le_fixed_mul_image ⊤ W A le_top hA d.actor d.ker_eq
  rw [hcard] at hlo
  have hlow : 16 ≤ Nat.card (FixedVectors (A.map d.actor)) * Nat.card (A.map d.actor) :=
    hlo.trans (Nat.mul_le_mul_right _ (d.fixed_card_bound A))
  intro a ha
  by_contra hn
  have hcode : (codeEquiv.symm (d.actor a)).2.2 = true := by
    simpa only [Bool.not_eq_false] using mt (base_iff _).mpr hn
  exact (Nat.not_lt_of_ge hlow) (swapping_elementary_strict_fixed_bound (A.map d.actor)
    (d.actor a) (mem_map.mpr ⟨a,ha,rfl⟩) hcode)
/-- The elementary Thompson group therefore preserves the first coordinate plane. -/
theorem thompson_base [W.Normal] [IsElementaryAbelian 2 W] :
    elementaryAbelianMaxJ (⊤ : Subgroup G) ≤ base.comap d.actor := by
  apply sSup_le
  intro A hA
  exact d.maximum_family_base A hA
/-- The Baumann group preserves both definite planes of the faithful natural action. -/
theorem baumann_base [W.Normal] [IsElementaryAbelian 2 W] (hG : IsPGroup 2 G) :
    ChapterB.baumann (⊤ : Subgroup G) ≤ base.comap d.actor := by
  let J := elementaryAbelianMaxJ (⊤ : Subgroup G)
  have hJN : J ≤ normalizer (d.plane : Set G) := fun g hg => d.plane_normalizes (d.thompson_base hg)
  let U := d.plane ⊓ centralizer (J : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (inf_le_left.trans d.plane_le)
  have hUne : U ≠ ⊥ := by
    intro he
    have hmod := card_modEq_card_inf_centralizer J d.plane (hG.to_subgroup J) hJN
    change Nat.card d.plane ≡ Nat.card U [MOD 2] at hmod
    rw [d.plane_card,he,card_bot] at hmod
    norm_num [Nat.ModEq] at hmod
  have hUalpha : U ≤ ChapterB.thompsonAlpha (⊤ : Subgroup G) :=
    elementary_centralizer_maxJ_le_omegaCenter ⊤ U le_top inf_le_right
  obtain ⟨u,hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
  obtain ⟨w,hw,hwu⟩ := u.property.1
  obtain ⟨v,hv,hvw⟩ := hw
  have hcv : d.coordinates w = v := by
    rw [←hvw]
    exact d.coordinates.apply_symm_apply v
  have hvne : v ≠ 1 := by
    intro hv1
    apply hune
    apply Subtype.ext
    have hw1 : w = 1 := d.coordinates.injective (hcv.trans (hv1.trans (map_one _).symm))
    exact hwu.symm.trans (congrArg Subtype.val hw1)
  intro g hg
  apply fixed_first_nonzero_base (d.actor g) v hv hvne
  apply d.coordinates.symm.injective
  apply Subtype.ext
  have hh := d.intertwines g w
  rw [hcv] at hh
  have hgu : g * (u : G) * g⁻¹ = u :=
    mul_inv_eq_iff_eq_mul.mpr (hg.2 u (hUalpha u.property)).symm
  change (w : G) = u at hwu
  rw [hwu] at hh
  exact hh.trans (hgu.trans hwu.symm) |>.trans (congrArg Subtype.val hvw).symm
end Action

/-- The same Baumann conclusion in the original ambient subgroup coordinates. -/
theorem ambient_baumann_base (T M W : Subgroup G) [Finite G]
    [IsElementaryAbelian 2 W] (hT : IsPGroup 2 T) (hTM : T ≤ M) (hWT : W ≤ T)
    (hnW : M ≤ normalizer (W : Set G))
    (c : W ≃* ModelSpace) (γ : M →* OrthogonalFourBinary.IsometryGroup)
    (hγ : ∀ (g : M) (w : W),
      (c.symm (vectorAction (γ g) (c w)) : G) = (g : G) * (w : G) * (g : G)⁻¹) :
    (ChapterB.baumann T).subgroupOf M ≤ base.comap γ := by
  let W' := W.subgroupOf T
  let e : W' ≃* W := subgroupOfEquivOfLe hWT
  let : W'.Normal := normal_subgroupOf_of_le_normalizer (hTM.trans hnW)
  let : IsElementaryAbelian 2 W' := IsElementaryAbelian.subgroupOf hWT
  let d : Action W' :=
    { coordinates := e.trans c
      actor := γ.comp (inclusion hTM)
      intertwines := by
        intro g w
        apply Subtype.ext
        exact hγ (inclusion hTM g) (e w) }
  have hb := d.baumann_base hT
  have hmap : (ChapterB.baumann (⊤ : Subgroup T)).map T.subtype = ChapterB.baumann T := by
    have hh := baumann_map_injective T.subtype T.subtype_injective (⊤ : Subgroup T)
    simpa only [ChapterB.baumann,ChapterB.thompsonAlpha,←MonoidHom.range_eq_map,range_subtype]
      using hh
  intro m hm
  obtain ⟨t,ht,htm⟩ := hmap.symm.le hm
  have he : inclusion hTM t = m := Subtype.ext htm
  have hb' := hb ht
  change γ (inclusion hTM t) ∈ base at hb'
  rwa [he] at hb'

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BaumannPair

namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure
open BinaryNormalizer BaumannPair
/-- Orthogonal coordinates on the genuine moved group in which every original
Baumann element fixes both definite planes. The faithful cubic image and
pointwise action are retained for the intrinsic factor application. -/
theorem Input.double_orthogonal_baumann {G : Type*} [Group G] [Finite G]
    {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G} (h : Input K T M X 2) :
    ∃ (c : movedModule (T : Subgroup G) M X ≃* ModelSpace)
      (γ : M →* OrthogonalFourBinary.IsometryGroup)
      (ρ : image M X →* MulAut (movedModule (T : Subgroup G) M X)),
      Function.Injective ρ ∧
      (∀ (x : X) (w : movedModule (T : Subgroup G) M X),
        (ρ (memberProjection M X h.member_le x) w : G) =
          (x : G) * (w : G) * (x : G)⁻¹) ∧
      ρ.range.map (MulAut.congr c).toMonoidHom = modelRotations ∧
      (∀ (m : M) (w : movedModule (T : Subgroup G) M X),
        (c.symm (vectorAction (γ m) (c w)) : G) =
          (m : G) * (w : G) * (m : G)⁻¹) ∧
      ∀ b : (ChapterB.baumann (T : Subgroup G)).subgroupOf M,
        (codeEquiv.symm (γ b)).2.2 = false := by
  let W := movedModule (T : Subgroup G) M X
  let : IsElementaryAbelian 2 W := h.moved_elementary
  obtain ⟨c,γ,ρ,hi,hρ,hc,hγ⟩ := h.double_orthogonal_action
  have hWT : W ≤ (T : Subgroup G) := by
    intro w hw
    exact localV_le_sylow T M h.sylow_le
      (h.ambient.evenCharacteristic T M h.maximal h.sylow_le) (h.moved_le hw)
  have hb := ambient_baumann_base (T : Subgroup G) M W T.isPGroup' h.sylow_le hWT
    h.moved_normalized c γ hγ
  exact ⟨c,γ,ρ,hi,hρ,hc,hγ,fun b => (base_iff (γ b)).mp (hb b.property)⟩
end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure

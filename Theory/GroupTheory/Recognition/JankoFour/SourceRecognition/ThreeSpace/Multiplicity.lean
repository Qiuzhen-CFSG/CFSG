module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.CoreSections
public import Mathlib.LinearAlgebra.Pi

/-!
# The same four-space in the three radical coordinates

The source generators z,r,s give literal binary coordinates on Z. The full
K-action therefore realizes every permutation of this marked triple.
Conjugation transports its three pair-core sections, and the commuting
K/R and S/R actions make these transports S/R-equivariant. Multiplication
then identifies R/Z with three copies of the original order-sixteen section
(Q_z ∩ Q_r)/Z, with the same S/R action on every copy.

This constructs the multiplicity space from the source groups and retains
its action on original representatives. Identifying its alternating-five
action as the natural L₂(4) module, and the complementary K/R action as
dual-natural to Z, are further parts of the tensor argument.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.4), pp.597–598, DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)

/-- The original three source markers, in their given order. -/
def markedPoint (i : Fin 3) : d.space := ⟨![z,d.r,d.s] i,by
  rw [space,d.generated]
  fin_cases i <;> exact subset_closure (by simp)⟩

local instance spaceElementary : IsElementaryAbelian 2 d.space := d.elementary

/-- Binary linear combinations of the original source markers. -/
noncomputable def markedLinear : (Fin 3 → ZMod 2) →ₗ[ZMod 2] Additive d.space where
  toFun v := ∑ i, v i • Additive.ofMul (d.markedPoint i)
  map_add' v w := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c v := by simp [mul_smul,Finset.smul_sum]

@[simp] theorem markedLinear_single (i : Fin 3) :
    d.markedLinear (Pi.single i 1) = Additive.ofMul (d.markedPoint i) := by
  classical
  simp [markedLinear,Pi.single_apply]

/-- The source triple spans its literal three-space. -/
theorem markedLinear_surjective : Function.Surjective d.markedLinear := by
  let f := d.markedLinear.toAddMonoidHom.toMultiplicativeLeft
  have hmap : f.range.map d.space.subtype = d.space := by
    apply le_antisymm (map_subtype_le _)
    apply (show d.space = closure ({z,d.r,d.s} : Set G) from d.generated).le.trans
    refine (Subgroup.closure_le _).mpr ?_
    intro t ht
    have hm (i : Fin 3) : (d.markedPoint i : G) ∈ f.range.map d.space.subtype := by
      refine ⟨d.markedPoint i,?_,rfl⟩
      refine ⟨Multiplicative.ofAdd (Pi.single i 1),?_⟩
      exact congrArg Additive.toMul (d.markedLinear_single i)
    rcases ht with ht | ht | ht
    · simpa [ht,markedPoint] using hm 0
    · simpa [ht,markedPoint] using hm 1
    · have ht' : t = d.s := ht
      simpa [ht',markedPoint] using hm 2
  have hr : f.range = ⊤ := by
    apply (map_injective d.space.subtype_injective)
    rw [hmap,← MonoidHom.range_eq_map,range_subtype]
  exact MonoidHom.range_eq_top.mp hr

/-- The original triple gives coordinates, without choosing an unrelated basis. -/
noncomputable def markedCoordinates : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] Additive d.space :=
  LinearEquiv.ofBijective d.markedLinear
    ((Nat.bijective_iff_surjective_and_card d.markedLinear).mpr
      ⟨d.markedLinear_surjective,by
        rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
        exact d.card.symm⟩)

@[simp] theorem markedCoordinates_single (i : Fin 3) :
    d.markedCoordinates (Pi.single i 1) = Additive.ofMul (d.markedPoint i) :=
  d.markedLinear_single i

/-- Coordinate permutations act on the original marked three-space. -/
noncomputable def markedPermutation (p : Equiv.Perm (Fin 3)) : MulAut d.space :=
  MulEquiv.toAdditive.symm
    ((d.markedCoordinates.symm.trans
      (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) p.symm)).trans
        d.markedCoordinates).toAddEquiv

@[simp] theorem markedPermutation_point (p : Equiv.Perm (Fin 3)) (i : Fin 3) :
    d.markedPermutation p (d.markedPoint i) = d.markedPoint (p i) := by
  have hp : LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) p.symm (Pi.single i 1) =
      Pi.single (p i) 1 := by
    classical
    ext j
    change (Pi.single i (1 : ZMod 2) : Fin 3 → ZMod 2) (p.symm j) = (Pi.single (p i) (1 : ZMod 2) : Fin 3 → ZMod 2) j
    simp only [Pi.single_apply]
    have he : p.symm j = i ↔ j = p i := p.symm_apply_eq
    simp only [he]
  change Additive.toMul (d.markedCoordinates
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) p.symm
      (d.markedCoordinates.symm (Additive.ofMul (d.markedPoint i))))) = _
  rw [← d.markedCoordinates_single i,LinearEquiv.symm_apply_apply,hp,d.markedCoordinates_single]
  rfl

/-- Every permutation of the original triple is realized by an element of the original K. -/
theorem exists_K_marked_permutation (h : IsTypeJ4 z) (p : Equiv.Perm (Fin 3)) :
    ∃ k : d.K, ∀ i : Fin 3,
      (k : G) * (d.markedPoint i : G) * (k : G)⁻¹ = (d.markedPoint (p i) : G) := by
  obtain ⟨k,hk⟩ := d.KAction_surjective h (d.markedPermutation p)
  refine ⟨k,fun i => ?_⟩
  have hh := congrArg (fun a : MulAut d.space => (a (d.markedPoint i) : G)) hk
  exact hh.trans (congrArg Subtype.val (d.markedPermutation_point p i))

/-- Restrict an action to a subgroup that it preserves. -/
def restrictAction {A V : Type*} [Group A] [Group V] (ρ : A →* MulAut V)
    (W : Subgroup V) (hW : ∀ a, W.map (ρ a).toMonoidHom = W) : A →* MulAut W where
  toFun a := ((ρ a).subgroupMap W).trans (MulEquiv.subgroupCongr (hW a))
  map_one' := by
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    exact congrArg (fun f : MulAut V => f w.val) ρ.map_one
  map_mul' a b := by
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    exact congrArg (fun f : MulAut V => f w.val) (ρ.map_mul a b)

@[simp] theorem restrictAction_apply {A V : Type*} [Group A] [Group V] (ρ : A →* MulAut V)
    (W : Subgroup V) (hW : ∀ a, W.map (ρ a).toMonoidHom = W) (a : A) (w : W) :
    (restrictAction ρ W hW a w : V) = ρ a w := rfl

attribute [local instance] R_normal_in_K R_normal_in_S_intrinsic

/-- The original pair section used as the four-dimensional multiplicity space. -/
def multiplicitySpace : Subgroup (d.R ⧸ center d.R) := d.coreSection z ⊓ d.coreSection d.r

theorem multiplicitySpace_card (h : IsTypeJ4 z) : Nat.card d.multiplicitySpace = 16 := by
  have hz := (d.markedPoint 0).property
  have hr := (d.markedPoint 1).property
  have hz1 : z ≠ 1 := by intro he; have hi := h.involution; simp [he] at hi
  have hr1 : d.r ≠ 1 := by intro he; exact hz1 (isConj_one_left.mp (he ▸ d.r_conj))
  exact d.coreSection_inf_card h hz hr hz1 hr1 d.r_ne.symm

theorem coreSection_SQuotient_invariant (h : IsTypeJ4 z) {t : G} (ht : t ∈ d.space)
    (a : d.S ⧸ d.R.subgroupOf d.S) :
    (d.coreSection t).map (d.SRadicalAction h a).toMonoidHom = d.coreSection t := by
  obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective (d.R.subgroupOf d.S) a
  exact d.coreSection_S_invariant ht s

theorem pairSection_SQuotient_invariant (h : IsTypeJ4 z) {t u : G}
    (ht : t ∈ d.space) (hu : u ∈ d.space) (a : d.S ⧸ d.R.subgroupOf d.S) :
    (d.coreSection t ⊓ d.coreSection u).map (d.SRadicalAction h a).toMonoidHom =
      d.coreSection t ⊓ d.coreSection u := by
  rw [Subgroup.map_inf _ _ _ (d.SRadicalAction h a).injective,
    d.coreSection_SQuotient_invariant h ht,d.coreSection_SQuotient_invariant h hu]

/-- The action of the literal S/R on its original four-dimensional section. -/
def multiplicityAction (h : IsTypeJ4 z) :
    (d.S ⧸ d.R.subgroupOf d.S) →* MulAut d.multiplicitySpace :=
  restrictAction (d.SRadicalAction h) d.multiplicitySpace
    (d.pairSection_SQuotient_invariant h (d.markedPoint 0).property (d.markedPoint 1).property)

@[simp] theorem multiplicityAction_apply (h : IsTypeJ4 z)
    (a : d.S ⧸ d.R.subgroupOf d.S) (w : d.multiplicitySpace) :
    (d.multiplicityAction h a w : d.R ⧸ center d.R) = d.SRadicalAction h a w := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restrict conjugation by K to the pair of core sections it carries to another pair. -/
noncomputable def pairSectionTransport (h : IsTypeJ4 z) (k : d.K)
    (t u t' u' : G) (ht : (k : G)*t*(k : G)⁻¹=t')
    (hu : (k : G)*u*(k : G)⁻¹=u') :
    (d.coreSection t ⊓ d.coreSection u : Subgroup (d.R ⧸ center d.R)) ≃*
      (d.coreSection t' ⊓ d.coreSection u' : Subgroup (d.R ⧸ center d.R)) :=
  ((d.KRadicalAction h (QuotientGroup.mk' _ k)).subgroupMap _).trans
    (MulEquiv.subgroupCongr (by
      rw [Subgroup.map_inf _ _ _ (d.KRadicalAction h (QuotientGroup.mk' _ k)).injective,
        d.KRadicalAction_mk,← MulEquiv.toMonoidHom_eq_coe,
        d.coreSection_conjugate,d.coreSection_conjugate]
      exact congrArg₂ (· ⊓ ·) (congrArg d.coreSection ht) (congrArg d.coreSection hu)))

@[simp] theorem pairSectionTransport_apply (h : IsTypeJ4 z) (k : d.K)
    (t u t' u' : G) (ht : (k : G)*t*(k : G)⁻¹=t')
    (hu : (k : G)*u*(k : G)⁻¹=u')
    (w : (d.coreSection t ⊓ d.coreSection u : Subgroup (d.R ⧸ center d.R))) :
    (d.pairSectionTransport h k t u t' u' ht hu w : d.R ⧸ center d.R) =
      d.KRadicalAction h (QuotientGroup.mk' _ k) w := rfl

/-- Conjugation transports the original pair section equivariantly for the same S/R. -/
theorem pairSectionTransport_intertwines (h : IsTypeJ4 z) (k : d.K)
    (t u : G) (ht : (k : G)*z*(k : G)⁻¹=t)
    (hu : (k : G)*d.r*(k : G)⁻¹=u)
    (a : d.S ⧸ d.R.subgroupOf d.S) (w : d.multiplicitySpace) :
    (d.pairSectionTransport h k z d.r t u ht hu (d.multiplicityAction h a w) :
        d.R ⧸ center d.R) =
      d.SRadicalAction h a (d.pairSectionTransport h k z d.r t u ht hu w) := by
  exact congrArg (fun f : MulAut (d.R ⧸ center d.R) => f w.val)
    (d.radical_factors_commute h (QuotientGroup.mk' _ k) a).eq

set_option backward.isDefEq.respectTransparency false in
/-- Three identical copies of the actual S/R module give the whole radical quotient. -/
theorem exists_multiplicity_coordinates (h : IsTypeJ4 z) :
    ∃ f : d.multiplicitySpace × (d.multiplicitySpace × d.multiplicitySpace) ≃*
        (d.R ⧸ center d.R),
      (∀ w, f (w,1,1) = (w : d.R ⧸ center d.R)) ∧
      ∀ a : d.S ⧸ d.R.subgroupOf d.S, ∀ u v w : d.multiplicitySpace,
        f (d.multiplicityAction h a u,d.multiplicityAction h a v,d.multiplicityAction h a w) =
          d.SRadicalAction h a (f (u,v,w)) := by
  classical
  obtain ⟨k,hk⟩ := d.exists_K_marked_permutation h (Equiv.swap 1 2)
  have hkz : (k : G)*z*(k : G)⁻¹=z := by simpa [markedPoint,Equiv.swap_apply_def] using hk 0
  have hkr : (k : G)*d.r*(k : G)⁻¹=d.s := by simpa [markedPoint,Equiv.swap_apply_def] using hk 1
  obtain ⟨l,hl⟩ := d.exists_K_marked_permutation h ((Equiv.swap 0 1)*(Equiv.swap 1 2))
  have hlz : (l : G)*z*(l : G)⁻¹=d.r := by simpa [markedPoint,Equiv.swap_apply_def] using hl 0
  have hlr : (l : G)*d.r*(l : G)⁻¹=d.s := by simpa [markedPoint,Equiv.swap_apply_def] using hl 1
  let b : d.multiplicitySpace ≃* (d.coreSection z ⊓ d.coreSection d.s : Subgroup (d.R ⧸ center d.R)) :=
    d.pairSectionTransport h k z d.r z d.s hkz hkr
  let c : d.multiplicitySpace ≃* (d.coreSection d.r ⊓ d.coreSection d.s : Subgroup (d.R ⧸ center d.R)) :=
    d.pairSectionTransport h l z d.r d.r d.s hlz hlr
  obtain ⟨f,hf⟩ := d.exists_coreSection_product h
  let e := ((MulEquiv.refl d.multiplicitySpace).prodCongr (b.prodCongr c)).trans f
  have he (u v w : d.multiplicitySpace) :
      e (u,v,w) = (u : d.R ⧸ center d.R)*((b v : d.R ⧸ center d.R)*(c w : d.R ⧸ center d.R)) :=
    hf u (b v) (c w)
  refine ⟨e,?_,?_⟩
  · intro w
    rw [he,map_one,map_one]
    simp
  · intro a u v w
    rw [he,he,map_mul,map_mul]
    exact congrArg₂ (· * ·) rfl (congrArg₂ (· * ·)
      (d.pairSectionTransport_intertwines h k z d.s hkz hkr a v)
      (d.pairSectionTransport_intertwines h l d.r d.s hlz hlr a w))

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
end

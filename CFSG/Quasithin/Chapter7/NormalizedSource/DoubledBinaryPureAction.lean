module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlaneQuotient
-- Reuse the small two-subgroup image count at its internal proof boundary.
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySylowFixed

/-!
# The H1 Sylow action modulo its actual pure line

The fixer of a pure line acts through the original inner SL₃(2). Its
restriction to the two-dimensional dual annihilator has image in S₃.
A two-subgroup therefore has a kernel of index at most two, acting
trivially on the perpendicular hyperplane modulo the same pure line.
The graph action supplies the other marked orientation.

The source join Z ∨ V₋ has order thirty-two, so it equals this invariant
hyperplane. We normalize this join, without imposing invariance on the
chosen rank-four complement. NonFFSourceDoubledBinaryPureAction applies
the result to the actual offender and original C_T(Z).
Source: Aschbacher–Smith, the H1 argument in 7.7.3, printed p.706,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureAction
open ChapterE BinaryLinearThree NaturalDual DoubledBinaryPlanes

private def annihilator (v : Vector) : Submodule (ZMod 2) (Module.Dual (ZMod 2) Vector) :=
  (Module.Dual.eval (ZMod 2) Vector v).ker

private theorem preserves_annihilator (v : Vector) (g : doubledBinaryVectorFixer W v)
    (f : annihilator v) : W.dual g f ∈ annihilator v := by
  change f.val (W (g : Group)⁻¹ v) = 0
  have he := congrArg (W (g : Group)⁻¹) g.property
  rw [W.inv_self_apply] at he
  rw [←he]
  exact f.property

private def pointAction (v : Vector) :
    doubledBinaryVectorFixer W v →* (annihilator v ≃ₗ[ZMod 2] annihilator v) where
  toFun g := {
    toFun f := ⟨W.dual g f, preserves_annihilator v g f⟩
    invFun f := ⟨W.dual (g⁻¹ : doubledBinaryVectorFixer W v) f,
      preserves_annihilator v g⁻¹ f⟩
    left_inv f := Subtype.ext (W.dual.inv_self_apply g f)
    right_inv f := Subtype.ext (W.dual.self_inv_apply g f)
    map_add' f k := Subtype.ext (map_add (W.dual g) f.val k.val)
    map_smul' c f := Subtype.ext (map_smul (W.dual g) c f.val) }
  map_one' := by
    apply LinearEquiv.ext
    intro f
    apply Subtype.ext
    exact congrArg (fun l : Module.End (ZMod 2) (Module.Dual (ZMod 2) Vector) => l f.val) W.dual.map_one
  map_mul' a b := by
    apply LinearEquiv.ext
    intro f
    apply Subtype.ext
    exact congrArg (fun l : Module.End (ZMod 2) (Module.Dual (ZMod 2) Vector) => l f.val) (W.dual.map_mul a b)

private def annihilatorAutEquiv (v : Vector) (hv : v ≠ 0) :
    (annihilator v ≃ₗ[ZMod 2] annihilator v) ≃* Equiv.Perm (Fin 3) := by
  have he : Module.Dual.eval (ZMod 2) Vector v ≠ 0 := by
    intro hh
    obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hv
    have he : f v = 0 := LinearMap.congr_fun hh f
    exact zero_ne_one (he.symm.trans hf)
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero he
  change Module.finrank (ZMod 2) (annihilator v) + 1 = _ at hd
  have hvd : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) Vector) = 3 := by
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  have hpd : Module.finrank (ZMod 2) BinaryFourPlus.Plane = 2 := by simp [BinaryFourPlus.Plane]
  let b : annihilator v ≃ₗ[ZMod 2] BinaryFourPlus.Plane := LinearEquiv.ofFinrankEq _ _ (by omega)
  let c : (annihilator v ≃ₗ[ZMod 2] annihilator v) ≃*
      (BinaryFourPlus.Plane ≃ₗ[ZMod 2] BinaryFourPlus.Plane) := {
    toFun e := b.symm.trans (e.trans b)
    invFun e := b.trans (e.trans b.symm)
    left_inv e := by ext x; simp
    right_inv e := by ext x; simp
    map_mul' e d := by ext x; simp }
  exact c.trans BinaryFourPlus.planeAutEquiv

private theorem kernel_displacement (v : Vector)
    (g : doubledBinaryVectorFixer W v) (hg : pointAction v g = 1)
    (x : Space) (hx : x.2 v = 0) :
    ∃ c : ZMod 2, action (g : Group) x - x = c • (v,0) := by
  have hfix (f : Module.Dual (ZMod 2) Vector) (hf : f v = 0) : W.dual g f = f :=
    congrArg Subtype.val (LinearEquiv.congr_fun hg ⟨f,hf⟩)
  have hspan : W g x.1 - x.1 ∈ Submodule.span (ZMod 2) ({v} : Set Vector) := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro f hf
    have hfv : f v = 0 := ((Submodule.mem_dualAnnihilator f).mp hf) v (Submodule.subset_span (by simp))
    have hh := LinearMap.congr_fun (hfix f hfv) (W g x.1)
    change f (W (g : Group)⁻¹ (W g x.1)) = f (W g x.1) at hh
    rw [W.inv_self_apply] at hh
    rw [map_sub,hh,sub_self]
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hspan
  exact ⟨c,Prod.ext hc.symm (by simpa using sub_eq_zero.mpr (hfix x.2 hx))⟩

/-- A two-group fixing a pure natural point has an index-at-most-two kernel
on its perpendicular hyperplane modulo the point. -/
theorem natural_point_two_kernel
    {S : Type*} [_root_.Group S] [Finite S] (hp : IsPGroup 2 S)
    (q : S →* Group) (v : Vector) (hv : v ≠ 0)
    (hfix : ∀ s, W (q s) v = v) :
    ∃ N : Subgroup S, N.index ≤ 2 ∧
      ∀ n ∈ N, ∀ x : Space, x.2 v = 0 →
        ∃ c : ZMod 2, action (q n) x - x = c • (v,0) := by
  let r : S →* doubledBinaryVectorFixer W v := q.codRestrict _ hfix
  let a := (pointAction v).comp r
  let b := (annihilatorAutEquiv v hv).toMonoidHom.comp a
  refine ⟨a.ker,?_,?_⟩
  · have he : b.ker = a.ker := by
      ext s
      change annihilatorAutEquiv v hv (a s) = 1 ↔ a s = 1
      rw [← (annihilatorAutEquiv v hv).map_one,(annihilatorAutEquiv v hv).injective.eq_iff]
    rw [← he,index_ker]
    exact DoubledBinarySylowFixed.two_image_card_le_two hp b
  · intro n hn x hx
    exact kernel_displacement v (r n) hn x hx


variable {G : Type*} [_root_.Group G]

/-- The full fixer of a nontrivial pure line acts through the original inner
SL₃(2), with the actual action equation retained. -/
theorem pureLine_inner_action
    (W₀ Z : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (a : Automizer W₀ ≃* MulAut Group)
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (action g (E w)))) =
      action (a b g) (E (automizerRepresentation W₀ b w)))
    (hZW : Z ≤ W₀) (hZ : Z ≠ ⊥)
    (hp : (∀ w : Additive W₀, (w.toMul : G) ∈ Z → (E w).2 = 0) ∨
      (∀ w : Additive W₀, (w.toMul : G) ∈ Z → (E w).1 = 0)) :
    ∃ q : (normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G) : Subgroup G) →* Group,
      ∀ (n : (normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G) : Subgroup G)) w, E (automizerRepresentation W₀
        (W₀.normalizerMonoidHom.rangeRestrict ⟨n,n.property.1⟩) w) = action (q n) (E w) := by
  let C := normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G)
  let r : C →* Automizer W₀ := W₀.normalizerMonoidHom.rangeRestrict.comp (inclusion inf_le_left)
  let op (n : C) := E.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv
    ((automizerRepresentation W₀).asGroupHom (r n))).trans E)
  have hc (n : C) (g : Group) (x : Space) : op n (action g x) = action (a (r n) g) (op n x) := by
    change E (automizerRepresentation W₀ (r n) (E.symm (action g x))) =
      action (a (r n) g) (E (automizerRepresentation W₀ (r n) (E.symm x)))
    simpa only [E.apply_symm_apply] using hcov (r n) g (E.symm x)
  obtain ⟨z,hz,hz1⟩ := (Z.bot_or_exists_ne_one).resolve_left hZ
  let w : Additive W₀ := Additive.ofMul ⟨z,hZW hz⟩
  have hw : E w ≠ 0 := by
    intro hh
    exact hz1 (congrArg (fun u : Additive W₀ => (u.toMul : G)) (E.map_eq_zero_iff.mp hh))
  have hi (n : C) : a (r n) ∈ MulAut.innerSubgroup Group := by
    by_contra hn
    have he : op n (E w) = E w := by
      change E (automizerRepresentation W₀ (r n) (E.symm (E w))) = E w
      rw [E.symm_apply_apply]
      congr 1
      apply Additive.toMul.injective
      apply Subtype.ext
      change (n : G) * z * (n : G)⁻¹ = z
      rw [← n.property.2 z hz,mul_inv_cancel_right]
    rcases hp with hp | hp
    · have hz2 := hp w hz
      have hh := (outer_swaps _ (op n) (hc n) hn).1 (E w).1
      rw [show ((E w).1,0) = E w from Prod.ext rfl hz2.symm,he] at hh
      exact hw (Prod.ext hh hz2)
    · have hz1 := hp w hz
      have hh := (outer_swaps _ (op n) (hc n) hn).2 (E w).2
      rw [show (0,(E w).2) = E w from Prod.ext hz1.symm rfl,he] at hh
      exact hw (Prod.ext hz1 hh)
  let e : Group ≃* MulAut.innerSubgroup Group := MonoidHom.ofInjective
    (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot)
  let q : C →* Group := e.symm.toMonoidHom.comp ((a.toMonoidHom.comp r).codRestrict _ hi)
  have hq (n : C) : MulAut.conj (q n) = a (r n) := congrArg Subtype.val (e.apply_symm_apply _)
  refine ⟨q,?_⟩
  intro n u
  have he : op n = innerOperator (q n) := implementing_unique _ _ _ (hc n)
    (fun g x => by rw [← hq]; exact innerOperator_covariance (q n) g x)
  have hh := LinearEquiv.congr_fun he (E u)
  change E (automizerRepresentation W₀ (r n) (E.symm (E u))) = action (q n) (E u) at hh
  have hrn : r n = W₀.normalizerMonoidHom.rangeRestrict ⟨n,n.property.1⟩ := rfl
  rw [E.symm_apply_apply,hrn] at hh
  exact hh

private def hyperplaneMap (v : Vector) : Space →ₗ[ZMod 2] ZMod 2 :=
  (Module.Dual.eval (ZMod 2) Vector v).comp (LinearMap.snd (ZMod 2) Vector _)

/-- On the actual perpendicular hyperplane, a two-group fixing a natural
line centralizes modulo that same line a subgroup of index at most two. -/
theorem naturalLine_hyperplane_action [Finite G]
    (W₀ Z R S : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (hZW : Z ≤ W₀) (hZ : Nat.card Z = 2)
    (hp : ∀ w : Additive W₀, (w.toMul : G) ∈ Z → (E w).2 = 0)
    (hR : R ≤ normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G))
    (hS : S ≤ normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G))
    (hpS : IsPGroup 2 S)
    (q : (normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G) : Subgroup G) →* Group)
    (hq : ∀ (n : (normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G) : Subgroup G)) w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict ⟨n,n.property.1⟩) w) = action (q n) (E w)) :
    ∃ X : Subgroup G, X ≤ W₀ ∧ Nat.card X = 32 ∧ Z ≤ X ∧ ⁅W₀,R⁆ ≤ X ∧
      S ≤ normalizer (X : Set G) ∧
      ∃ N : Subgroup S, N.index ≤ 2 ∧ ⁅N.map S.subtype,X⁆ ≤ Z := by
  obtain ⟨z,hz,hall⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  let w : Additive W₀ := Additive.ofMul ⟨z,hZW z.property⟩
  let v := (E w).1
  have hw2 : (E w).2 = 0 := hp w z.property
  have hw : E w = (v,0) := Prod.ext rfl hw2
  have hv : v ≠ 0 := by
    intro hh
    apply hz
    exact Subtype.ext (congrArg (fun u : Additive W₀ => (u.toMul : G))
      (E.map_eq_zero_iff.mp (Prod.ext hh hw2)))
  let C := normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G)
  have hfix (n : C) : W (q n) v = v := by
    have he : automizerRepresentation W₀
        (W₀.normalizerMonoidHom.rangeRestrict ⟨n,n.property.1⟩) w = w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (n : G) * (z : G) * (n : G)⁻¹ = z
      rw [← n.property.2 _ z.property,mul_inv_cancel_right]
    have hh := hq n w
    rw [he,hw] at hh
    exact (congrArg Prod.fst hh).symm
  have hform (n : C) (u : Additive W₀) :
      hyperplaneMap v (E (automizerRepresentation W₀
        (W₀.normalizerMonoidHom.rangeRestrict ⟨n,n.property.1⟩) u)) = hyperplaneMap v (E u) := by
    rw [hq]
    change (E u).2 (W (q n)⁻¹ v) = (E u).2 v
    have hi := congrArg (W (q n)⁻¹) (hfix n)
    rw [W.inv_self_apply] at hi
    rw [←hi]
  let p := (hyperplaneMap v).comp E.toLinearMap
  let X := ambientSubmodule W₀ p.ker
  have hmem (x : G) : x ∈ X ↔ ∃ hx : x ∈ W₀, (E (Additive.ofMul ⟨x,hx⟩)).2 v = 0 := by
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,hu⟩
    · rintro ⟨hx,hx0⟩
      exact ⟨⟨x,hx⟩,hx0,rfl⟩
  have hXW : X ≤ W₀ := map_subtype_le _
  have hcard : Nat.card X = 32 := by
    have hpne : p ≠ 0 := by
      obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hv
      intro hh
      have he := LinearMap.congr_fun hh (E.symm (0,f))
      change hyperplaneMap v (E (E.symm (0,f))) = 0 at he
      rw [E.apply_symm_apply] at he
      change f v = 0 at he
      exact zero_ne_one (he.symm.trans hf)
    have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hpne
    have hdW : Module.finrank (ZMod 2) (Additive W₀) = 6 := by
      rw [E.finrank_eq]
      simp [Space,Module.finrank_prod,BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    have hd5 : Module.finrank (ZMod 2) p.ker = 5 := by omega
    change Nat.card ((Chapter7.moduleSubgroup W₀ p.ker).map W₀.subtype) = 32
    rw [card_map_of_injective W₀.subtype_injective]
    change Nat.card p.ker = 32
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hd5,Nat.card_zmod]
    rfl
  have hZX : Z ≤ X := by
    intro x hx
    exact (hmem x).mpr ⟨hZW hx,by rw [hp (Additive.ofMul ⟨x,hZW hx⟩) hx]; rfl⟩
  have hRX : ⁅W₀,R⁆ ≤ X := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro r hr x hx
    let n : C := ⟨r,hR hr⟩
    let u : Additive W₀ := Additive.ofMul ⟨x,hx⟩
    let u' := automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict ⟨n,n.property.1⟩) u - u
    refine ⟨u'.toMul,?_,?_⟩
    · change hyperplaneMap v (E (_ - _)) = 0
      rw [map_sub,map_sub,hform,sub_self]
    · change (r*x*r⁻¹)/x = ⁅r,x⁆
      rw [div_eq_mul_inv]
      rfl
  have hSX : S ≤ normalizer (X : Set G) := by
    apply le_normalizer_iff.mpr
    intro s hs x hx
    obtain ⟨u,hu,rfl⟩ := hx
    let n : C := ⟨s,hS hs⟩
    refine ⟨(automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict ⟨n,n.property.1⟩) (Additive.ofMul u)).toMul,?_,rfl⟩
    exact (hform n (Additive.ofMul u)).trans hu
  obtain ⟨N,hN,hact⟩ := natural_point_two_kernel hpS (q.comp (inclusion hS)) v hv
    (fun s => hfix (inclusion hS s))
  refine ⟨X,hXW,hcard,hZX,hRX,hSX,N,hN,?_⟩
  apply commutator_le.mpr
  rintro _ ⟨n,hn,rfl⟩ x hx
  obtain ⟨hxW,hx0⟩ := (hmem x).mp hx
  let u : Additive W₀ := Additive.ofMul ⟨x,hxW⟩
  let b : Automizer W₀ := W₀.normalizerMonoidHom.rangeRestrict ⟨n,(hS n.property).1⟩
  obtain ⟨c,hc⟩ := hact n hn (E u) hx0
  have he : automizerRepresentation W₀ b u - u = c • w := by
    apply E.injective
    have heq := hq (inclusion hS n) u
    change E (automizerRepresentation W₀ b u) = action ((q.comp (inclusion hS)) n) (E u) at heq
    rw [map_sub,heq,map_smul,hw]
    exact hc
  have hcw : (((c • w).toMul : W₀) : G) ∈ Z := by
    rcases ((by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c) with rfl | rfl
    · rw [zero_smul]
      exact Z.one_mem
    · rw [one_smul]
      exact z.property
  have hh := congrArg (fun u : Additive W₀ => (u.toMul : G)) he
  change ((n : G)*x*(n : G)⁻¹)/x = _ at hh
  rw [div_eq_mul_inv] at hh
  change (n : G)*x*(n : G)⁻¹*x⁻¹ ∈ Z
  rw [hh]
  exact hcw


/-- Both marked orientations give the same literal hyperplane and modulo-line
Sylow action. The order-thirty-two join identifies that hyperplane, rather
than assuming that the chosen rank-four complement is Sylow invariant. -/
theorem pureLine_sylow_modulo [Finite G]
    (W₀ Z R S A : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (a : Automizer W₀ ≃* MulAut Group)
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (action g (E w)))) =
      action (a b g) (E (automizerRepresentation W₀ b w)))
    (hZW : Z ≤ W₀) (hZ : Nat.card Z = 2)
    (hp : (∀ w : Additive W₀, (w.toMul : G) ∈ Z → (E w).2 = 0) ∨
      (∀ w : Additive W₀, (w.toMul : G) ∈ Z → (E w).1 = 0))
    (hR : R ≤ normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G))
    (hS : S ≤ normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G))
    (hpS : IsPGroup 2 S) (hAR : A ≤ ⁅W₀,R⁆)
    (hcard : Nat.card (Z ⊔ A : Subgroup G) = 32) :
    S ≤ normalizer ((Z ⊔ A : Subgroup G) : Set G) ∧
      ∃ N : Subgroup S, N.index ≤ 2 ∧ ⁅N.map S.subtype,Z ⊔ A⁆ ≤ Z := by
  have hZne : Z ≠ ⊥ := by intro he; rw [he,card_bot] at hZ; omega
  obtain ⟨q,hq⟩ := pureLine_inner_action W₀ Z E a hcov hZW hZne hp
  have hex : ∃ X : Subgroup G, X ≤ W₀ ∧ Nat.card X = 32 ∧ Z ≤ X ∧ ⁅W₀,R⁆ ≤ X ∧
      S ≤ normalizer (X : Set G) ∧
      ∃ N : Subgroup S, N.index ≤ 2 ∧ ⁅N.map S.subtype,X⁆ ≤ Z := by
    rcases hp with hp | hp
    · exact naturalLine_hyperplane_action W₀ Z R S E hZW hZ hp hR hS hpS q hq
    · let E' := E.trans graphSwap
      let q' := AutomorphismAction.graph.toMonoidHom.comp q
      have hp' (w : Additive W₀) (hw : (w.toMul : G) ∈ Z) : (E' w).2 = 0 := by
        change AutomorphismAction.graphNaturalDual (E w).1 = 0
        rw [hp w hw,map_zero]
      have hq' (n : (normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G) : Subgroup G)) (w : Additive W₀) :
          E' (automizerRepresentation W₀
            (W₀.normalizerMonoidHom.rangeRestrict ⟨n,n.property.1⟩) w) = action (q' n) (E' w) := by
        change graphSwap (E _) = action (AutomorphismAction.graph (q n)) (graphSwap (E w))
        rw [hq,graphSwap_covariance]
      exact naturalLine_hyperplane_action W₀ Z R S E' hZW hZ hp' hR hS hpS q' hq'
  obtain ⟨X,_,hX,hZX,hRX,hSX,N,hN,hcomm⟩ := hex
  have he : Z ⊔ A = X := eq_of_le_of_card_ge (sup_le hZX (hAR.trans hRX))
    (by rw [hX,hcard])
  rw [he]
  exact ⟨hSX,N,hN,hcomm⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureAction

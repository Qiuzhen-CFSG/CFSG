module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearActor
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Coordinates
/-!
# The selected first component has the actual natural local model

The first-coordinate homomorphism identifies the literal local centralizer
quotient with SL₂. The original moved group maps onto its natural module;
the retained kernel is precisely the local fixed subgroup. These two
canonical quotient equivalences intertwine original conjugation and
construct the C.1.17 natural model, with no splitting assumption.

Source: Aschbacher–Smith C.1.17 and C.1.26, printed pp.126 and132.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.QuasisimpleSource ChapterB.RankOneBaumann.PairedFactorOrbit
variable {G H : Type*} [Group G] [Group H] [Finite G]
variable (F : BinaryField)
local notation "A" => Matrix.SpecialLinearGroup (Fin 2) F.Carrier
local notation "W" => Fin 2 → F.Carrier
theorem paired_first_natural_model
    (T U L : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hLp : IsPPerfect 2 L) (hUL : U ≤ normalizer (L : Set G))
    (hBL : baumann T ≤ normalizer (L : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (Y : Subgroup H) (e : Y ≃* A × A) (hA : IsPPerfect 2 A) [IsQuasisimple A]
    (hNY : (L ⊔ baumann T).map q ≤ Y)
    (hL : L.map q = (⊤ : Subgroup A).map (Y.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl A A))))
    (f : Additive U →ₗ[ZMod 2] (W × W)) (hf : Function.Surjective f)
    (hfk : f.ker ≤ fixedSpace (NormalElementaryQuotient.representation U q hq hk)
      (Y.subtype.comp e.symm.toMonoidHom).range)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hk
      ((Y.subtype.comp e.symm.toMonoidHom) g) v) =
      (linearNatural F 2 g.1 (f v).1,linearNatural F 2 g.2 (f v).2))
    (hv : (GlaubermanNiles.localV (inclusion (show baumann T ≤ L ⊔ baumann T from le_sup_right))).map
      (L ⊔ baumann T).subtype = ⁅U,L⁆ ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G))) :
    Nonempty (GlaubermanNiles.NaturalModel
      (inclusion (show baumann T ≤ L ⊔ baumann T from le_sup_right)) F.Carrier) := by
  let N := L ⊔ baumann T
  let b := inclusion (show baumann T ≤ N from le_sup_right)
  let α := NormalElementaryQuotient.representation U q hq hk
  let j := Y.subtype.comp e.symm.toMonoidHom
  let j₁ := j.comp (MonoidHom.inl A A)
  let r := pairedFirstActor q Y e N hNY
  obtain ⟨hrs,hrk⟩ := paired_first_actor_kernel F T U L q hq hk Y e hA hNY hL f hf hfk he hv
  let c : GlaubermanNiles.LocalStar b ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq hrk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hrs)
  have hc (n : N) : c (QuotientGroup.mk' (GlaubermanNiles.localKernel b) n) = r n := rfl
  let : IsQuasisimple (GlaubermanNiles.LocalStar b) := IsQuasisimple.of_mulEquiv c.symm
  have hactor : GlaubermanNiles.actorLift b = ⊤ := by
    unfold GlaubermanNiles.actorLift
    rw [generalizedFitting_eq_top_of_quasisimple,comap_top]
  have hmove : (GlaubermanNiles.moved b).map N.subtype = ⁅U,L⁆ := by
    unfold GlaubermanNiles.moved
    rw [hactor]
    exact localV_factor_full_commutator T U L hLp hUL hBL hv
  let k := ((GlaubermanNiles.moved b).equivMapOfInjective N.subtype N.subtype_injective).trans
    (MulEquiv.subgroupCongr hmove)
  let v (w : GlaubermanNiles.moved b) : Additive U :=
    Additive.ofMul ⟨(k w:G),(commutator_le_left U L) (k w).property⟩
  let p := (LinearMap.fst (ZMod 2) W W).comp f
  let g : GlaubermanNiles.moved b →* Multiplicative W :=
    p.toAddMonoidHom.toMultiplicativeRight.comp
      ((inclusion (commutator_le_left U L)).comp k.toMonoidHom)
  have hg (w : GlaubermanNiles.moved b) : (g w).toAdd = (f (v w)).1 := rfl
  let M := NormalElementaryQuotient.commutatorSpace U L
  have hres : pResidual 2 A = ⊤ := (pResidual_eq_top_iff 2 A).mpr hA
  have hm : M.map f = (⊤ : Submodule (ZMod 2) W).prod ⊥ := by
    change (NormalElementaryQuotient.commutatorSpace U L).map f = _
    rw [NormalElementaryQuotient.commutatorSpace_eq U q hq hk,hL,←hres]
    apply first_axis_moved_map F α j₁ f hf
    intro a v
    simpa only [j₁,j,MonoidHom.comp_apply,MonoidHom.inl_apply,map_one,Module.End.one_apply] using he (a,1) v
  have hvalue (n : N) : j (e ⟨q n,hNY (mem_map_of_mem q n.property)⟩) = q n :=
    congrArg Subtype.val (e.symm_apply_apply _)
  have hsecond (w : GlaubermanNiles.moved b) : (f (v w)).2 = 0 :=
    (hm.le (Submodule.mem_map_of_mem (show v w ∈ M from (k w).property))).2
  have hgs : Function.Surjective g := by
    intro z
    obtain ⟨u,hu,hfu⟩ := hm.ge (show (z.toAdd,0) ∈ (⊤ : Submodule (ZMod 2) W).prod ⊥ from
      ⟨Submodule.mem_top,Submodule.zero_mem _⟩)
    obtain ⟨w,hw⟩ := k.surjective (⟨u.toMul,hu⟩ : (⁅U,L⁆ : Subgroup G))
    refine ⟨w,?_⟩
    apply Multiplicative.toAdd.injective
    rw [hg]
    have hvw : v w = u := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (k w:G) = (u.toMul:G)
      exact congrArg (fun z : (⁅U,L⁆ : Subgroup G) => (z:G)) hw
    rw [hvw,hfu]
  have hgk : g.ker = GlaubermanNiles.movedFixed b := by
    ext w
    change g w = 1 ↔ (w:N) ∈ centralizer (GlaubermanNiles.actorLift b : Set N)
    constructor
    · intro hw n hn
      have hfzero : f (v w) = 0 := Prod.ext (by
        have hh := congrArg Multiplicative.toAdd hw
        exact hh) (hsecond w)
      have hfixed := hfk (show v w ∈ f.ker from hfzero)
        ⟨q (n:G),⟨e ⟨q n,hNY (mem_map_of_mem q n.property)⟩,hvalue n⟩⟩
      change α (q (n:G)) (v w) = v w at hfixed
      have hh := congrArg (fun u : Additive U => (u.toMul:G)) hfixed
      rw [NormalElementaryQuotient.representation_apply] at hh
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hh)
    · intro hw
      apply Multiplicative.toAdd.injective
      rw [hg]
      apply (ExtensionConsequences.linearNatural_invariants F (by decide)).le
      intro a
      obtain ⟨n,hn⟩ := hrs a
      have hfixed : α (q n) (v w) = v w := by
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [NormalElementaryQuotient.representation_apply]
        have hh := congrArg (fun x : N => (x:G)) (hw n (hactor.symm ▸ mem_top n))
        change (n:G)*(v w).toMul=(v w).toMul*(n:G) at hh
        rw [hh,mul_inv_cancel_right]
      have hh := congrArg (fun u => (f u).1) hfixed
      rw [←hvalue n,he] at hh
      change linearNatural F 2 (r n) (f (v w)).1 = (f (v w)).1 at hh
      rwa [hn] at hh
  apply naturalModel_of_star_coordinates b F.Carrier c g hgs hgk
  intro a w
  have hvc : v (GlaubermanNiles.movedConjugate b a w) = α (q ((a:N):G)) (v w) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    rfl
  rw [hg,hvc,hg,←hvalue a,he,hc]
  rfl
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne

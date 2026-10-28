module
public import Theory.Representation.BinaryPermutation.FivePairWreath
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric
public import Theory.Representation.NormalComponentConstituents
/-!
# The whole paired-five chief action

A faithful action extending the marked S₅ × S₅ natural layer normalizes its two
actual factors. Their intrinsic preserve-or-exchange dichotomy gives a concrete
wreath actor. The source Sylow exchanges them, so this actor is surjective, and
its base is exactly the original layer. On a faithful irreducible chief module
the layer has no fixed vectors, making its original quotient coordinates an
actual linear equivalence on the whole module.

Source: Aschbacher–Smith B.6.9, E.2.3(3), and 3.1.9(5).
-/
public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction BinaryPermutation BinaryPermutation.FiveCentralExtension
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

theorem source_pair_wreath_of_faithful_action
    (Y : Subgroup G) [Y.Normal] (α : Representation (ZMod 2) Y V)
    (d : SourceTwoFactorCase α) (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (hcore : pCore 2 Y = ⊥)
    (ρ : Representation (ZMod 2) G (FivePair.Core × FivePair.Core))
    (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : Y) v, ρ (g : G) v = FivePair.action (c.action.groupEquiv g) v)
    (hex : ∃ t : G, d.first.map (MulAut.conjNormal t).toMonoidHom = d.second) :
    ∃ e : G ≃* FivePair.Wreath,
      (∀ g v, ρ g v = FivePair.wreathRepresentation (e g) v) ∧
      Y.map e.toMonoidHom = FivePair.baseSubgroup := by
  classical
  let e := c.action.groupEquiv
  let j := Y.subtype.comp e.symm.toMonoidHom
  let r : G →* ((FivePair.Core × FivePair.Core) ≃ₗ[ZMod 2] (FivePair.Core × FivePair.Core)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).toMonoidHom.comp ρ.asGroupHom
  have hr (g : G) (v : FivePair.Core × FivePair.Core) : r g v = ρ g v := rfl
  have hexw (x : G) : ∃ w : FivePair.Wreath, FivePair.wreathToLinear w = r x := by
    let ψ : MulAut Y := MulAut.conjNormal x
    let φ : MulAut (Sym × Sym) := e.symm.trans (ψ.trans e)
    have hact (g : Sym × Sym) (v : FivePair.Core × FivePair.Core) :
        r x (FivePair.action g v) = FivePair.action (φ g) (r x v) := by
      have hg (g : Sym × Sym) (v : FivePair.Core × FivePair.Core) : ρ (j g) v = FivePair.action g v := by
        have hh := hnat (e.symm g) v
        change ρ (j g) v = FivePair.action (e (e.symm g)) v at hh
        rw [e.apply_symm_apply] at hh
        exact hh
      change ρ x (FivePair.action g v) = FivePair.action (φ g) (ρ x v)
      rw [←hg g v,←hg (φ g) (ρ x v)]
      have he : j (φ g) = x * j g * x⁻¹ := by
        change ((e.symm (e (ψ (e.symm g))) : Y) : G) = _
        rw [e.symm_apply_apply]
        rfl
      rw [he]
      simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
    have hmap (A : Subgroup (Sym × Sym)) :
        (A.map φ.toMonoidHom).map e.symm.toMonoidHom =
          (A.map e.symm.toMonoidHom).map ψ.toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro g
      exact e.symm_apply_apply _
    apply FivePair.normalizer_wreath (r x) φ hact
    rcases d.automorphism_permutation hcore ψ with h | h
    · left
      constructor
      · apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
        rw [hmap,c.first_eq]
        exact h.1
      · apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
        rw [hmap,c.second_eq]
        exact h.2
    · right
      constructor
      · apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
        rw [hmap,c.first_eq,c.second_eq]
        exact h.1
      · apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
        rw [hmap,c.second_eq,c.first_eq]
        exact h.2
  let q : G →* FivePair.Wreath :=
    { toFun := fun g => (hexw g).choose
      map_one' := by
        apply FivePair.wreathToLinear_injective
        rw [(hexw 1).choose_spec,map_one,map_one]
      map_mul' := fun a b => by
        apply FivePair.wreathToLinear_injective
        exact (hexw (a*b)).choose_spec.trans ((r.map_mul a b).trans
          ((congrArg₂ (· * ·) (hexw a).choose_spec.symm (hexw b).choose_spec.symm).trans
            (FivePair.wreathToLinear.map_mul _ _).symm)) }
  have hq (g : G) : FivePair.wreathToLinear (q g) = r g := (hexw g).choose_spec
  have hqinj : Function.Injective q := by
    intro a b hab
    apply hfaith
    apply LinearMap.ext
    intro v
    exact congrArg (fun z : (FivePair.Core × FivePair.Core) ≃ₗ[ZMod 2] (FivePair.Core × FivePair.Core) => z v)
      ((hq a).symm.trans ((congrArg FivePair.wreathToLinear hab).trans (hq b)))
  have hqbase (g : Y) : q (g : G) = FivePair.base (e g) := by
    apply FivePair.wreathToLinear_injective
    apply LinearEquiv.ext
    intro v
    rw [hq,hr,FivePair.wreathToLinear_base]
    exact hnat g v
  have hbase (a : Sym × Sym) : ∃ g : G, q g = FivePair.base a := by
    refine ⟨e.symm a,?_⟩
    rw [hqbase,e.apply_symm_apply]
  have htout : ∃ t : G, (q t).right ≠ 1 := by
    obtain ⟨t,ht⟩ := hex
    refine ⟨t,?_⟩
    intro htq
    have htb := FivePair.base_coordinates (q t) htq
    obtain ⟨g,hg⟩ := e.surjective ((q t).left 1,(q t).left FivePair.swapIndex)
    have hgt : (g : G) = t := hqinj (by rw [hqbase,hg,htb])
    let : d.first.Normal := d.product.swap.second_normal
    have hc : (MulAut.conjNormal t : MulAut Y) = MulAut.conj g := by
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      change t * (y:G) * t⁻¹ = (g:G) * (y:G) * (g:G)⁻¹
      rw [hgt]
    rw [hc] at ht
    have he : d.first = d.second := (Normal.map_conj_eq d.first g).symm.trans ht
    have hb : d.first = ⊥ := by
      have hd := d.product.disjoint.eq_bot
      rw [←he,inf_idem] at hd
      exact hd
    exact (d.first.nontrivial_iff_ne_bot.mp d.firstCase.nontrivial) hb
  have hqsurj := FivePair.range_eq_top_of_base_and_exchange q hbase htout
  refine ⟨MulEquiv.ofBijective q ⟨hqinj,hqsurj⟩,?_,?_⟩
  · intro g v
    exact (congrArg (fun z : (FivePair.Core × FivePair.Core) ≃ₗ[ZMod 2] (FivePair.Core × FivePair.Core) => z v) (hq g)).symm
  · apply le_antisymm
    · rintro _ ⟨g,hg,rfl⟩
      change (q g).right = 1
      rw [hqbase ⟨g,hg⟩]
      rfl
    · intro w hw
      have hw' : w.right = 1 := hw
      obtain ⟨g,hg⟩ := e.surjective (w.left 1,w.left FivePair.swapIndex)
      refine ⟨g,g.property,?_⟩
      change q (g:G) = w
      rw [hqbase,hg,FivePair.base_coordinates w hw']

variable [FiniteDimensional (ZMod 2) V]

/-- The original faithful irreducible paired-five chief action is the whole wreath
module. Its original offender subgroup is exactly the coordinatewise base. -/
theorem source_two_factor_five_whole_action
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (hf : Function.Injective ρ) (T : Sylow 2 G)
    (hP : IsMinimalParabolicOver T ⊤) (hff : IsFFModule ρ)
    (hcore : pCore 2 G = ⊥)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5))) :
    ∃ e : ActionEquiv ρ FivePair.wreathRepresentation,
      (offenderSubgroup ρ).map e.groupEquiv.toMonoidHom = FivePair.baseSubgroup ∧
      e.linearEquiv.toLinearMap = c.symmetricCoreMap := by
  let Y := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  let : Nontrivial Y := c.action.groupEquiv.symm.injective.nontrivial
  have hne : Y ≠ ⊥ := Y.nontrivial_iff_ne_bot.mp inferInstance
  have hfix : Representation.invariants (ρ.comp Y.subtype) = ⊥ :=
    fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf inferInstance Y hne
  have hcY : pCore 2 Y = ⊥ := by
    have hle : (pCore 2 Y).map Y.subtype ≤ pCore 2 G :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map Y.subtype⟩
    rw [hcore] at hle
    apply (map_eq_bot_iff_of_injective (pCore 2 Y) Y.subtype_injective).mp
    exact le_bot_iff.mp hle
  have hfmap : Function.Injective c.symmetricCoreMap := LinearMap.ker_eq_bot.mp
    (c.symmetricCoreMap_ker.trans hfix)
  let f := LinearEquiv.ofBijective c.symmetricCoreMap ⟨hfmap,c.symmetricCoreMap_surjective⟩
  let τ : Representation (ZMod 2) G (FivePair.Core × FivePair.Core) :=
    f.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (g : G) (v : V) : f (ρ g v) = τ g (f v) := by
    change f (ρ g v) = f (ρ g (f.symm (f v)))
    rw [f.symm_apply_apply]
  have htfaith : Function.Injective τ := f.conjRingEquiv.injective.comp hf
  have hnat (g : Y) (v : FivePair.Core × FivePair.Core) :
      τ (g:G) v = FivePair.action (c.action.groupEquiv g) v := by
    obtain ⟨w,rfl⟩ := f.surjective v
    rw [←hτ]
    exact c.symmetricCoreMap_action g w
  obtain ⟨t,ht,_⟩ := source_offender_two_factor_exists_sylow_exchange ρ T hP hff hcore d
  obtain ⟨eG,he,hbase⟩ := source_pair_wreath_of_faithful_action Y (ρ.comp Y.subtype)
    d c hcY τ htfaith hnat ⟨t,ht⟩
  refine ⟨⟨eG,f,fun g v => (hτ g v).trans (he g (f v))⟩,hbase,rfl⟩

end CFSG.Quasithin.ChapterB

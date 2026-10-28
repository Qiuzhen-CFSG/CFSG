module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledLinearNearOffendersFixed
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledLinearNearOffendersOddAxes
public import Theory.Representation.SL3.TwistedPairOddDisplacement
public import Theory.Representation.BinaryOffender.InnerNormalizerActors

/-!
# H.4 odd displacement for an actual covered pair normalizer

Odd actors preserve the two inequivalent original simple axes. Restrict the
original covering group to the preserving subgroup of its literal image,
and use the two actual block actions there. The original SL₃ remains marked
in that image. Natural/dual coordinates and the covered beta calculation
then give four field degrees, retaining rank on the covering subgroup.
Source: Aschbacher--Smith H.4.1, printed pp.377--379 and383--385.
-/
public noncomputable section
open Representation Subgroup Module Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterB.QuasisimpleSource

private def axesSubgroup {H U W : Type*} [Group H]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (π : Representation (ZMod 2) H (U × W)) : Subgroup H where
  carrier := {x | (∀ u, (π x (u,0)).2=0) ∧ (∀ w, (π x (0,w)).1=0)}
  one_mem' := by constructor <;> intro v <;> rw [map_one] <;> rfl
  mul_mem' := by
    intro x y hx hy
    constructor
    · intro u
      rw [map_mul,Module.End.mul_apply,
        show π y (u,0)=((π y (u,0)).1,0) from Prod.ext rfl (hy.1 u)]
      exact hx.1 _
    · intro w
      rw [map_mul,Module.End.mul_apply,
        show π y (0,w)=(0,(π y (0,w)).2) from Prod.ext (hy.2 w) rfl]
      exact hx.2 _
  inv_mem' := by
    intro x hx
    have he (v : U × W) : π x v=((π x (v.1,0)).1,(π x (0,v.2)).2) := by
      have hv : v=(v.1,0)+(0,v.2) := by simp
      calc
        π x v=π x (v.1,0)+π x (0,v.2) := by rw [←map_add,←hv]
        _=_ := Prod.ext (by simpa using hx.2 v.2) (by simpa using hx.1 v.1)
    have hi := (LinearMap.GeneralLinearGroup.toLinearEquiv (π.asGroupHom x)).injective
    constructor
    · intro u
      let v := π x⁻¹ (u,0)
      have hv : π x v=(u,0) := π.self_inv_apply x (u,0)
      have hz : π x (0,v.2)=0 := Prod.ext (hx.2 v.2)
        (by have hh := congrArg Prod.snd hv; rw [he] at hh; exact hh)
      exact congrArg Prod.snd (hi (hz.trans (map_zero (π x)).symm))
    · intro w
      let v := π x⁻¹ (0,w)
      have hv : π x v=(0,w) := π.self_inv_apply x (0,w)
      have hz : π x (v.1,0)=0 := Prod.ext
        (by have hh := congrArg Prod.fst hv; rw [he] at hh; exact hh) (hx.1 v.1)
      exact congrArg Prod.fst (hi (hz.trans (map_zero (π x)).symm))

/-- H.4 beta for a normalizer image covered by the original rank-two group.
The full normalizer itself is not assigned an odd-rank bound. -/
theorem doubledLinear_normalizer_odd_displacement_of_cover (F : BinaryField)
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
    (hne : ¬ Nonempty ((linearNatural F 3).Equiv
      ((linearNatural F 3).comp a.toMonoidHom)))
    {K : Type*} [Group K] [Finite K]
    (f : K →* linearNormalizer
      ((linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom)))
    (hinner : ∀ g, normalizerEmbedding
      ((linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom)) g ∈ f.range)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hrank : primeRank p K ≤ 2)
    (x : linearNormalizer
      ((linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom)))
    (hx : orderOf x=p) (hxim : x ∈ f.range) :
    4*F.degree ≤ fixedCodim (normalizerRepresentation
      ((linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom))) (zpowers x) := by
  let W := Fin 3 → F.Carrier
  let σ := linearNatural F 3
  let τ := σ.comp a.toMonoidHom
  let μ := σ.prod τ
  let N := linearNormalizer μ
  let π := normalizerRepresentation μ
  let : IsIrreducible σ := ExtensionConsequences.linearNatural_irreducible F (by decide)
  let : IsIrreducible τ := (irreducible_comp_surjective_iff
    a.toMonoidHom a.surjective σ).mpr inferInstance
  have hi : Function.Injective (actionHom μ) := by
    intro g k hgk
    apply specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    exact congrArg (fun z : actionImage μ => (z.val.val (v,0)).1) hgk
  let e := MulEquiv.ofBijective (actionHom μ) ⟨hi,μ.asGroupHom.rangeRestrict_surjective⟩
  let α := (MulAut.congr e.symm).toMonoidHom.comp (actionImage μ).normalizerMonoidHom
  have heα (y : N) (g) : e (α y g) = (actionImage μ).normalizerMonoidHom y (e g) := by
    change e (e.symm ((actionImage μ).normalizerMonoidHom y (e g))) = _
    rw [e.apply_symm_apply]
  have hπ (y : N) (g) (v : W × W) : π y (μ g v)=μ (α y g) (π y v) := by
    have hh := congrArg Subtype.val (heα y g)
    change μ.asGroupHom (α y g)=y.val*μ.asGroupHom g*y.val⁻¹ at hh
    exact congrArg (fun z : (Module.End (ZMod 2) (W × W))ˣ => z.val v)
      (mul_inv_eq_iff_eq_mul.mp hh.symm)
  let P := f.range ⊓ axesSubgroup π
  have hxP : x ∈ P := by
    refine ⟨hxim,?_⟩
    let E := LinearMap.GeneralLinearGroup.toLinearEquiv x.val
    have ho : orderOf E=p :=
      (orderOf_injective (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (W × W)).toMonoidHom
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (W × W)).injective x.val).trans
      ((orderOf_injective N.subtype N.subtype_injective x).trans hx)
    exact irreducible_pair_odd_order_preserves_axes σ τ hne (α x) E (hπ x) (ho ▸ hodd)
  let j₀ := normalizerEmbedding μ
  have hjP (g : Matrix.SpecialLinearGroup (Fin 3) F.Carrier) : j₀ g ∈ P := by
    refine ⟨hinner g,?_,?_⟩
    · intro u
      change τ g 0=0
      exact map_zero _
    · intro w
      change σ g 0=0
      exact map_zero _
  let j := j₀.codRestrict P hjP
  let πP := π.comp P.subtype
  obtain ⟨β,γ,hblocks⟩ := pair_preserving_block_representations πP (fun y => y.property.2)
  have hfi : Function.Injective (β.prod γ) := by
    rw [←hblocks]
    intro y z heq
    apply Subtype.ext
    apply Subtype.ext
    exact Units.ext heq
  let αP := α.comp P.subtype
  have hβ (y : P) (g) (v : W) : β y (specialLinearNatural 3 g v)=
      specialLinearNatural 3 (αP y g) (β y v) := by
    have hh := congrArg Prod.fst (hπ y.val g (v,0))
    change (πP y (μ g (v,0))).1=(μ (αP y g) (πP y (v,0))).1 at hh
    rw [hblocks] at hh
    exact hh
  have hγ (y : P) (g) (v : W) : γ y (σ (a g) v)=σ (a (αP y g)) (γ y v) := by
    have hh := congrArg Prod.snd (hπ y.val g (0,v))
    change (πP y (μ g (0,v))).2=(μ (αP y g) (πP y (0,v))).2 at hh
    rw [hblocks] at hh
    exact hh
  obtain ⟨d,hd⟩ := doubledLinear_second_dual_coordinates F a hne
  have hjβ (g) (v : W) : β (j g) v=specialLinearNatural 3 g v := by
    have hh : πP (j g) (v,0)=μ g (v,0) := rfl
    rw [hblocks] at hh
    exact congrArg Prod.fst hh
  have hjγ (g) (v : W) : γ (j g) v=specialLinearNatural 3 (a g) v := by
    have hh : πP (j g) (0,v)=μ g (0,v) := rfl
    rw [hblocks] at hh
    exact congrArg Prod.snd hh
  let q := f.subgroupComap P
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨k,hk⟩ := y.property.1
    exact ⟨⟨k,by change f k ∈ P; rw [hk]; exact y.property⟩,Subtype.ext hk⟩
  let xP : P := ⟨x,hxP⟩
  have hxorder : orderOf xP=p :=
    (orderOf_injective P.subtype P.subtype_injective xP).symm.trans hx
  have hbnd := SL3NaturalFixed.twisted_pair_odd_displacement_of_cover a d hd β γ hfi αP hβ hγ q hqs j
    hjβ hjγ hp hodd ((primeRank_subgroup_le p (P.comap f)).trans hrank) xP hxorder
  rw [←hblocks] at hbnd
  have hn := fixedCodim_map_equivariant πP π P.subtype (LinearEquiv.refl _ _) (fun _ _ => rfl) (zpowers xP)
  rw [MonoidHom.map_zpowers] at hn
  rw [hn] at hbnd
  have hF : finrank (ZMod 2) F.Carrier=F.degree := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
    rw [Nat.card_zmod,F.card_eq] at hh
    exact (Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hh).symm
  rw [hF] at hbnd
  exact hbnd
end CFSG.Quasithin.Chapter7.NormalizedSource

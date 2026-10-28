module
public import Theory.SpecificGroups.SymplecticSix.LocalOrder
public import Theory.SpecificGroups.SymplecticSix.FanoCore
public import Theory.LinearAlgebra.BinaryLagrangianKernel
public import Theory.Representation.PSL3Two.NaturalDualCoreObstruction
public import Theory.Representation.PSL3Two.NaturalDualNormalizerMarking
public import Theory.ElementaryAbelian.Quotient
public import Theory.Representation.BinaryGroupAction

/-!
# Excluding the symplectic-six placed component for the binary doubled orbit

An order-64 two-subgroup whose normalizer has order divisible by seven
fixes a Lagrangian in the actual binary symplectic six-space. Its pointwise
fixer has order at most 64: displacement is determined by a symmetric
three-by-three matrix, with six independent binary entries. The injective
Fano shear construction therefore identifies the whole subgroup with the
six-dimensional seven-point permutation core.

For an actor inducing the split natural-plus-dual SL₃(2) action, restriction
to that Lagrangian constructs a second SL₃(2) marking. The original quotient
factors through this marking and gives an automorphism of SL₃(2). Transport
by its canonical natural-dual operator would identify the nonsplit Fano
core with the split natural-plus-dual module, contradicting its proved
simple-head obstruction. No Sylow containment or parabolic normality is
assumed.

The Chapter12 companion applies this to the entire original orbit through
the component's full central quotient. Source: Aschbacher--Smith 4.4.12,
printed pp.621--622, used by 7.3.4 and 7.6.1, pp.699,702,
refs/quasithin.pdf. The reused transvection construction retains its ATLAS
attribution and license in Theory/SpecificGroups/SymplecticSix/FanoCore.lean
and LICENSES/ATLAS.txt.
-/

open Subgroup Representation
open Theory.SpecificGroups.SymplecticSix
open Theory.SpecificGroups.SymplecticSix.TwoLocalCover
public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedSymplectic
local notation "F" => ZMod 2
local notation "V" => Theory.SpecificGroups.SymplecticSix.Vector F

private theorem form_symm (x y : V) : form F x y = form F y x := by
  simpa only [CharTwo.neg_eq] using (@form_alternating (ZMod 2) _).neg_eq x y

/-- The pointwise fixer in the actual symplectic matrix group. -/
@[expose] def pointwise (W : Submodule F V) : Subgroup (Sp F) :=
  (fixingSubgroup (Sp F) (W : Set V))

private theorem pointwise_mem (W : Submodule F V) (g : Sp F) :
    g ∈ pointwise W ↔ ∀ w ∈ W, g • w = w := by
  exact mem_fixingSubgroup_iff (Sp F)

private theorem displacement_mem (W : Submodule F V)
    (hW : (form F).orthogonal W = W) (g : pointwise W) (x : V) :
    (g : Sp F) • x - x ∈ W :=
  Theory.LinearAlgebra.binary_lagrangian_displacement (form F) W hW
    (toLinear g.val) (preserves_form g.val) ((pointwise_mem W _).mp g.property) x

private theorem displacement_symm (W : Submodule F V)
    (hW : (form F).orthogonal W = W) (g : pointwise W) (x y : V) :
    form F ((g : Sp F) • x - x) y = form F x ((g : Sp F) • y - y) := by
  have hi : form F ((g : Sp F) • x - x) ((g : Sp F) • y - y) = 0 := by
    have hh := displacement_mem W hW g y
    have hh' : g.val • y - y ∈ (form F).orthogonal W := hW.symm ▸ hh
    exact hh' _ (displacement_mem W hW g x)
  have hp := preserves_form g.val x y
  simp only [map_sub,LinearMap.sub_apply,hp,form_symm] at hi ⊢
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) -hi

private theorem symmetric_card :
    Nat.card {M : Matrix (Fin 3) (Fin 3) F // M.transpose = M} = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- A binary Lagrangian in six-space has pointwise fixer of order at most 64. -/
theorem pointwise_card_le (W : Submodule F V)
    (hW : (form F).orthogonal W = W) (hd : Module.finrank F W = 3) :
    Nat.card (pointwise W) ≤ 64 := by
  let b : BinaryLinearThree.Vector ≃ₗ[F] W := LinearEquiv.ofFinrankEq _ _ (by
    simp [BinaryLinearThree.Vector,hd])
  let emb : BinaryLinearThree.Vector →ₗ[F] V := W.subtype.comp b.toLinearMap
  have hi : Function.Injective emb := Subtype.val_injective.comp b.injective
  have hx : ∀ i : Fin 3, ∃ x : V, ∀ v : BinaryLinearThree.Vector,
      form F x (emb v) = v i := by
    intro i
    obtain ⟨φ,hφ⟩ := LinearMap.dualMap_surjective_of_injective hi (LinearMap.proj i)
    refine ⟨((form F).toDual form_nondegenerate).symm φ,?_⟩
    intro v
    exact ((form F).apply_toDual_symm_apply φ (emb v)).trans (LinearMap.congr_fun hφ v)
  choose x hx using hx
  let d (g : pointwise W) (v : V) : W := ⟨g.val • v-v,displacement_mem W hW g v⟩
  let M (g : pointwise W) : Matrix (Fin 3) (Fin 3) F := fun i j => b.symm (d g (x j)) i
  have hm (g : pointwise W) : (M g).transpose = M g := by
    ext i j
    change b.symm (d g (x i)) j = b.symm (d g (x j)) i
    have hh := displacement_symm W hW g (x i) (x j)
    have hhx (v : W) (i : Fin 3) : form F (x i) v = b.symm v i := by
      simpa only [emb,LinearMap.comp_apply,LinearEquiv.coe_coe,b.apply_symm_apply,
        Submodule.subtype_apply] using hx i (b.symm v)
    rw [form_symm (g.val • x i - x i),hhx (d g (x i)) j,hhx (d g (x j)) i] at hh
    exact hh
  let f (g : pointwise W) : {m : Matrix (Fin 3) (Fin 3) F // m.transpose=m} := ⟨M g,hm g⟩
  have hf : Function.Injective f := by
    intro g k h
    have he : M g = M k := congrArg Subtype.val h
    have hj (i : Fin 3) : d g (x i) = d k (x i) := by
      apply b.symm.injective
      funext j
      exact congrFun (congrFun he j) i
    apply Subtype.ext
    apply Matrix.PSp4Three.ext_action
    intro v
    have hv : d g v = d k v := by
      apply b.symm.injective
      funext i
      have hh (a : pointwise W) : b.symm (d a v) i = form F v (d a (x i)) := by
        have hq := displacement_symm W hW a v (x i)
        rw [form_symm (a.val • v-v)] at hq
        have hx' := hx i (b.symm (d a v))
        change form F (x i) (b (b.symm (d a v))) = _ at hx'
        rw [b.apply_symm_apply] at hx'
        exact hx'.symm.trans hq
      rw [hh g,hh k,hj]
    exact sub_left_injective (congrArg Subtype.val hv)
  exact symmetric_card ▸ Nat.card_le_card_of_injective f hf

private theorem three_of_seven (W : Submodule F V) (hne : W ≠ ⊥)
    (hd : Module.finrank F W ≤ 3) (h7 : 7 ∣ Nat.card (stabilizer W)) :
    Module.finrank F W = 3 := by
  by_contra hdim
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := stabilizer W) 7 h7
  have hg' : orderOf g.val = 7 := (Subgroup.orderOf_coe g).trans hg
  let ρ : Representation F (zpowers g.val) V :=
    (symplecticNatural 3).comp (zpowers g.val).subtype
  have hs : ∀ a : zpowers g.val, ∀ x ∈ W, ρ a x ∈ W := by
    intro a x hx
    exact (mem_stabilizer_iff W a.val).mp ((zpowers_le.mpr g.property) a.property) x hx
  let σ := ρ.subrepresentation W hs
  have hh := BinaryOffender.orderOf_two_dvd_fixedCodim_of_isPGroup σ
    (by decide : Nat.Prime 7) (by decide) ⊤
    ((IsPGroup.of_card (p:=7) (n:=1)
      (by simpa only [Nat.card_zpowers,pow_one] using hg')).to_subgroup ⊤)
  rw [BinaryPrimeDegree.orderOf_two_mod_seven] at hh
  have hb := BinaryOffender.fixedCodim_add_finrank σ ⊤
  have hz : BinaryOffender.fixedCodim σ ⊤ = 0 := by omega
  have ht : BinaryOffender.fixedSpace σ ⊤ = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  apply hne
  apply bot_unique
  intro x hx
  have hfix : x ∈ BinaryOffender.fixedSpace (symplecticNatural 3) (zpowers g.val) := by
    intro a
    exact congrArg Subtype.val
      ((show (⟨x,hx⟩ : W) ∈ BinaryOffender.fixedSpace σ ⊤ from ht ▸ Submodule.mem_top)
        ⟨a,mem_top a⟩)
  rwa [fixedSpace_seven_eq_bot g.val hg'] at hfix

/-- Seven in the normalizer identifies the entire order-64 two-subgroup
with the pointwise fixer of a Lagrangian. -/
theorem sixtyFour_pointwise (E : Subgroup (Sp F)) (hE : IsPGroup 2 E)
    (hc : Nat.card E = 64) (h7 : 7 ∣ Nat.card (normalizer (E : Set (Sp F)))) :
    ∃ W : Submodule F V, (form F).orthogonal W = W ∧ Module.finrank F W = 3 ∧
      E = pointwise W ∧ normalizer (E : Set (Sp F)) ≤ stabilizer W := by
  have hne : E ≠ ⊥ := by intro he; rw [he,card_bot] at hc; omega
  let W := fixedRadical E
  have hW := fixedRadical_ne_bot E hne hE
  have hiso : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0 :=
    fun x hx y hy => fixedRadical_isotropic E x y hx hy
  have hn := normalizer_le_fixedRadical_stabilizer E
  have hd := three_of_seven W hW (finrank_le_three_of_isotropic W hiso)
    (h7.trans (card_dvd_of_le hn))
  have ho : (form F).orthogonal W = W := by
    apply (Submodule.eq_of_le_of_finrank_eq
      (show W ≤ (form F).orthogonal W from fun x hx y hy => hiso y hy x hx) ?_).symm
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,hd]
    simp [Theory.SpecificGroups.SymplecticSix.Vector]
  refine ⟨W,ho,hd,?_,hn⟩
  apply eq_of_le_of_card_ge
  · intro g hg
    exact (pointwise_mem W g).mpr (fun x hx => hx.1 g hg)
  · rw [hc]
    exact pointwise_card_le W ho hd

private theorem core_card : Nat.card (Multiplicative BinaryLinearThree.Core) = 64 := by
  let : Nonempty BinaryLinearThree.Point := ⟨Matrix.PSL3Two.flagPoint⟩
  change Nat.card BinaryLinearThree.Core = 64
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,
    BinaryPermutation.finrank_core,Matrix.PSL3Two.Fano.card_point]
  rfl

/-- The faithful Fano shear is the whole pointwise fixer, in the chosen
coordinates on the same Lagrangian. -/
theorem shear_range (W : Submodule F V)
    (ho : (form F).orthogonal W = W) (hd : Module.finrank F W = 3)
    (b : BinaryLinearThree.Vector ≃ₗ[F] W) :
    (BinaryLinearThree.FanoTransvection.shear (W.subtype.comp b.toLinearMap)
      (fun v w => (show (b w : V) ∈ (form F).orthogonal W from ho.symm ▸ (b w).property)
        (b v) (b v).property)).range = pointwise W := by
  let emb := W.subtype.comp b.toLinearMap
  have hi : Function.Injective emb := Subtype.val_injective.comp b.injective
  have hiso (v w : BinaryLinearThree.Vector) : form F (emb v) (emb w) = 0 :=
    (show (b w : V) ∈ (form F).orthogonal W from ho.symm ▸ (b w).property) (b v) (b v).property
  let sh := BinaryLinearThree.FanoTransvection.shear emb hiso
  change sh.range = pointwise W
  apply eq_of_le_of_card_ge
  · rintro _ ⟨a,rfl⟩
    apply (pointwise_mem W _).mpr
    intro x hx
    obtain ⟨v,hv⟩ := b.surjective ⟨x,hx⟩
    have hv' : emb v = x := congrArg Subtype.val hv
    rw [←hv']
    change BinaryLinearThree.FanoTransvection.shearElement emb hiso a.toAdd • emb v = emb v
    rw [BinaryLinearThree.FanoTransvection.shearElement_apply,
      BinaryLinearThree.FanoTransvection.displacement_on_range _ _ hiso,add_zero]
  · have hh := Nat.card_congr (MonoidHom.ofInjective
        (BinaryLinearThree.FanoTransvection.shear_injective emb hiso hi)).toEquiv
    rw [core_card] at hh
    rw [←hh]
    exact pointwise_card_le W ho hd

private def modelEquiv : BinaryLinearThree.Group ≃*
    (BinaryLinearThree.Vector ≃ₗ[F] BinaryLinearThree.Vector) :=
  (Matrix.PSL3Two.equivGL.trans Matrix.GeneralLinearGroup.toLin).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F BinaryLinearThree.Vector)

private theorem modelEquiv_apply (g : BinaryLinearThree.Group) (v : BinaryLinearThree.Vector) :
    modelEquiv g v = g • v := by
  simp only [modelEquiv,MulEquiv.trans_apply,Matrix.PSL3Two.equivGL_apply]
  rfl

private def spaceActor (W : Submodule F V) (g : stabilizer W) : W ≃ₗ[F] W :=
  (toLinear g.val).ofSubmodules W W g.property

private def coordinateActor (W : Submodule F V) (b : BinaryLinearThree.Vector ≃ₗ[F] W) :
    stabilizer W →* (BinaryLinearThree.Vector ≃ₗ[F] BinaryLinearThree.Vector) where
  toFun g := b.trans ((spaceActor W g).trans b.symm)
  map_one' := by ext v : 1; apply b.injective; apply Subtype.ext; simp [spaceActor]
  map_mul' g k := by ext v : 1; apply b.injective; apply Subtype.ext; simp [spaceActor]

private def actor (W : Submodule F V) (b : BinaryLinearThree.Vector ≃ₗ[F] W) :
    stabilizer W →* BinaryLinearThree.Group :=
  modelEquiv.symm.toMonoidHom.comp (coordinateActor W b)

private theorem actor_action (W : Submodule F V) (b : BinaryLinearThree.Vector ≃ₗ[F] W)
    (g : stabilizer W) (v : BinaryLinearThree.Vector) :
    g.val • (b v : V) = (b (actor W b g • v) : V) := by
  have he : modelEquiv (actor W b g) = coordinateActor W b g := modelEquiv.apply_symm_apply _
  rw [←modelEquiv_apply,he]
  change _ = (b (b.symm (spaceActor W g (b v)))).val
  rw [b.apply_symm_apply]
  rfl

private def linearize {U U' : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup U'] [Module F U']
    (e : Multiplicative U ≃* Multiplicative U') : U ≃ₗ[F] U' :=
  let a : U ≃+ U' := {
    toFun v := (e (Multiplicative.ofAdd v)).toAdd
    invFun v := (e.symm (Multiplicative.ofAdd v)).toAdd
    left_inv v := e.symm_apply_apply v
    right_inv v := e.apply_symm_apply v
    map_add' v w := congrArg Multiplicative.toAdd (e.map_mul
      (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  { a with map_smul' := ZMod.map_smul a }

open BinaryLinearThree

/-- A whole natural-plus-dual six-space with its surjective SL₃(2) action
cannot embed in Sp₆(2). The actor and its original quotient are arbitrary. -/
theorem no_symplectic_natural_dual {R : Type*} [_root_.Group R]
    (f : R →* Sp F) (q : R →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (u : Multiplicative NaturalDual.Space →* Sp F) (hu : Function.Injective u)
    (ha : ∀ r v, f r * u (Multiplicative.ofAdd v) * (f r)⁻¹ =
      u (Multiplicative.ofAdd (NaturalDual.action (q r) v))) : False := by
  let E := u.range
  let : IsElementaryAbelian 2 (Multiplicative NaturalDual.Space) :=
    Representation.BinaryGroupAction.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective
    u.rangeRestrict u.rangeRestrict_surjective
  have hc : Nat.card E = 64 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hu).toEquiv]
    change Nat.card NaturalDual.Space = 64
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2)]
    norm_num [NaturalDual.Space,Module.finrank_prod]
  have hn : f.range ≤ normalizer (E : Set (Sp F)) := by
    apply le_set_normalizer_iff.mpr
    rintro _ ⟨r,rfl⟩ _ ⟨v,rfl⟩
    exact ⟨Multiplicative.ofAdd (NaturalDual.action (q r) v.toAdd),(ha r v.toAdd).symm⟩
  have hk : f.rangeRestrict.ker ≤ q.ker := by
    intro r hr
    have hfr : f r = 1 := congrArg Subtype.val hr
    apply NaturalDual.action_injective
    apply LinearMap.ext
    intro v
    have he := ha r v
    rw [hfr,one_mul,inv_one,mul_one] at he
    have hh := congrArg Multiplicative.toAdd (hu he)
    change v = NaturalDual.action (q r) v at hh
    simpa only [map_one,Module.End.one_apply] using hh.symm
  let qB : f.range →* BinaryLinearThree.Group :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨q,hk⟩
  have hqB : Function.Surjective qB := by
    intro g
    obtain ⟨r,rfl⟩ := hq g
    exact ⟨f.rangeRestrict r,by simp [qB]⟩
  have h7 : 7 ∣ Nat.card (normalizer (E : Set (Sp F))) := by
    have hh := (card_dvd_of_surjective qB hqB).trans (card_dvd_of_le hn)
    rw [Matrix.PSL3Two.card_SL] at hh
    exact (by decide : 7 ∣ 168).trans hh
  obtain ⟨W,ho,hd,hE,hNW⟩ := sixtyFour_pointwise E
    (IsElementaryAbelian.isPGroup 2 E) hc h7
  let b : BinaryLinearThree.Vector ≃ₗ[F] W := LinearEquiv.ofFinrankEq _ _ (by
    simp [BinaryLinearThree.Vector,hd])
  let emb := W.subtype.comp b.toLinearMap
  have hi : Function.Injective emb := Subtype.val_injective.comp b.injective
  have hiso (v w : BinaryLinearThree.Vector) : form F (emb v) (emb w) = 0 :=
    (show (b w : V) ∈ (form F).orthogonal W from ho.symm ▸ (b w).property) (b v) (b v).property
  let sh := FanoTransvection.shear emb hiso
  have hsh : sh.range = E := (shear_range W ho hd b).trans hE.symm
  let a : Multiplicative Core ≃* Multiplicative NaturalDual.Space :=
    ((MonoidHom.ofInjective (FanoTransvection.shear_injective emb hiso hi)).trans
      (MulEquiv.subgroupCongr hsh)).trans (MonoidHom.ofInjective hu).symm
  let e := linearize a
  have hea (v : Core) : u (Multiplicative.ofAdd (e v)) = sh (Multiplicative.ofAdd v) := by
    change u ((MonoidHom.ofInjective hu).symm
      (((MonoidHom.ofInjective (FanoTransvection.shear_injective emb hiso hi)).trans
        (MulEquiv.subgroupCongr hsh)) (Multiplicative.ofAdd v))) = _
    exact congrArg Subtype.val ((MonoidHom.ofInjective hu).apply_symm_apply _)
  let fP : R →* stabilizer W := f.codRestrict _ (fun r => hNW (hn ⟨r,rfl⟩))
  let k := (actor W b).comp fP
  have hact (r : R) (v : BinaryLinearThree.Vector) : f r • emb v = emb (k r • v) :=
    actor_action W b (fP r) v
  have he (r : R) (v : Core) : e (U₂ (k r) v) = NaturalDual.action (q r) (e v) := by
    apply Multiplicative.ofAdd.injective
    apply hu
    rw [hea,←ha,hea]
    exact FanoTransvection.shear_equivariant emb hiso (f r) (k r) (hact r) v
  have hkq : k.ker ≤ q.ker := by
    intro r hr
    apply NaturalDual.action_injective
    apply LinearMap.ext
    intro v
    obtain ⟨v,rfl⟩ := e.surjective v
    have hh := he r v
    change k r = 1 at hr
    rw [hr,map_one] at hh
    simpa only [map_one,Module.End.one_apply] using hh.symm
  let qr : k.range →* BinaryLinearThree.Group :=
    k.rangeRestrict.liftOfSurjective k.rangeRestrict_surjective ⟨q,by simpa only [MonoidHom.ker_rangeRestrict] using hkq⟩
  have hqr : Function.Surjective qr := by
    intro g
    obtain ⟨r,rfl⟩ := hq g
    exact ⟨k.rangeRestrict r,by simp [qr]⟩
  have hkt : k.range = ⊤ := eq_top_of_card_eq _
    (Nat.le_antisymm (Nat.card_le_card_of_injective _ k.range.subtype_injective)
      (Nat.card_le_card_of_surjective qr hqr))
  have hks : Function.Surjective k := MonoidHom.range_eq_top.mp hkt
  let α : BinaryLinearThree.Group →* BinaryLinearThree.Group :=
    k.liftOfSurjective hks ⟨q,hkq⟩
  have hα (r : R) : α (k r) = q r := by simp [α]
  have hαs : Function.Surjective α := by
    intro g
    obtain ⟨r,rfl⟩ := hq g
    exact ⟨k r,hα r⟩
  let β : MulAut BinaryLinearThree.Group := MulEquiv.ofBijective α
    ⟨(Finite.injective_iff_surjective).mpr hαs,hαs⟩
  let c := LinearMap.GeneralLinearGroup.toLinearEquiv (NaturalDual.autAction.asGroupHom β.symm)
  let E' : U₂.Equiv NaturalDual.action := {
    toLinearEquiv := e.trans c
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      obtain ⟨r,rfl⟩ := hks g
      change c (e (U₂ (k r) v)) = NaturalDual.action (k r) (c (e v))
      rw [he,←hα]
      have hh := NaturalDual.autAction_covariance β.symm (β (k r)) (e v)
      rw [β.symm_apply_apply] at hh
      exact hh }
  exact NaturalDualCoreObstruction.pointCore_not_equiv_naturalDual ⟨E'⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedSymplectic

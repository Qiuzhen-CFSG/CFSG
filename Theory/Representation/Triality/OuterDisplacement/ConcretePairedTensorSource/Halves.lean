module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights.Graph
public import Theory.Representation.Triality.OuterDisplacement.ConcretePairedTensorSource.Schur

/-!
# Actual half tensors for an even triality field involution

Split the original iterated tensor at its half length. A period of three half
lengths, together with the forward diagram wrap, identifies the second block
with inverse graph pullback of the first. The pinned graph intertwiner and
the actual graph-field fixed equation construct the paired component action.
An explicit action of the supplied inner element absorbs its twist, and Schur
rigidity identifies the original involutory actor with tensor interchange.
Source: GLS3 2.8.3--8; Guralnick--Malle II 3.5 and Lemma 8.6.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
open scoped TensorProduct
namespace Triality.OuterDisplacement.PairedSource
open RestrictedWeights.SteinbergTensors
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Type v} [Group G]

def tensorCongr {U V W Z : Type*}
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [AddCommGroup Z] [Module k Z]
    {ρ : Representation k G U} {σ : Representation k G V}
    {τ : Representation k G W} {υ : Representation k G Z}
    (e : Representation.Equiv ρ σ) (f : Representation.Equiv τ υ) :
    Representation.Equiv (ρ.tprod τ) (σ.tprod υ) := by
  refine .mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv) ?_
  intro g
  apply TensorProduct.ext'
  intro x y
  change e (ρ g x) ⊗ₜ[k] f (τ g y) = σ g (e x) ⊗ₜ[k] υ g (f y)
  exact congrArg₂ (fun u w => u ⊗ₜ[k] w)
    (LinearMap.congr_fun (e.isIntertwining' g) x)
    (LinearMap.congr_fun (f.isIntertwining' g) y)

def prefixCongr (V W : ℕ → FDRep k G)
    (e : ∀ i, Representation.Equiv (V i).ρ (W i).ρ) (n : ℕ) :
    Representation.Equiv (tensorPrefix V n).ρ (tensorPrefix W n).ρ := by
  induction n with
  | zero => exact .refl _
  | succ n ih => exact tensorCongr ih (e n)

def prefixAdd (V : ℕ → FDRep k G) (m n : ℕ) :
    Representation.Equiv (tensorPrefix V (m+n)).ρ
      (Representation.tprod (tensorPrefix V m).ρ (tensorPrefix (fun i => V (m+i)) n).ρ) := by
  induction n with
  | zero => exact (Representation.TensorProduct.rid k _).symm
  | succ n ih =>
    exact (tensorCongr ih (Representation.Equiv.refl (V (m+n)).ρ)).trans
      (Representation.TensorProduct.assoc _ _ _)

def prefixComp (V : ℕ → FDRep k G) (a : G →* G) (n : ℕ) :
    Representation.Equiv (tensorPrefix (fun i => FDRep.of ((V i).ρ.comp a)) n).ρ
      ((tensorPrefix V n).ρ.comp a) := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    refine .mk (TensorProduct.congr ih.toLinearEquiv (LinearEquiv.refl k (V n))) ?_
    intro g
    apply TensorProduct.ext'
    intro x y
    change ih ((tensorPrefix (fun i => FDRep.of ((V i).ρ.comp a)) n).ρ g x) ⊗ₜ[k]
      (V n).ρ (a g) y = (tensorPrefix V n).ρ (a g) (ih x) ⊗ₜ[k] (V n).ρ (a g) y
    exact congrArg (fun z => z ⊗ₜ[k] (V n).ρ (a g) y)
      (LinearMap.congr_fun (ih.isIntertwining' g) x)

private theorem commute_power {H : Type*} [Group H] (φ : Monoid.End H) (γ : H ≃* H)
    (hcomm : ∀ x, φ (γ x)=γ (φ x)) (n : ℕ) (x : H) :
    (φ^n) (γ x)=γ ((φ^n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change φ ((φ^n) (γ x))=γ (φ ((φ^n) x))
    rw [ih,hcomm]

private theorem inverse_commute_power {H : Type*} [Group H]
    (φ : Monoid.End H) (γ : H ≃* H) (hcomm : ∀ x, φ (γ x)=γ (φ x))
    (n : ℕ) (x : H) : (φ^n) (γ.symm x)=γ.symm ((φ^n) x) := by
  apply γ.injective
  rw [←commute_power φ γ hcomm, γ.apply_symm_apply, γ.apply_symm_apply]

theorem half_twist_points {H : Type*} [Group H]
    (φ : Monoid.End H) (γ : H ≃* H) (hcomm : ∀ x, φ (γ x)=γ (φ x))
    (ι : G →* H) (m : ℕ)
    (hfixed : ∀ g, (φ^(2*m)) (γ (ι g))=ι g)
    (δ : G ≃* G) (hδ : ∀ g, ι (δ g)=(φ^(3*m)) (ι g)) (i : ℕ) (g : G) :
    (φ^i) (ι (δ g)) = γ.symm ((φ^(m+i)) (ι g)) := by
  have hf : (φ^(2*m)) (ι g)=γ.symm (ι g) :=
    field_eq_inverse_graph γ (φ^(2*m)) (commute_power φ γ hcomm (2*m)) (hfixed g)
  calc
    _ = (φ^(i+3*m)) (ι g) := by rw [hδ,pow_add]; rfl
    _ = (φ^(m+i)) ((φ^(2*m)) (ι g)) := by
      rw [show i+3*m=(m+i)+2*m by omega,pow_add]; rfl
    _ = _ := by rw [hf,inverse_commute_power φ γ hcomm]

theorem half_weight (w : ℕ → BasicWeight) (m : ℕ)
    (hwrap : ∀ i,w (i+2*m)=diagramAction (w i))
    (hp : Function.Periodic w (3*m)) (i : ℕ) :
    w (m+i)=inverseDiagramAction (w i) := by
  have h := hp i
  rw [show i+3*m=(m+i)+2*m by omega,hwrap] at h
  exact (inverseDiagramAction_diagram (w (m+i))).symm.trans (congrArg inverseDiagramAction h)

variable {K : Variety k} [AlgebraicGroup K]
open AlgebraicTensor

def halfFactorEquiv (S : D4Geometry K) (F : OrdinaryFrobenius S) (D : PinnedTriality S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (hcomm : ∀ x,F.morphism.onPoints (D.iso.toMulEquiv x)=D.iso.toMulEquiv (F.morphism.onPoints x))
    (ι : G →* K.Point) (m : ℕ)
    (hfixed : ∀ g, (pointEnd F.morphism^(2*m)) (D.iso.toMulEquiv (ι g))=ι g)
    (δ : G ≃* G) (hδ : ∀ g, ι (δ g)=(pointEnd F.morphism^(3*m)) (ι g))
    (w : ℕ → BasicWeight) (hwrap : ∀ i,w (i+2*m)=diagramAction (w i))
    (hp : Function.Periodic w (3*m)) (i : ℕ) :
    Representation.Equiv
      (twistedFactor A.factor F.morphism.onPoints ι (w (m+i)) (m+i)).ρ
      ((twistedFactor A.factor F.morphism.onPoints ι (w i) i).ρ.comp δ.toMonoidHom) := by
  have hw := half_weight w m hwrap hp i
  rw [hw]
  let e := leftInverseGraphPullbackEquiv S D A (w i)
  refine .mk e.symm.toLinearEquiv ?_
  intro g
  apply LinearMap.ext
  intro v
  have he := LinearMap.congr_fun (e.symm.isIntertwining' ((pointEnd F.morphism^(m+i)) (ι g))) v
  change e.symm (((A.factor (inverseDiagramAction (w i))).action.action
    ((pointEnd F.morphism^(m+i)) (ι g))).val v) =
    ((A.factor (w i)).action.action
      (D.iso.inv.onPoints ((pointEnd F.morphism^(m+i)) (ι g)))).val (e.symm v) at he
  change e.symm (((A.factor (inverseDiagramAction (w i))).action.action
    ((pointEnd F.morphism^(m+i)) (ι g))).val v) =
    ((A.factor (w i)).action.action
      ((pointEnd F.morphism^i) (ι (δ g)))).val (e.symm v)
  rw [half_twist_points (pointEnd F.morphism) D.iso.toMulEquiv hcomm ι m hfixed δ hδ]
  exact he

def tensorHalvesEquiv (S : D4Geometry K) (F : OrdinaryFrobenius S) (D : PinnedTriality S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (hcomm : ∀ x,F.morphism.onPoints (D.iso.toMulEquiv x)=D.iso.toMulEquiv (F.morphism.onPoints x))
    (ι : G →* K.Point) (m : ℕ)
    (hfixed : ∀ g, (pointEnd F.morphism^(2*m)) (D.iso.toMulEquiv (ι g))=ι g)
    (δ : G ≃* G) (hδ : ∀ g, ι (δ g)=(pointEnd F.morphism^(3*m)) (ι g))
    (w : ℕ → BasicWeight) (hwrap : ∀ i,w (i+2*m)=diagramAction (w i))
    (hp : Function.Periodic w (3*m)) :
    Representation.Equiv (tensor A.factor F.morphism.onPoints ι w (2*m)).ρ
      (Representation.tprod (tensor A.factor F.morphism.onPoints ι w m).ρ
        ((tensor A.factor F.morphism.onPoints ι w m).ρ.comp δ.toMonoidHom)) := by
  let V (i) := twistedFactor A.factor F.morphism.onPoints ι (w i) i
  let e := prefixCongr (fun i=>V (m+i)) (fun i=>FDRep.of ((V i).ρ.comp δ.toMonoidHom))
    (halfFactorEquiv S F D A hcomm ι m hfixed δ hδ w hwrap hp) m
  let f := e.trans (prefixComp V δ.toMonoidHom m)
  have hsplit := prefixAdd V m m
  rw [←two_mul m] at hsplit
  exact hsplit.trans (tensorCongr (.refl _) f)

def innerTwistEquiv {U : Type*} [AddCommGroup U] [Module k U]
    (π : Representation k G U) (δ a : G ≃* G) (g : G)
    (hform : ∀ x,a x=g*δ x*g⁻¹) :
    Representation.Equiv (π.comp δ.toMonoidHom) (π.comp a.toMonoidHom) := by
  refine .mk (LinearMap.GeneralLinearGroup.toLinearEquiv (π.asGroupHom g)) ?_
  intro x
  apply LinearMap.ext
  intro v
  change π g (π (δ x) v)=π (a x) (π g v)
  simp only [←Module.End.mul_apply,←map_mul]
  exact congrArg (fun z=>π z v) (by rw [hform]; group)

def innerTwistedPairEquiv {U W : Type*}
    [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    (ρ : Representation k G W) (π : Representation k G U) (δ a : G ≃* G)
    (g : G) (hform : ∀ x,a x=g*δ x*g⁻¹)
    (e : Representation.Equiv ρ (Representation.tprod π (π.comp δ.toMonoidHom))) :
    Representation.Equiv ρ (Representation.tprod π (π.comp a.toMonoidHom)) :=
  e.trans (tensorCongr (.refl π) (innerTwistEquiv π δ a g hform))

variable [CharP k 2]

theorem paired_rank_ratio {U W : Type*}
    [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G W) [Representation.IsIrreducible ρ]
    (π : Representation k G U) (a : G ≃* G) (ha : Function.Involutive a)
    (e : Representation.Equiv ρ (Representation.tprod π (π.comp a.toMonoidHom)))
    (T : Module.End k W) (hT2 : T*T=1)
    (hTi : ∀ g v,T (ρ g v)=ρ (a g) (T v)) (hd : 8≤Module.finrank k U) :
    7*Module.finrank k W ≤ 16*Module.finrank k (LinearMap.range (T-LinearMap.id)) := by
  let c := ConcretePairedTensorSource.pairedCoordinates e.toLinearEquiv
  have hc : ∀ v i j,c (T v) i j=c v j i :=
    ConcretePairedTensorSource.pairedCoordinates_action ρ a ha π e.toLinearEquiv
      (fun g v=>LinearMap.congr_fun (e.isIntertwining' g) v) T hT2 hTi
  have ht : ∀ v i j,c.conj T v i j=(1 : Module.End k (Fin 1→k)) (v j i) := by
    intro v i j
    simpa only [LinearEquiv.conj_apply_apply,c.apply_symm_apply,Module.End.one_apply] using hc (c.symm v) i j
  have hb := transpose_displacement_ratio (Module.finrank k U) hd (c.conj T) 1 ht
  have hr := Representation.BinaryOffender.NaturalTensor.operatorFixedCodim_eq_of_equiv
    T (c.conj T) c (by intro v; simp)
  change Module.finrank k (LinearMap.range (T-LinearMap.id)) =
    Module.finrank k (LinearMap.range (c.conj T-LinearMap.id)) at hr
  rw [←c.finrank_eq,←hr] at hb
  exact hb

end
end Triality.OuterDisplacement.PairedSource

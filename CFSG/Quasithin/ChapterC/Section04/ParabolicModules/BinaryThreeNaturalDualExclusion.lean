module
public import Theory.Representation.BinaryNaturalDual.NaturalIsotypicExclusion
public import Theory.Representation.PSL3Two.NaturalDualCentralizer
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledCoordinates

/-!
# Repeated-natural exclusion on the binary-three orbit

A six-dimensional natural-plus-dual action cannot be a direct sum of
identically marked natural modules. The proposed natural marking need not use
the supplied quotient coordinates: its kernel contains the natural-dual kernel
by equivariance, and the descended surjection between finite isomorphic actors
is an isomorphism. Transport along the explicit `ModelBridge` then applies the
checked invariant-bilinear-form obstruction. Degree four is excluded by dimension.

The subgroup application retains conjugation on `Additive U` and the literal
map L → LR/R. The descendant `SourceOrbit` applies it to the original chosen
orbit, including restriction to the actual C.2.8 actor. The bridge remains an
explicit premise; neither the C.4.8 classification nor its orthogonal row is
proved here.

Source: Aschbacher--Smith C.4.8(2), printed pp.153--154, and the binary
natural-plus-dual application of 4.4.3(i.a), printed p.619, refs/quasithin.pdf.
-/

public noncomputable section
open Representation Subgroup
open scoped IsMulCommutative
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterC.Section04.BinaryThreeNaturalDualExclusion

/-- The conditional model comparison: both the actor and the whole pair are
identified by equivalences satisfying the literal action equation. Constructing
this bridge is independent of the repeated-natural exclusion. -/
structure ModelBridge where
  actor : BinaryLinearThree.Group ≃* LinearGroup 3
  coordinates : BinaryLinearThree.NaturalDual.Space ≃ₗ[ZMod 2]
    BinaryNaturalDual.CoordinateSpace 3
  intertwines : ∀ g v, coordinates (BinaryLinearThree.NaturalDual.action g v) =
    BinaryNaturalDual.naturalDualRepresentation (actor g) (coordinates v)

/-- Independently marked surjective natural coordinates are impossible on the
same natural-plus-dual action. Kernel containment is proved from equivariance;
no agreement of the two actor markings is assumed. -/
theorem no_repeated_natural_marking
    {L U : Type*} [Group L] [AddCommGroup U] [Module (ZMod 2) U]
    (b : ModelBridge) (ρ : Representation (ZMod 2) L U)
    (q : L →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space)
    (hE : ∀ l v, E (ρ l v) = BinaryLinearThree.NaturalDual.action (q l) (E v))
    (p : L →* LinearGroup 3) (hp : Function.Surjective p)
    (m : ℕ) (hm : 0 < m)
    (N : U ≃ₗ[ZMod 2] (Fin m → BinaryLinear.OuterCyclic.Space 3))
    (hN : ∀ l v, N (ρ l v) = fun i => p l (N v i)) : False := by
  classical
  have hker : q.ker ≤ p.ker := by
    intro l hl
    have hfix (v : U) : ρ l v = v := by
      apply E.injective
      rw [hE, show q l = 1 from hl, map_one, Module.End.one_apply]
    change p l = 1
    apply LinearEquiv.ext
    intro x
    let i : Fin m := ⟨0,hm⟩
    have hh := congrFun (hN l (N.symm (Pi.single i x))) i
    rw [hfix,N.apply_symm_apply] at hh
    change p l x = x
    simpa only [Pi.single_eq_same] using hh.symm
  let f : BinaryLinearThree.Group →* LinearGroup 3 :=
    q.liftOfSurjective hq ⟨p,hker⟩
  have hf (l : L) : f (q l) = p l := by simp [f]
  have hfs : Function.Surjective f := by
    intro g
    obtain ⟨l,rfl⟩ := hp g
    exact ⟨q l,hf l⟩
  let a₀ := f.comp b.actor.symm.toMonoidHom
  have ha : Function.Surjective a₀ := hfs.comp b.actor.symm.surjective
  let : Finite (LinearGroup 3) := Finite.of_injective
    (fun g : LinearGroup 3 => (g : BinaryLinear.OuterCyclic.Space 3 →
      BinaryLinear.OuterCyclic.Space 3)) DFunLike.coe_injective
  let a : MulAut (LinearGroup 3) := MulEquiv.ofBijective a₀
    ⟨(Finite.injective_iff_surjective).mpr ha,ha⟩
  let C := E.trans b.coordinates
  have hC (l : L) (v : U) : C (ρ l v) =
      BinaryNaturalDual.naturalDualRepresentation (b.actor (q l)) (C v) := by
    exact (congrArg b.coordinates (hE l v)).trans (b.intertwines (q l) (E v))
  apply BinaryNaturalDual.no_natural_copies_equiv (by decide : 3 ≤ 3) a (C.symm.trans N)
  intro g v
  obtain ⟨l,rfl⟩ := b.actor.surjective.comp hq g
  have hv := hC l (C.symm v)
  rw [C.apply_symm_apply] at hv
  change N (C.symm (BinaryNaturalDual.naturalDualRepresentation (b.actor (q l)) v)) = _
  rw [← hv,C.symm_apply_apply,hN]
  have ha' : a (b.actor (q l)) = p l := by
    change f (b.actor.symm (b.actor (q l))) = p l
    rw [b.actor.symm_apply_apply,hf]
  change (fun i => p l (N (C.symm v) i)) = fun i => a (b.actor (q l)) (N (C.symm v) i)
  rw [ha']

/-- Exclude both repeated-natural degrees in C.4.8(2). In degree four the
six-dimensional space gives an immediate dimension obstruction. The orthogonal
alternative is a separate row and is not asserted to be excluded here. -/
theorem no_c48_repeated_natural_marking
    {L U : Type*} [Group L] [AddCommGroup U] [Module (ZMod 2) U]
    (b : ModelBridge) (ρ : Representation (ZMod 2) L U)
    (q : L →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space)
    (hE : ∀ l v, E (ρ l v) = BinaryLinearThree.NaturalDual.action (q l) (E v))
    (d : ℕ) (hd : d = 3 ∨ d = 4)
    (p : L →* LinearGroup d) (hp : Function.Surjective p)
    (m : ℕ) (hm : 0 < m)
    (N : U ≃ₗ[ZMod 2] (Fin m → BinaryLinear.OuterCyclic.Space d))
    (hN : ∀ l v, N (ρ l v) = fun i => p l (N v i)) : False := by
  rcases hd with rfl | rfl
  · exact no_repeated_natural_marking b ρ q hq E hE p hp m hm N hN
  · have hdim : Module.finrank (ZMod 2) U = 6 := by
      rw [E.finrank_eq]
      simp [BinaryLinearThree.NaturalDual.Space, Module.finrank_prod,
        Subspace.dual_finrank_eq, BinaryLinearThree.Vector]
    have hcopies : Module.finrank (ZMod 2) U = m * 4 := by
      rw [N.finrank_eq]
      simp [BinaryLinear.OuterCyclic.Space, Module.finrank_pi_fintype]
    omega

section Quotient
open Chapter7.NormalizedSource
variable {G : Type*} [Group G] (L R U : Subgroup G)

/-- The literal map from L to LR/R, with normality only inside LR. -/
@[expose] def radicalQuotientMap [(R.subgroupOf (L ⊔ R)).Normal] :
    L →* (L ⊔ R : Subgroup G) ⧸ R.subgroupOf (L ⊔ R) :=
  (QuotientGroup.mk' (R.subgroupOf (L ⊔ R))).comp (inclusion le_sup_left)

/-- L covers the actual quotient LR/R. -/
theorem radicalQuotientMap_surjective [(R.subgroupOf (L ⊔ R)).Normal] :
    Function.Surjective (radicalQuotientMap L R) := by
  intro x
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf (L ⊔ R)) x
  have hy : y ∈ L.subgroupOf (L ⊔ R) ⊔ R.subgroupOf (L ⊔ R) := by
    rw [← subgroupOf_sup (show L ≤ L ⊔ R from le_sup_left)
      (show R ≤ L ⊔ R from le_sup_right),subgroupOf_self]
    trivial
  obtain ⟨l,hl,r,hr,he⟩ := mem_sup_of_normal_right.mp hy
  refine ⟨⟨l,hl⟩,?_⟩
  change QuotientGroup.mk' (R.subgroupOf (L ⊔ R)) l = _
  have hr' : QuotientGroup.mk' (R.subgroupOf (L ⊔ R)) r = 1 :=
    (QuotientGroup.eq_one_iff r).mpr hr
  rw [←he,map_mul,hr',mul_one]

/-- C.4.8(2)'s repeated-natural marking on the actual subgroup U and the
literal LR/R quotient contradicts its supplied binary natural-dual coordinates. -/
theorem no_radical_quotient_natural_marking [IsElementaryAbelian 2 U]
    [(R.subgroupOf (L ⊔ R)).Normal]
    (b : ModelBridge) (hLU : L ≤ normalizer (U : Set G))
    (q : L →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (E : Additive U ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space)
    (hE : ∀ l v, E (doubledSeedAction L U hLU l v) =
      BinaryLinearThree.NaturalDual.action (q l) (E v))
    (d : ℕ) (hd : d = 3 ∨ d = 4)
    (a : ((L ⊔ R : Subgroup G) ⧸ R.subgroupOf (L ⊔ R)) ≃* LinearGroup d)
    (m : ℕ) (hm : 0 < m)
    (N : Additive U ≃ₗ[ZMod 2] (Fin m → BinaryLinear.OuterCyclic.Space d))
    (hN : ∀ l v, N (doubledSeedAction L U hLU l v) =
      fun i => a (radicalQuotientMap L R l) (N v i)) : False :=
  no_c48_repeated_natural_marking b (doubledSeedAction L U hLU) q hq E hE d hd
    (a.toMonoidHom.comp (radicalQuotientMap L R))
    (a.surjective.comp (radicalQuotientMap_surjective L R)) m hm N hN

end Quotient
end CFSG.Quasithin.ChapterC.Section04.BinaryThreeNaturalDualExclusion

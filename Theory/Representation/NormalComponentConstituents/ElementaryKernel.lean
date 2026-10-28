module
public import Theory.Representation.ConjugateRep
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Elementary Sylow subgroups from an exchanged constituent kernel

Let H be normal and let two exchanged constituent actions jointly separate H.
If a Sylow element a fixes the first constituent, its commutator with the
exchanging actor has square one. Applying the first action to that identity
shows that a squared also fixes the second constituent. Separation forces
its square to be one. Thus the Sylow intersection with the first kernel is
elementary abelian, without assuming that the pair spans the whole module.

A noncentral normal subgroup of the normal component orbit contains an actual
conjugate of its generating component: otherwise the component-normal-subgroup
dichotomy makes every conjugate centralize it. Restricting the original Sylow
to that component and transporting back proves the original component's
Sylow two-subgroups elementary. No direct-product decomposition or intrinsic
Frattini monotonicity is used.

Source application: Aschbacher--Smith G.10.15, printed p.362.
-/

@[expose] public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace Representation.BinaryOffender.ExchangedKernel

private theorem conjugate_fixed_of_conj_fixed
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) [H.Normal]
    (R : Subrepresentation (ρ.comp H.subtype)) (x : G) (a : H)
    (ha : R.toRepresentation ((MulAut.conjNormal x⁻¹ : MulAut H) a) = 1) :
    (conjugateSubrepresentationOrderIso ρ H x R).toRepresentation a = 1 := by
  let e := conjugateSubrepresentationEquiv ρ H R x⁻¹
  rw [conjugateSubrepresentationOrderIso_apply]
  apply LinearMap.ext
  intro u
  apply (EquivLike.injective e)
  have hi := e.isIntertwining a u
  change e ((conjugateSubrepresentation ρ H R x⁻¹).toRepresentation a u) =
    (conjugateRep R.toRepresentation x⁻¹) a (e u) at hi
  have hh : (conjugateRep R.toRepresentation x⁻¹) a = 1 := ha
  simpa only [hh, Module.End.one_apply] using hi

private theorem square_of_pair_separates
    {E Q : Type*} [Group E] [Group Q] (f : E →* Q) (α : MulAut E)
    (hsep : ∀ a : E, f a = 1 → f (α a) = 1 → a = 1)
    (a : E) (ha : f a = 1) (hc : (α a * a⁻¹)^2 = 1) : a^2 = 1 := by
  apply hsep
  · simp only [map_pow,ha,one_pow]
  · have hh := congrArg f hc
    simpa only [map_pow,map_mul,map_inv,ha,inv_one,mul_one,map_one] using hh

/-- An exponent-two actor makes the source Sylow intersection with one of two
separating constituent kernels elementary abelian. -/
theorem kernel_sylow_elementary
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (H X S : Subgroup G) [H.Normal]
    [IsElementaryAbelian 2 X] (hn : S ≤ normalizer (X:Set G))
    (R : Subrepresentation (ρ.comp H.subtype)) (x : X)
    (hsep : ∀ a : H, R.toRepresentation a = 1 →
      (conjugateSubrepresentationOrderIso ρ H (x:G) R).toRepresentation a = 1 → a=1) :
    IsElementaryAbelian 2 (((S.subgroupOf H) ⊓ R.toRepresentation.asGroupHom.ker) : Subgroup H) := by
  let P := (S.subgroupOf H) ⊓ R.toRepresentation.asGroupHom.ker
  have hpow (a:P) : a^2=1 := by
    apply Subtype.ext
    apply square_of_pair_separates R.toRepresentation.asGroupHom
      (MulAut.conjNormal (x:G)⁻¹)
    · intro b hb hbx
      apply hsep b
      · exact congrArg Units.val hb
      · apply conjugate_fixed_of_conj_fixed
        exact congrArg Units.val hbx
    · exact MonoidHom.mem_ker.mp a.property.2
    · apply Subtype.ext
      change ((x:G)⁻¹ * (a:H) * ((x:G)⁻¹)⁻¹ * ((a:H):G)⁻¹)^2=1
      have hc : ⁅(x:G)⁻¹,((a:H):G)⁆ ∈ X := by
        apply le_normalizer_iff_commutator_le_left.mp hn
        exact commutator_mem_commutator (X.inv_mem x.property) a.property.1
      exact elemPow_eq_one_of_isElementaryAbelian (p:=2) _ hc
  exact {
    toIsMulCommutative := ⟨⟨fun a b =>
      (Commute.of_orderOf_dvd_two (fun c => orderOf_dvd_of_pow_eq_one (hpow c)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }

/-- A noncentral normal subgroup of a component orbit contains an actual
ambient conjugate of the original component. -/
theorem exists_kernel_component
    {G : Type*} [Group G] {L : Subgroup G} (hL : IsComponent G L)
    (N : Subgroup (componentOrbit L ⊤)) [N.Normal]
    (hn : ¬ N ≤ center (componentOrbit L ⊤)) :
    ∃ t : G, (L.map (MulAut.conj t).toMonoidHom).subgroupOf (componentOrbit L ⊤) ≤ N := by
  classical
  by_contra! hnone
  let H := componentOrbit L ⊤
  have hcomm (t : G) : ⁅(L.map (MulAut.conj t).toMonoidHom).subgroupOf H,N⁆ = ⊥ := by
    apply Or.resolve_left (((hL.map_conj t).subgroupOf ?_).normal_dichotomy N) (hnone t)
    exact le_iSup (fun t : (⊤ : Subgroup G) => L.map (MulAut.conj (t:G)).toMonoidHom) ⟨t,mem_top t⟩
  have hcent : H ≤ centralizer (N.map H.subtype : Set G) := by
    apply iSup_le
    intro t
    have hle : L.map (MulAut.conj (t:G)).toMonoidHom ≤ H := le_iSup (fun t : (⊤ : Subgroup G) => L.map (MulAut.conj (t:G)).toMonoidHom) t
    intro a ha n hn
    obtain ⟨n,hn,rfl⟩ := hn
    exact congrArg H.subtype ((commutator_eq_bot_iff_le_centralizer.mp (hcomm t))
      (show (⟨a,hle ha⟩ : H) ∈ (L.map (MulAut.conj (t:G)).toMonoidHom).subgroupOf H from ha) n hn)
  apply hn
  intro n hn
  rw [mem_center_iff]
  intro a
  apply Subtype.ext
  exact (hcent a.property n (mem_map_of_mem H.subtype hn)).symm

/-- If the actual Sylow intersection with a noncentral orbit kernel is
elementary abelian, every Sylow two-subgroup of the original component is
elementary abelian. The argument transports the actual Sylow intersection. -/
theorem component_sylow_elementary_of_kernel
    {G : Type*} [Group G] [Finite G] {L : Subgroup G} (hL : IsComponent G L)
    (S : Sylow 2 G) (N : Subgroup (componentOrbit L ⊤)) [N.Normal]
    (hn : ¬ N ≤ center (componentOrbit L ⊤))
    [IsElementaryAbelian 2 ((((S:Subgroup G).subgroupOf (componentOrbit L ⊤)) ⊓ N) :
      Subgroup (componentOrbit L ⊤))] (P : Sylow 2 L) : IsElementaryAbelian 2 P := by
  classical
  let H := componentOrbit L ⊤
  obtain ⟨t,ht⟩ := exists_kernel_component hL N hn
  let K := L.map (MulAut.conj t).toMonoidHom
  have hK : K ≤ H := le_iSup
    (fun t : (⊤:Subgroup G) => L.map (MulAut.conj (t:G)).toMonoidHom) ⟨t,mem_top t⟩
  obtain ⟨Q,hQ⟩ := S.exists_subgroupOf_eq_of_subnormal K (hL.map_conj t).1
  let f : Q →* (((S:Subgroup G).subgroupOf H) ⊓ N : Subgroup H) :=
    { toFun := fun a => ⟨⟨a,hK a.val.property⟩,by
        constructor
        · exact hQ.le a.property
        · exact ht a.val.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c => ((c.val:H):G)) hab
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.of_injective f hf
  let e : L ≃* K := (MulAut.conj t).subgroupMap L
  let P' := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let ep : P ≃* P' := e.subgroupMap (P:Subgroup L)
  let eq : P ≃* Q := ep.trans (P'.equiv Q)
  exact IsElementaryAbelian.of_injective eq.toMonoidHom eq.injective

end Representation.BinaryOffender.ExchangedKernel

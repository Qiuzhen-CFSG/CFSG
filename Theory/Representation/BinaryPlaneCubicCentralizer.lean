module
public import Theory.GroupTheory.Perm.PrimeDegreeNormalizer
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.CyclicFixedRank
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Theory.GroupTheory.ThreePointActionKernel
public import Theory.Representation.BinaryOffender.CentralSectionAction

/-!
# Binary planes centralized by a cubic action

A nontrivial cubic linear action on a binary plane permutes its three
nonzero vectors regularly. Its linear centralizer consequently has exponent
three. A faithful group preserving a spanning family of such planes and
centralizing a fixed-point-free cubic subgroup is therefore a three-group.

The final theorem applies this to the kernel of the conjugation action on
three subgroups. The three-core lies in that kernel, so the three-point
permutation theorem supplies a normal member. This is the linear and
permutation argument used in Aschbacher–Smith D.2.28–29, pp.191–192.
-/

public noncomputable section
open Subgroup
namespace Representation
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

private def nonzeroPerm : (W ≃ₗ[ZMod 2] W) →* Equiv.Perm {w : W // w ≠ 0} where
  toFun a := a.toEquiv.subtypeEquiv (fun w => by simp)
  map_one' := by ext w; rfl
  map_mul' := by intro a b; ext w; rfl

omit [FiniteDimensional (ZMod 2) W] in
private theorem nonzeroPerm_injective : Function.Injective (nonzeroPerm (W := W)) := by
  intro a b he
  ext w
  by_cases hw : w = 0
  · simp [hw]
  · exact congrArg Subtype.val (DFunLike.congr_fun he ⟨w,hw⟩)

/-- The centralizer of a nontrivial cubic action on a binary plane has exponent three. -/
theorem binary_plane_commuting_cubic_pow
    (hd : Module.finrank (ZMod 2) W = 2)
    (a r : W ≃ₗ[ZMod 2] W) (hr : r^3=1) (hrne : r≠1)
    (hc : Commute a r) : a^3=1 := by
  classical
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Fintype W := Fintype.ofFinite W
  let X := {w : W // w ≠ 0}
  have hW : Nat.card W = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    norm_num
  have hX : Nat.card X = 3 := by
    have hh := Fintype.card_subtype_compl (fun w : W => w=0)
    simp only [Fintype.card_unique] at hh
    simpa only [Nat.card_eq_fintype_card,X,←Nat.card_eq_fintype_card,hW] using hh
  let e : X ≃ Fin 3 := (Finite.equivFin X).trans (Equiv.cast (congrArg Fin hX))
  let f : (W ≃ₗ[ZMod 2] W) →* Equiv.Perm (Fin 3) :=
    (Equiv.permCongrHom e).toMonoidHom.comp nonzeroPerm
  have hf : Function.Injective f := (Equiv.permCongrHom e).injective.comp nonzeroPerm_injective
  have hrc : orderOf r = 3 := orderOf_eq_prime hr hrne
  have ha : a ∈ zpowers r := by
    rw [←Theory.GroupTheory.centralizer_eq_zpowers_of_prime_degree Nat.prime_three f hf r hrc]
    exact mem_centralizer_singleton_iff.mpr hc.eq
  have hdiv : orderOf a ∣ 3 := by
    simpa only [Nat.card_zpowers,hrc] using (zpowers r).orderOf_dvd_natCard ha
  exact orderOf_dvd_iff_pow_eq_one.mp hdiv

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ι : Type*}

/-- Compatible binary plane actions detect the three-power exponent of a faithful action. -/
theorem isPGroup_three_of_binary_planes
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (U : ι → Submodule (ZMod 2) V) (hspan : ⨆ i, U i = ⊤)
    (σ : ∀ i, Representation (ZMod 2) G (U i))
    (hσ : ∀ i g v, (σ i g v : V) = ρ g (v : V))
    (hd : ∀ i, Module.finrank (ZMod 2) (U i) = 2)
    (r : ∀ i, (U i) ≃ₗ[ZMod 2] (U i)) (hr : ∀ i, (r i)^3=1)
    (hrne : ∀ i, r i≠1)
    (hc : ∀ i g, Commute (LinearMap.GeneralLinearGroup.toLinearEquiv ((σ i).asGroupHom g)) (r i)) :
    IsPGroup 3 G := by
  intro g
  refine ⟨1,?_⟩
  suffices g^3=1 by simpa using this
  apply hf
  rw [map_one]
  apply LinearMap.ext
  intro v
  have hv : v ∈ (⨆ i, U i) := hspan ▸ Submodule.mem_top
  have hfix : (⨆ i, U i) ≤ LinearMap.ker (ρ (g^3) - LinearMap.id) := by
    apply iSup_le
    intro i u hu
    change ρ (g^3) u - u = 0
    apply sub_eq_zero.mpr
    have he := binary_plane_commuting_cubic_pow (hd i)
      (LinearMap.GeneralLinearGroup.toLinearEquiv ((σ i).asGroupHom g)) (r i)
      (hr i) (hrne i) (hc i g)
    have hp : σ i (g^3) ⟨u,hu⟩ = ⟨u,hu⟩ := by
      change (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (U i)
        ((σ i).asGroupHom (g^3))) ⟨u,hu⟩ = ⟨u,hu⟩
      rw [map_pow,map_pow]
      change ((LinearMap.GeneralLinearGroup.toLinearEquiv ((σ i).asGroupHom g))^3) ⟨u,hu⟩ = _
      rw [he]
      rfl
    rw [←hσ i (g^3) ⟨u,hu⟩,hp]
  exact sub_eq_zero.mp (hfix hv)

/-- A common central cubic forces a group stabilizing spanning binary planes to be a three-group. -/
theorem isPGroup_three_of_plane_stabilizers_central_cubic
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (U : ι → Submodule (ZMod 2) V) (hspan : ⨆ i, U i = ⊤)
    (hd : ∀ i, Module.finrank (ZMod 2) (U i) = 2)
    (K Z : Subgroup G) (hstable : ∀ i, K ≤ BinaryOffender.subspaceStabilizer ρ (U i))
    (hZK : Z ≤ K) (hZ : Nat.card Z = 3) (hcentral : Z ≤ center G)
    (hfixed : BinaryOffender.fixedSpace ρ Z = ⊥) : IsPGroup 3 K := by
  let : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; decide)
  let : IsCyclic Z := isCyclic_of_prime_card hZ
  obtain ⟨z,hz⟩ := IsCyclic.exists_generator (α := Z)
  have hzgen : zpowers (z : G) = Z := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr z.property)
    rw [Nat.card_zpowers,Subgroup.orderOf_coe,orderOf_eq_card_of_forall_mem_zpowers hz]
  have hz3 : (z:G)^3=1 := by
    have hh : z^3=1 := by rw [←hZ]; exact pow_card_eq_one'
    exact congrArg Subtype.val hh
  let zK : K := ⟨z,hZK z.property⟩
  let σ (i : ι) : Representation (ZMod 2) K (U i) :=
    (BinaryOffender.stabilizerRepresentation ρ (U i)).comp (inclusion (hstable i))
  let r (i : ι) := LinearMap.GeneralLinearGroup.toLinearEquiv ((σ i).asGroupHom zK)
  apply isPGroup_three_of_binary_planes (ρ.comp K.subtype) (hf.comp K.subtype_injective)
    U hspan σ (fun _ _ _ => rfl) hd r
  · intro i
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (U i)
      ((σ i).asGroupHom zK))^3 = 1
    rw [←map_pow,←map_pow,show zK^3=1 from Subtype.ext hz3,map_one,map_one]
  · intro i he
    have hbot : U i = ⊥ := by
      apply le_bot_iff.mp
      rw [←hfixed]
      intro v hv
      rw [←hzgen,BinaryOffender.mem_fixedSpace_zpowers_iff]
      have hh := congrArg (fun a : (U i) ≃ₗ[ZMod 2] (U i) => (a ⟨v,hv⟩ : V)) he
      exact hh
    have hh := hd i
    rw [hbot,finrank_bot] at hh
    omega
  · intro i k
    have hc : Commute k zK := by
      apply Subtype.ext
      exact (mem_center_iff.mp (hcentral z.property)) k
    exact (hc.map (σ i).asGroupHom).map
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (U i)).toMonoidHom

open scoped Pointwise

/-- A conjugacy-invariant family of three subgroups with binary fixed planes
contains a normal member when a central cubic acts fixed freely. -/
theorem exists_normal_of_three_fixed_planes [Finite G]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (S : Set (Subgroup G))
    (hstable : ∀ D ∈ S, ∀ g : G, D.map (MulAut.conj g).toMonoidHom ∈ S)
    (hcard : Nat.card S = 3)
    (hspan : ⨆ D : S, BinaryOffender.fixedSpace ρ D.val = ⊤)
    (hd : ∀ D ∈ S, Module.finrank (ZMod 2) (BinaryOffender.fixedSpace ρ D) = 2)
    (hcore : ∀ D ∈ S, pCore 3 G ≤ normalizer (D : Set G))
    (Z : Subgroup G) (hZR : Z ≤ pCore 3 G) (hZ : Nat.card Z = 3)
    (hcentral : Z ≤ center G) (hfixed : BinaryOffender.fixedSpace ρ Z = ⊥) :
    ∃ D ∈ S, D.Normal := by
  let : MulAction G (Subgroup G) :=
    MulAction.compHom (Subgroup G) ConjAct.toConjAct.toMonoidHom
  let A : SubMulAction G (Subgroup G) := {
    carrier := S
    smul_mem' := fun g D hD => hstable D hD g }
  let f := MulAction.toPermHom G A
  have hKN (D : A) : f.ker ≤ normalizer (D.val : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact congrArg Subtype.val (congrArg (fun p : Equiv.Perm A => p D) hg)
  have hRK : pCore 3 G ≤ f.ker := by
    intro g hg
    change f g = 1
    apply _root_.Equiv.ext
    intro D
    apply Subtype.ext
    exact mem_normalizer_iff_map_conj_eq.mp (hcore D.val D.property hg)
  have hK : IsPGroup 3 f.ker := isPGroup_three_of_plane_stabilizers_central_cubic
    ρ hf (fun D : A => BinaryOffender.fixedSpace ρ D.val) hspan
    (fun D => hd D.val D.property) f.ker Z
    (fun D => BinaryOffender.fixedSpace_stable_of_normalizes ρ (hKN D))
    (hZR.trans hRK) hZ hcentral hfixed
  obtain ⟨D,hD⟩ := f.exists_fixed_of_threeGroup_kernel hcard hK hRK
  refine ⟨D.val,D.property,normal_iff_map_conj_eq.mpr ?_⟩
  intro g
  exact congrArg Subtype.val (hD g)

end Representation

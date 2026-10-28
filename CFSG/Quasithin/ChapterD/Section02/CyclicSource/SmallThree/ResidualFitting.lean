module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.ResidualKernel
public import CFSG.Quasithin.ChapterG.Section08.ThetaFaithfulness
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Residual Fitting control through canonical factor normalizers

The intersection of the normalizers of all canonical cubic factors is normal.
Its elements square into the centralizer of their join, since an automorphism
of a cyclic group of order three has square one. If a residual image has
trivial two-core, its odd Fitting subgroup inside this normalizer image lies
in the centralizer image. The central-kernel lifting theorem therefore places
it in the image of the original Fitting subgroup.

Solvable Fitting self-centralization then excludes a nontrivial residual
involution centralizing that original Fitting image. This is the group step
in the seed-based residual inverter for Aschbacher--Smith D.2.25, printed p.190.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
variable {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
  [MulDistribMulAction G V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]

@[expose] def factorNormalizer : Subgroup G :=
  ⨅ X : smallSupportFactors G V 1, normalizer (X.val : Set G)

omit [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V] in
theorem mem_factorNormalizer_iff (x : G) : x ∈ factorNormalizer (G:=G) (V:=V) ↔
    ∀ X ∈ smallSupportFactors G V 1, x ∈ normalizer (X : Set G) := by
  simp only [factorNormalizer,mem_iInf,Subtype.forall]

omit [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V] in
instance factorNormalizer_normal : (factorNormalizer (G:=G) (V:=V)).Normal := by
  constructor
  intro n hn g
  rw [mem_factorNormalizer_iff] at hn ⊢
  intro X hX
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hh := congrArg (fun H : Subgroup G => H.conjBy g)
    (mem_normalizer_iff_map_conj_eq.mp (hn (X.conjBy g⁻¹) (smallSupportFactors_conjBy hX g⁻¹)))
  change ((X.conjBy g⁻¹).conjBy n).conjBy g = (X.conjBy g⁻¹).conjBy g at hh
  change X.conjBy (g*n*g⁻¹)=X
  simpa only [conjBy_conjBy,mul_assoc,mul_inv_cancel,conjBy_one] using hh

omit [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V] in
theorem factorNormalizer_square_centralizes {x : G}
    (hx : x ∈ factorNormalizer (G:=G) (V:=V)) :
    x^2 ∈ centralizer (smallSupportGroup G V 1 : Set G) := by
  have hlocal : ∀ X ∈ smallSupportFactors G V 1, x^2 ∈ centralizer (X : Set G) := by
    intro X hX
    let : IsCyclic X := smallSupportFactor_isCyclic (Or.inl rfl) hX
    have hcard : Nat.card (MulAut X)=2 := by
      rw [IsCyclic.card_mulAut, hX.2.1]
      decide
    let n : normalizer (X:Set G) := ⟨x,(mem_factorNormalizer_iff x).mp hx X hX⟩
    have he : X.normalizerMonoidHom (n^2)=1 := by
      rw [map_pow,←hcard]
      exact pow_card_eq_one'
    have hn : n^2 ∈ X.normalizerMonoidHom.ker := he
    rw [normalizerMonoidHom_ker] at hn
    exact hn
  have hY : smallSupportGroup G V 1 ≤ centralizer ({x^2}:Set G) := by
    apply sSup_le
    intro X hX z hz
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hlocal X hX) z hz)
  apply mem_centralizer_iff.mpr
  intro z hz
  exact mem_centralizer_singleton_iff.mp (hY hz)

theorem residual_factorNormalizer_fitting_lift
    (hsplit : FixedPoints.subgroup (smallSupportGroup G V 1) V ⊔
      commutatorAction (smallSupportGroup G V 1) V = ⊤)
    {D : Type*} [Group D] [Finite D] (f : G →* D) (hf : Function.Surjective f)
    (hker : ∀ x, f x = 1 → ∀ v ∈ FixedPoints.subgroup (smallSupportGroup G V 1) V,
      x • v = v) (hcore : pCore 2 D=⊥) :
    fittingSubgroupOf ((factorNormalizer (G:=G) (V:=V)).map f) ≤
      (fittingSubgroup G).map f := by
  let B := (factorNormalizer (G:=G) (V:=V)).map f
  have hB : B.Normal := Normal.map inferInstance f hf
  let L := fittingSubgroupOf B
  let : L.Normal := fittingSubgroupOf_normal B hB
  let : Group.IsNilpotent L := fittingSubgroupOf_isNilpotent B
  have hLF : L ≤ fittingSubgroup D := le_sSup ⟨inferInstance,inferInstance⟩
  have hodd : Odd (Nat.card L) :=
    (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot hcore).of_dvd_nat
      (Subgroup.card_dvd_of_le hLF)
  apply residual_centralizer_nilpotent_lift hsplit f hker L
  intro z hz
  have hzB : z ∈ B := by obtain ⟨a,_,rfl⟩ := hz; exact a.property
  obtain ⟨x,hx,hxz⟩ := hzB
  have hz2 : z^2 ∈ (centralizer (smallSupportGroup G V 1 : Set G)).map f := by
    exact ⟨x^2,factorNormalizer_square_centralizes hx,by rw [map_pow,hxz]⟩
  have hzpow : z^Nat.card L=1 := congrArg Subtype.val (pow_card_eq_one' (x:= (⟨z,hz⟩ : L)))
  obtain ⟨n,hn⟩ := hodd
  have he : (z^2)^(n+1)=z := by
    rw [←pow_mul,show 2*(n+1)=Nat.card L+1 by omega,pow_succ,hzpow,one_mul]
  exact he ▸ ((centralizer (smallSupportGroup G V 1 : Set G)).map f).pow_mem hz2 (n+1)

theorem residual_factorNormalizer_involution_not_centralizer
    (hsplit : FixedPoints.subgroup (smallSupportGroup G V 1) V ⊔
      commutatorAction (smallSupportGroup G V 1) V = ⊤)
    {D : Type*} [Group D] [Finite D] [Group.IsSolvable D]
    (f : G →* D) (hf : Function.Surjective f)
    (hker : ∀ x, f x = 1 → ∀ v ∈ FixedPoints.subgroup (smallSupportGroup G V 1) V,
      x • v = v) (hcore : pCore 2 D=⊥)
    {t : G} (ht : t ∈ factorNormalizer (G:=G) (V:=V))
    (ht2 : t^2=1) (htn : f t≠1) :
    f t ∉ centralizer ((fittingSubgroup G).map f : Set D) := by
  intro hc
  let B := (factorNormalizer (G:=G) (V:=V)).map f
  have hB : B.Normal := Normal.map inferInstance f hf
  let L := fittingSubgroupOf B
  let : L.Normal := fittingSubgroupOf_normal B hB
  let : Group.IsNilpotent L := fittingSubgroupOf_isNilpotent B
  have hLF : L ≤ fittingSubgroup D := le_sSup ⟨inferInstance,inferInstance⟩
  have hLift := residual_factorNormalizer_fitting_lift hsplit f hf hker hcore
  let b : B := ⟨f t,⟨t,ht,rfl⟩⟩
  have hb : b ∈ fittingSubgroup B := by
    apply centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance
    apply mem_centralizer_iff.mpr
    intro a ha
    apply Subtype.ext
    exact mem_centralizer_iff.mp hc a.val (hLift ⟨a,ha,rfl⟩)
  have htF : f t ∈ fittingSubgroup D := hLF ⟨b,hb,rfl⟩
  have ho : orderOf (f t) ∣ Nat.card (fittingSubgroup D) :=
    (fittingSubgroup D).orderOf_dvd_natCard htF
  have ho2 : orderOf (f t) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [←map_pow,ht2,map_one])
  have he : orderOf (f t)=1 := Nat.eq_one_of_dvd_coprimes
    (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot hcore).coprime_two_left ho2 ho
  exact htn (orderOf_eq_one_iff.mp he)
end CFSG.Quasithin.ChapterD.CyclicSource.SmallThree

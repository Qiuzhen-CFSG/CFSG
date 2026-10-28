module
public import Theory.Representation.ExtraspecialBinarySix.FixedPlanes
public import Theory.Representation.ExtraspecialBinarySix
public import Theory.Representation.BinaryOffender.FixedSpaceFaithfulness
public import Theory.Representation.BinaryOffender.FixedKernelResidual
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints
/-!
# Pointwise stabilizers of noncentral cubic fixed planes

In a faithful binary six-space for an extraspecial group of order 27,
the pointwise stabilizer of a noncentral cubic fixed plane meets the
extraspecial group in exactly that cubic. A larger intersection would
contain the center, which acts without nonzero fixed vectors. When the
extraspecial group is the two-residual, this identifies the stabilizer's
literal two-residual.

The stabilizer fixes the extraspecial center. Each of its two-subgroups
acts faithfully on the marked cubic: a nontrivial center-fixing involution
on the extraspecial group fixes only the center. Thus these two-subgroups
have order at most two. The chapter consumer applies all statements to
the original action image, retaining its Sylow and Thompson marking.

Source: Aschbacher--Smith 15.1.16(c)--18, printed pp.1092--1093.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.ExtraspecialBinarySix
variable {D U : Type*} [Group D] [Finite D]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

/-- The fixed plane has exactly its defining cubic as pointwise kernel in P. -/
theorem noncentral_cubic_fixed_kernel
    (ρ : Representation (ZMod 2) D U) (hf : Function.Injective ρ)
    (P : Subgroup D) [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hd : Module.finrank (ZMod 2) U = 6)
    (X : Subgroup P) (hX : Nat.card X = 3) (hXZ : X ≠ center P) :
    subspaceKernel ρ (fixedSpace ρ (X.map P.subtype)) P = X.map P.subtype := by
  let σ := ρ.comp P.subtype
  let W := fixedSpace ρ (X.map P.subtype)
  let K := subspaceKernel ρ W P
  let A := K.subgroupOf P
  have hKP : K ≤ P := subspaceKernel_le ρ W P
  have hXA : X ≤ A := fun x hx => ⟨x.property,fun w hw => hw ⟨x,mem_map_of_mem P.subtype hx⟩⟩
  have hW : W ≠ ⊥ := by
    have hh := (noncentral_cubic_planes ρ hf P hP hd X hX hXZ).1
    change Module.finrank (ZMod 2) W = 2 at hh
    intro he
    rw [he,finrank_bot] at hh
    omega
  let : IsIrreducible σ := RankTwo.ExtraspecialModel.irreducible_of_faithful_six σ
    (hf.comp P.subtype_injective) hP hd
  have hZfix : fixedSpace ρ ((center P).map P.subtype) = ⊥ := by
    rw [←fixedSpace_comp_map]
    change invariants (σ.comp (center P).subtype) = ⊥
    by_contra hn
    have hh := Representation.le_ker_of_normal_invariants_ne_bot σ (center P) hn
    have hb : center P = ⊥ := bot_unique (by
      simpa only [(MonoidHom.ker_eq_bot_iff σ).mpr (hf.comp P.subtype_injective)] using hh)
    have hc := IsExtraspecial.center_order_p 3 P
    rw [hb,card_bot] at hc
    omega
  have hZA : ¬ center P ≤ A := by
    intro hh
    apply hW
    apply bot_unique
    rw [←hZfix]
    intro w hw y
    obtain ⟨z,hz,hze⟩ := y.property
    have he := (hh hz).2 w hw
    change ρ (z : D) w = w at he
    change ρ (y : D) w = w
    rw [←hze]
    exact he
  have hAc : Nat.card A = 3 := by
    have hdiv : Nat.card A ∣ 3^3 := by simpa [hP] using A.card_subgroup_dvd_card
    obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv
    have hlo : 3 ≤ Nat.card A := by
      rw [←hX]
      exact Nat.card_le_card_of_injective (inclusion hXA) (inclusion_injective hXA)
    interval_cases n
    · have hh : Nat.card A = 1 := by simpa only [pow_zero] using he
      omega
    · exact he
    · have hco : IsCoatom A := by
        refine ⟨?_,?_⟩
        · intro htop
          rw [htop,card_top,hP] at he
          norm_num at he
        · intro B hAB
          have hdivB : Nat.card B ∣ 3^3 := by simpa [hP] using B.card_subgroup_dvd_card
          obtain ⟨m,hm,hmcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdivB
          have hlt : Nat.card A < Nat.card B := lt_of_le_of_ne
            (Nat.card_le_card_of_injective (inclusion hAB.le) (inclusion_injective hAB.le))
            (fun hh => hAB.ne (eq_of_le_of_card_ge hAB.le hh.ge))
          interval_cases m <;> norm_num only [pow_zero, pow_one, Nat.reducePow] at hmcard <;> try omega
          exact B.eq_top_of_card_eq (hmcard.trans hP.symm)
      exact (hZA (by rw [←IsExtraspecial.frattini_eq_center_three]; exact frattini_le_coatom hco)).elim
    · exact (hZA (by rw [A.eq_top_of_card_eq (he.trans hP.symm)]; exact le_top)).elim
  have heq : X = A := eq_of_le_of_card_ge hXA (by rw [hX,hAc])
  change K = X.map P.subtype
  rw [heq,map_subgroupOf_eq_of_le hKP]

/-- Identify the literal two-residual of the full pointwise stabilizer. -/
theorem noncentral_cubic_stabilizer_residual
    (ρ : Representation (ZMod 2) D U) (hf : Function.Injective ρ)
    [IsExtraspecial 3 (pResidual 2 D)]
    (hP : Nat.card (pResidual 2 D) = 27) (hd : Module.finrank (ZMod 2) U = 6)
    (X : Subgroup (pResidual 2 D)) (hX : Nat.card X = 3)
    (hXZ : X ≠ center (pResidual 2 D)) :
    let K := subspaceKernel ρ (fixedSpace ρ (X.map (pResidual 2 D).subtype)) ⊤
    (pResidual 2 K).map K.subtype = X.map (pResidual 2 D).subtype := by
  intro K
  let P := pResidual 2 D
  let Y := X.map P.subtype
  have he := noncentral_cubic_fixed_kernel ρ hf P hP hd X hX hXZ
  have hYK : Y ≤ K := by
    rintro x ⟨y,hy,rfl⟩
    exact ⟨mem_top _,fun w hw => hw ⟨y,mem_map_of_mem P.subtype hy⟩⟩
  apply le_antisymm
  · intro x hx
    apply he.le
    refine ⟨map_pResidual_le 2 K.subtype hx,?_⟩
    exact (map_subtype_le _ hx).2
  · have hYc : Nat.card (Y.subgroupOf K) = 3 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hYK).toEquiv,card_map_of_injective P.subtype_injective,hX]
    have hperf : IsPPerfect 2 (Y.subgroupOf K) := by
      apply (pResidual_eq_top_iff 2 _).mp
      apply top_unique
      intro y _
      apply mem_pResidual_of_orderOf_coprime
      exact (show Nat.Coprime 2 3 by decide).of_dvd_right (hYc ▸ orderOf_dvd_natCard y)
    have hh := map_mono (f := K.subtype) (le_pResidual_of_isPPerfect (Y.subgroupOf K) hperf)
    rw [map_subgroupOf_eq_of_le hYK] at hh
    exact hh

/-- The pointwise stabilizer of a noncentral cubic plane fixes the residual center. -/
theorem noncentral_cubic_stabilizer_centralizes_center
    (ρ : Representation (ZMod 2) D U) (hf : Function.Injective ρ)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hd : Module.finrank (ZMod 2) U = 6)
    (X : Subgroup P) (hX : Nat.card X = 3) (hXZ : X ≠ center P) :
    subspaceKernel ρ (fixedSpace ρ (X.map P.subtype)) ⊤ ≤
      centralizer ((center P).map P.subtype : Set D) := by
  let W := fixedSpace ρ (X.map P.subtype)
  let K := subspaceKernel ρ W ⊤
  let Z := (center P).map P.subtype
  let Y := X.map P.subtype
  let : Z.Normal := inferInstance
  have he := noncentral_cubic_fixed_kernel ρ hf P hP hd X hX hXZ
  have hcom : ⁅Z,Y⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rintro z ⟨z,hz,rfl⟩ x ⟨x,hx,rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hz x)
  have hZW : Z ≤ subspaceStabilizer ρ W :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ Z Y hcom
  have hZK : Z ≤ normalizer (K : Set D) := by
    apply le_normalizer_iff.mpr
    intro z hz k hk
    refine ⟨mem_top _,?_⟩
    intro w hw
    have hi : ρ z⁻¹ w ∈ W := (hZW (Z.inv_mem hz) w).mpr hw
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,hk.2 _ hi]
    rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  have hdis : Disjoint Z K := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    obtain ⟨z,hz,hzx⟩ := hx.1
    have hPX : x ∈ Y := he.le ⟨(map_subtype_le _ hx.1),hx.2.2⟩
    obtain ⟨y,hy,hyx⟩ := hPX
    have hzy : z = y := Subtype.ext (hzx.trans hyx.symm)
    have hdXZ : Disjoint X (center P) := by
      have hi : Nat.card (X ⊓ center P : Subgroup P) ∣ 3 := by
        rw [←hX]
        exact card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hi with hi | hi
      · exact disjoint_iff.mpr (card_eq_one.mp hi)
      · have hh : X ⊓ center P = X := eq_of_le_of_card_ge inf_le_left (by rw [hi,hX])
        have hxz : X ≤ center P := hh ▸ inf_le_right
        exact (hXZ (eq_of_le_of_card_ge hxz (by rw [hX,IsExtraspecial.center_order_p 3 P]))).elim
    have hz1 : z = 1 := hdXZ.le_bot ⟨hzy.symm ▸ hy,hz⟩
    exact hzx ▸ congrArg Subtype.val hz1
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  apply hdis.le_bot.trans'
  exact le_inf (le_normalizer_iff_commutator_le_left.mp le_normalizer_of_normal)
    (le_normalizer_iff_commutator_le_right.mp hZK)


/-- Every two-subgroup of the literal plane stabilizer has order at most two. -/
theorem noncentral_cubic_stabilizer_two_subgroup_card_le_two
    (ρ : Representation (ZMod 2) D U) (hf : Function.Injective ρ)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hd : Module.finrank (ZMod 2) U = 6)
    (X : Subgroup P) (hX : Nat.card X = 3) (hXZ : X ≠ center P)
    (Q : Subgroup D) (hQ : IsPGroup 2 Q)
    (hQK : Q ≤ subspaceKernel ρ (fixedSpace ρ (X.map P.subtype)) ⊤) :
    Nat.card Q ≤ 2 := by
  let W := fixedSpace ρ (X.map P.subtype)
  let K := subspaceKernel ρ W ⊤
  let Y := X.map P.subtype
  have hYK : K ≤ normalizer (Y : Set D) := by
    change K ≤ normalizer (X.map P.subtype : Set D)
    rw [←noncentral_cubic_fixed_kernel ρ hf P hP hd X hX hXZ]
    exact pointwiseKernel_normalizes ρ W P K le_normalizer_of_normal le_rfl
  let a := Y.normalizerMonoidHom.comp (inclusion (hQK.trans hYK))
  have hfaith : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply card_eq_one.mp
    rcases (hQ.to_subgroup a.ker).card_eq_or_dvd with hone | htwo
    · exact hone
    obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := a.ker) 2 htwo
    let t : D := (y : Q)
    have ht : orderOf t = 2 := by
      exact (orderOf_injective Q.subtype Q.subtype_injective (y : Q)).trans
        ((orderOf_injective a.ker.subtype a.ker.subtype_injective y).trans hy)
    let b : MulAut P := MulAut.conjNormal t
    have hb : Function.Involutive b := by
      intro x
      have hh : b ^ 2 = 1 := by
        change (MulAut.conjNormal t : MulAut P) ^ 2 = 1
        rw [←map_pow,←ht,pow_orderOf_eq_one,map_one]
      exact congrArg (fun c : MulAut P => c x) (by simpa only [pow_two] using hh)
    have hbne : b ≠ 1 := by
      intro hh
      have hc : t ∈ centralizer (P : Set D) := by
        intro x hx
        have he := congrArg (fun c : MulAut P => (c ⟨x,hx⟩ : D)) hh
        change t * x * t⁻¹ = x at he
        exact (mul_inv_eq_iff_eq_mul.mp he).symm
      have hp : t ∈ P := centralizer_le ρ P hf hP hd hc
      have hone : t = 1 := (hQ.disjoint_of_coprime (IsExtraspecial.isPGroup 3 P)
        (by decide : Nat.Coprime 2 3)).le_bot ⟨(y : Q).property,hp⟩
      rw [hone,orderOf_one] at ht
      omega
    have hbZ : ∀ z ∈ center P, b z = z := by
      intro z hz
      apply Subtype.ext
      change t * (z : D) * t⁻¹ = z
      have hh := noncentral_cubic_stabilizer_centralizes_center ρ hf P hP hd X hX hXZ
        (hQK (y : Q).property) z (mem_map_of_mem P.subtype hz)
      rw [←hh,mul_inv_cancel_right]
    have hfixed := MulAut.fixed_eq_center_of_extraspecial27_involution hP b hb hbne hbZ
    have hXZle : X ≤ center P := by
      intro x hx
      rw [←hfixed]
      apply (MulAut.mem_fixedSubgroup b x).mpr
      apply Subtype.ext
      have hh := congrArg (fun c : MulAut Y => (c ⟨(x : D),mem_map_of_mem P.subtype hx⟩ : D)) y.property
      exact hh
    exact (hXZ (eq_of_le_of_card_ge hXZle (by rw [hX,IsExtraspecial.center_order_p 3 P]))).elim
  have hYc : Nat.card Y = 3 := by rw [card_map_of_injective P.subtype_injective,hX]
  let : IsCyclic Y := isCyclic_of_prime_card hYc
  have hAut : Nat.card (MulAut Y) = 2 := by rw [IsCyclic.card_mulAut,hYc]; decide
  exact (Nat.card_le_card_of_injective a hfaith).trans_eq hAut

end Representation.ExtraspecialBinarySix

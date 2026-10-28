module

public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.FusionInvariantTransfer
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.GroupTheory.Nilpotent

/-!
# Two-residual restriction under fusion control

If H has odd index in a finite group K and controls fusion of its two-elements,
then O²(K) ∩ H is the embedded O²(H), with O² defined by all two-group quotients.

Put J = O²(K), U = J ∩ H and Q = H/O²(H). The subgroup U has odd index in J,
and J is two-perfect. If the image of U lies in the nth lower central subgroup
of Q, its image modulo the next term is central. This gives a character of U
into an abelian two-group, invariant under J-fusion of two-elements by the
fusion hypothesis on H. Transfer to J is trivial by two-perfectness. The
odd-index power formula kills the character on two-elements, and a Sylow
subgroup surjects onto its image, so the whole character is trivial. Induction
places the image of U in every lower central subgroup of the finite two-group
Q. Nilpotence then kills that image.

Source application: Aschbacher, “A 2-local characterization of M12”,
Illinois J. Math. 47 (2003), Proposition 3.3, printed p.38. The transfer
calculation is the one behind *Finite Group Theory*, second edition,
37.3–37.5, printed pp.198–199. The statement of 37.5 includes the derived
subgroups; the lower-central-series argument here supplies the additional
step needed for the full residual intersection.
-/

open Subgroup
open scoped commutatorElement

namespace ResidualFusion

/-- Transfer from a two-perfect group kills fusion-invariant binary-primary characters. -/
private theorem character_eq_one {G A : Type*} [Group G] [CommGroup A] [Finite G]
    (H : Subgroup G) (hindex : Odd H.index) (hperfect : IsPPerfect 2 G)
    (f : H →* A) (hp : IsPGroup 2 A)
    (hf : ∀ x y : H, IsPGroup 2 (zpowers (x : G)) →
      IsConj (x : G) (y : G) → f x = f y) (x : H) : f x = 1 := by
  have ht : ∀ g : G, f.transfer g = 1 := by
    have hk : IsPGroup 2 (G ⧸ f.transfer.ker) :=
      (hp.to_subgroup f.transfer.range).of_equiv
        (QuotientGroup.quotientKerEquivRange f.transfer).symm
    have he := hperfect f.transfer.ker inferInstance hk
    intro g
    exact MonoidHom.mem_ker.mp (he ▸ mem_top g)
  have htwo : ∀ y : H, IsPGroup 2 (zpowers (y : G)) → f y = 1 := by
    intro y hy
    have he := f.transfer_apply_eq_pow_of_conjugate_powers y (by
      intro n z hconj
      exact (hf (y ^ n) z (hy.to_le (zpowers_le.mpr
        ((zpowers (y : G)).pow_mem (mem_zpowers _) n))) hconj).symm)
    have hpow : f y ^ H.index = 1 := he.symm.trans (ht y)
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes
      (hp.orderOf_coprime hindex.coprime_two_left (f y)) dvd_rfl
      (orderOf_dvd_of_pow_eq_one hpow)
  let S : Sylow 2 H := Classical.choice Sylow.nonempty
  let T : Sylow 2 f.range := S.mapSurjective f.rangeRestrict_surjective
  have hT : (T : Subgroup f.range) = ⊤ :=
    top_unique ((hp.to_subgroup f.range).to_subgroup ⊤ |>.le_sylow_of_normal T)
  obtain ⟨y, hy, he⟩ := mem_map.mp
    (show f.rangeRestrict x ∈ (S : Subgroup H).map f.rangeRestrict from
      (show f.rangeRestrict x ∈ (T : Subgroup f.range) by rw [hT]; trivial))
  have hy2 : IsPGroup 2 (zpowers (y : G)) :=
    (S.isPGroup'.map H.subtype).to_le (zpowers_le.mpr (mem_map.mpr ⟨y, hy, rfl⟩))
  exact (congrArg Subtype.val he).symm.trans (htwo y hy2)

/-- An odd-index subgroup restricts with odd index to a normal subgroup. -/
private theorem odd_index_in_normal {G : Type*} [Group G] [Finite G]
    (H J : Subgroup G) [J.Normal] (hindex : Odd H.index) :
    Odd (H.subgroupOf J).index := by
  let S : Sylow 2 H := Classical.choice Sylow.nonempty
  let U : Subgroup G := (S : Subgroup H).map H.subtype
  have hp : IsPGroup 2 U := S.isPGroup'.map H.subtype
  have hi : ¬ 2 ∣ U.index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul S.not_dvd_index hindex.not_two_dvd_nat
  let T : Sylow 2 G := hp.toSylow hi
  obtain ⟨V, hV⟩ := T.exists_subgroupOf_eq_of_normal J
  have hVH : (V : Subgroup J) ≤ H.subgroupOf J := by
    rw [hV]
    exact comap_mono (map_subtype_le _)
  have hVi := V.not_dvd_index
  exact (Nat.odd_iff.mpr (by omega : (V : Subgroup J).index % 2 = 1)).of_dvd_nat
    (index_dvd_of_le hVH)

end ResidualFusion

namespace Subgroup

/-- Odd index and control of two-element fusion identify the exact two-residual intersection. -/
public theorem twoResidual_inf_eq_of_odd_index_fusion {K : Type*} [Group K] [Finite K]
    (H : Subgroup K) (hindex : Odd H.index)
    (hcontrol : ∀ x y : K, x ∈ H → y ∈ H → IsPGroup 2 (zpowers x) →
      IsConj x y → ∃ m ∈ H, m * x * m⁻¹ = y) :
    (pResidual 2 K) ⊓ H = (pResidual 2 H).map H.subtype := by
  apply le_antisymm
  swap
  · exact le_inf (map_pResidual_le 2 H.subtype) (map_subtype_le _)
  let J := pResidual 2 K
  let U : Subgroup J := H.subgroupOf J
  let i : U →* H :=
    { toFun := fun y => ⟨(y.val : K), y.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let Q := H ⧸ pResidual 2 H
  let q : H →* Q := QuotientGroup.mk' (pResidual 2 H)
  have hpQ : IsPGroup 2 Q := isPGroup_quotient_pResidual 2
  have hUseries : ∀ n (y : U), q (i y) ∈ (⊤ : Subgroup Q).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => intro y; trivial
    | succ n ih =>
      let D : Subgroup Q := (⊤ : Subgroup Q).lowerCentralSeries n
      let C : Subgroup Q := ⁅D, ⊤⁆
      let v : H →* Q ⧸ C := (QuotientGroup.mk' C).comp q
      have hv : ∀ y : U, v (i y) ∈ center (Q ⧸ C) := by
        intro y
        apply mem_center_iff.mpr
        intro a
        obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective C a
        apply commutatorElement_eq_one_iff_mul_comm.mp
        change ⁅QuotientGroup.mk' C a, QuotientGroup.mk' C (q (i y))⁆ = 1
        rw [← map_commutatorElement]
        apply (QuotientGroup.eq_one_iff _).mpr
        change ⁅a, q (i y)⁆ ∈ ⁅D, ⊤⁆
        rw [commutator_comm D ⊤]
        exact commutator_mem_commutator (mem_top a) (ih y)
      let : CommGroup (center (Q ⧸ C)) := IsMulCommutative.instCommGroup
      let f : U →* center (Q ⧸ C) := (v.comp i).codRestrict (center (Q ⧸ C)) hv
      have hf : ∀ y : U, f y = 1 := ResidualFusion.character_eq_one (A := center (Q ⧸ C)) U
        (ResidualFusion.odd_index_in_normal H J hindex) (isPPerfect_pResidual 2)
        f ((hpQ.to_quotient C).to_subgroup (center (Q ⧸ C))) (by
          intro x y hx hxy
          have hxK : IsPGroup 2 (zpowers (x.val : K)) := by
            change IsPGroup 2 (zpowers (J.subtype (x : J)))
            rw [← J.subtype.map_zpowers (x : J)]
            exact hx.map J.subtype
          obtain ⟨m, hm, he⟩ := hcontrol (x.val : K) (y.val : K)
            x.property y.property hxK (J.subtype.map_isConj hxy)
          have hc : IsConj (i x) (i y) :=
            isConj_iff.mpr ⟨⟨m, hm⟩, Subtype.ext he⟩
          change f x = f y
          apply Subtype.ext
          exact (v.map_isConj hc).eq_of_left_mem_center (hv x))
      intro y
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val (hf y))
  obtain ⟨n, hn⟩ := nilpotent_iff_lowerCentralSeries.mp hpQ.isNilpotent
  intro x hx
  let y : U := ⟨⟨x, hx.1⟩, hx.2⟩
  have hy := hUseries n y
  rw [hn, mem_bot] at hy
  exact mem_map.mpr ⟨i y, (QuotientGroup.eq_one_iff _).mp hy, rfl⟩

end Subgroup

module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.NormalFourWeakClosureClass
public import Theory.GroupTheory.NormalFourSign
public import BenderSuzuki.External.Hall.theorem_14_4_1
import Mathlib.GroupTheory.Nilpotent

/-!
# A fused normal four is not weakly closed

Let a Sylow two-subgroup have central omega of order two, an elementary
subgroup of order at least eight, and no normal elementary eight. A normal
four whose involutions are fused cannot be weakly closed in a nonsolvable
finite simple group.

The maximal-normal-abelian and centralizer transport argument confines the
returning conjugacy class of the central involution to the four. Fusion then
confines every conjugate of a nonidentity member of the four returning to
its normalizer. Hall 14.4.1 generates that normalizer modulo its transfer
modulus by such conjugates of Engel commutators. All these generators lie
in the proper sign kernel of its action on the four, a contradiction.

This uses conjugacy-class containment only. It makes no claim that all
Sylow involutions belong to the four. The final wrapper retains the normal
quotient-image branch's inputs; several of them are unnecessary once fusion
is supplied explicitly.

Source: Janko--Thompson, Math. Z. 113 (1970), section 6, printed p.395,
refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf;
Hall, The Theory of Groups, Theorem 14.4.1.
-/

open Subgroup
open BenderSuzuki.External
open scoped Pointwise commutatorElement

namespace Stellmacher.Recognition.NormalEightFusedWeakClosure

variable {G : Type*} [Group G] [Finite G]

private theorem residual_eq_top [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G) :
    hallPResidual 2 G = ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : (hallPResidual 2 G).Normal := hallPResidual_normal 2 G
  rcases (inferInstance : (hallPResidual 2 G).Normal).eq_bot_or_eq_top with hb | ht
  · have hp := hallPResidual_quotient_isPGroup (G := G) 2
    have hpbot := hp.of_equiv (QuotientGroup.quotientMulEquivOfEq hb)
    let : Group.IsNilpotent G := (hpbot.of_equiv QuotientGroup.quotientBot).isNilpotent
    exact (hns inferInstance).elim
  · exact ht

omit [Finite G] in
private theorem modulus_le_sign_kernel (H : Subgroup G) (f : H →* ℤˣ) :
    hallTransferModulus 2 H H ≤ f.ker.map H.subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ℤˣ := fun u => ⟨1, Int.units_sq u⟩
  have hres : (hallPResidual 2 H).map H.subtype ≤ f.ker.map H.subtype :=
    map_mono (hallPResidual_le_ker_of_isPGroup f hp)
  refine sup_le (sup_le ?_ ?_) hres
  · apply (closure_le _).mpr
    rintro x ⟨h, rfl⟩
    exact mem_map.mpr ⟨h ^ 2, by simp [MonoidHom.mem_ker, Int.units_sq], rfl⟩
  · apply commutator_le.mpr
    intro x hx y hy
    refine mem_map.mpr ⟨⁅(⟨x, hx⟩ : H), (⟨y, hy⟩ : H)⁆, ?_, rfl⟩
    change f ⁅(⟨x, hx⟩ : H), (⟨y, hy⟩ : H)⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _

private theorem class_mem_of_normal_of_sylow
    (S : Sylow 2 G) (E : Subgroup S) (W H : Subgroup G)
    (hEW : W = E.map (S : Subgroup G).subtype)
    (hSH : (S : Subgroup G) ≤ H) (hHN : H ≤ normalizer (W : Set G))
    (z : S) (hclass : ∀ t : S, IsConj (z : G) (t : G) → t ∈ E)
    (t : G) (htH : t ∈ H) (ht : orderOf t = 2)
    (hzt : IsConj (z : G) t) : t ∈ W := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let tH : H := ⟨t, htH⟩
  have htHorder : orderOf tH = 2 := by simpa [tH] using ht
  have hp : IsPGroup 2 (zpowers tH) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, htHorder]; rfl :
      Nat.card (zpowers tH) = 2 ^ 1)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H T (S.subtype hSH)
  have hconj : g * tH * g⁻¹ ∈ (S.subtype hSH : Subgroup H) := by
    rw [← hg]
    exact mem_map.mpr ⟨tH, hT (mem_zpowers tH), rfl⟩
  let v : S := ⟨(g : G) * t * (g : G)⁻¹, hconj⟩
  have hv : IsConj t (v : G) := isConj_iff.mpr ⟨(g : G), rfl⟩
  have hvW : (v : G) ∈ W := by
    rw [hEW]
    exact mem_map_of_mem _ (hclass v (hzt.trans hv))
  exact (mem_normalizer_iff.mp (hHN g.property) t).mpr hvW

/-- Hall transfer excludes weak closure of the fused normal four under the
normal-only elementary bound. -/
public theorem false_of_weakly_closed [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ B : Subgroup S, B.Normal ∧ IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hfused : ∀ u v : S, u ∈ E → v ∈ E → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G))
    (hweak : ∀ g : G,
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        (S : Subgroup G) →
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom =
        E.map (S : Subgroup G).subtype) : False := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let W := E.map (S : Subgroup G).subtype
  let H := normalizer (W : Set G)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map_subtype
  have hW : Nat.card W = 4 := by
    rw [card_map_of_injective (S : Subgroup G).subtype_injective, hE]
  have hSN : (S : Subgroup G) ≤ H := by
    simpa only [E.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      E.le_normalizer_map (S : Subgroup G).subtype
  have hnc : ¬ (S : Subgroup G) ≤ centralizer (W : Set G) := by
    intro hc
    apply four_not_le_center_of_card_omega_one_center_eq_two hZ E hE
    intro e he
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    exact (hc s.property (e : G) (mem_map_of_mem _ he)).symm
  obtain ⟨f, hf, _, hWK⟩ := exists_normalizer_sign_of_noncentral_four
    (S : Subgroup G) W S.isPGroup' hSN hW hnc
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 := (orderOf_coe (w : center S)).trans ((orderOf_coe w).trans hw)
  have hzC : z ∈ center S := (w : center S).property
  have hclass : ∀ t : S, IsConj (z : G) (t : G) → t ∈ E :=
    fun t ht => S.mem_four_of_isConj_of_weakly_closed_of_no_normal_eight
      hno hZ A hA E hE hweak z t hzC hz ht
  have hzE : z ∈ E := hclass z (IsConj.refl _)
  let K := f.ker.map H.subtype
  have hnot : ¬ H ≤ K := by
    intro h
    obtain ⟨x, hx⟩ := hf
    obtain ⟨y, hy, heq⟩ := mem_map.mp (h x.property)
    have hyx : y = x := Subtype.ext heq
    exact hx (hyx ▸ hy)
  have hresK : (hallPResidual 2 H).map H.subtype ≤ K :=
    le_sup_right.trans (modulus_le_sign_kernel H f)
  have hreslt : (hallPResidual 2 H).map H.subtype < H :=
    lt_iff_le_not_ge.mpr ⟨hresK.trans (map_subtype_le _), fun h => hnot (h.trans hresK)⟩
  have hweak' : WeaklyClosedIn (S : Subgroup G) W :=
    ⟨map_subtype_le E, fun g hg => hweak g⁻¹ hg⟩
  obtain ⟨Zs, hZs, B, hB, hgen⟩ :=
    (hall_theorem_14_4_1_p_hall_of_weakly_closed 2 S W
      (normalizer ((S : Subgroup G) : Set G)) H ⊤ H (S : Subgroup G)
      rfl (weaklyClosedIn_normalizer_le_normalizer hweak') rfl hweak'
      (residual_eq_top hns).symm (by simp) (by simp)).2 hreslt
  apply hnot
  refine hgen.trans (sup_le (modulus_le_sign_kernel H f) ((closure_le _).mpr ?_))
  intro b hb
  obtain ⟨u, v, c, hu, hv, _, hbc, rfl⟩ := hB b hb
  have hvW : v ∈ W := hZs v hv
  have heW : engelSymbol 2 u v ∈ W := by
    have hc : u⁻¹ * v⁻¹ * u ∈ W := by
      simpa using (mem_normalizer_iff.mp (H.inv_mem (hSN hu)) v⁻¹).mp (W.inv_mem hvW)
    exact W.mul_mem hc hvW
  by_cases he : engelSymbol 2 u v = 1
  · simp [he]
  have heorder : orderOf (engelSymbol 2 u v) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (A := W) _ heW) he
  obtain ⟨e, heE, heq⟩ := mem_map.mp heW
  change (e : G) = engelSymbol 2 u v at heq
  have he2 : orderOf e = 2 := by rw [← orderOf_coe e, heq, heorder]
  have hze : IsConj (z : G) (engelSymbol 2 u v) := heq ▸ hfused z e hzE heE hz he2
  have hconj : IsConj (engelSymbol 2 u v) (c * engelSymbol 2 u v * c⁻¹) :=
    isConj_iff.mpr ⟨c, rfl⟩
  have horder : orderOf (c * engelSymbol 2 u v * c⁻¹) = 2 :=
    (MulAut.conj c).orderOf_eq _ |>.trans heorder
  exact hWK (class_mem_of_normal_of_sylow S E W H rfl hSN le_rfl z hclass
    _ hbc horder (hze.trans hconj))

/-- A distinct ambient conjugate of the fused four returns to the Sylow. -/
public theorem exists_distinct_conjugate_four [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ B : Subgroup S, B.Normal ∧ IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hfused : ∀ u v : S, u ∈ E → v ∈ E → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G)) :
    ∃ g : G,
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        (S : Subgroup G) ∧
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≠
        E.map (S : Subgroup G).subtype := by
  classical
  by_contra h
  apply false_of_weakly_closed hns S A hA hZ hno E hE hfused
  intro g hg
  by_contra hne
  exact h ⟨g, hg, hne⟩

/-- The weak-closure conclusion with the inputs of the normal quotient-image
branch. Fusion is explicit and is discharged by its ambient producer. -/
public theorem exists_distinct_returning_conjugate_four [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (_hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ B : Subgroup S, B.Normal ∧ IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (_hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G)) :
    ∃ g : G,
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        (S : Subgroup G) ∧
      (W.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≠
        W.map (S : Subgroup G).subtype :=
  exists_distinct_conjugate_four hns S A hA hZ hno W hW hfused

end Stellmacher.Recognition.NormalEightFusedWeakClosure

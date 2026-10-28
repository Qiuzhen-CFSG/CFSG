module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.PermutedThreeSeed
public import Theory.GroupAction.NineSixteenFixedFactors
public import Mathlib.LinearAlgebra.Projection

/-!
# The two cubic supports of a faithful elementary nine on a four-space

Coprime fixed-point generation constructs complementary order-three actors
with complementary fixed planes. Their opposite moved planes give literal
`SupportFactors` for the original representation. A proper invariant subspace
contains one moved plane, by the order-three fixed-point congruence. Any actor
permuting both planes must then stabilize each; exchanging them would generate
the whole module. Thus reducibility of the odd-core/Sylow join forces Sylow
normalization of both original cubic actors.

These are the linear facts used in Aschbacher--Smith 15.1.2, printed p.1085,
for the elementary-nine endpoint of D.2.17. The Sylow may exchange the planes;
no irreducibility claim is made without the source uniqueness argument.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.BinaryGroupAction
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
 [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

private theorem moved_comp_subtype {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (P : Subgroup G) (K : Subgroup P) :
    subspaceCommutator (ρ.comp P.subtype) ⊤ K =
      subspaceCommutator ρ ⊤ (K.map P.subtype) := by
  unfold subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨k, hk, w, hw, rfl⟩
    exact ⟨k, Subgroup.mem_map_of_mem P.subtype hk, w, hw, rfl⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, w, hw, rfl⟩
    exact ⟨k, hk, w, hw, rfl⟩

private theorem moved_eq_opposite_fixed {H V : Type*} [CommGroup H] [Finite H]
    [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) H V) (K L : Subgroup H)
    (hK : Odd (Nat.card K)) (hC : IsCompl (fixedSpace σ K) (fixedSpace σ L)) :
    subspaceCommutator σ ⊤ K = fixedSpace σ L := by
  have hle : subspaceCommutator σ ⊤ K ≤ fixedSpace σ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, v, _, rfl⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ fixedSpace σ K ⊔ fixedSpace σ L from hC.sup_eq_top ▸ Submodule.mem_top)
    have hu' : σ k u = u := hu ⟨k, hk⟩
    rw [map_add, hu', add_sub_add_left_eq_sub]
    intro l
    change σ (l : H) (σ k w - w) = σ k w - w
    rw [map_sub]
    have hc : σ (l : H) (σ k w) = σ k (σ (l : H) w) := by
      simp only [← Module.End.mul_apply, ← map_mul, mul_comm]
    have hw' : σ (l : H) w = w := hw l
    rw [hc, hw']
  exact (le_iff_eq_of_codisjoint_of_disjoint
    (odd_fixed_moved_complement σ hK).codisjoint hC.disjoint).mp hle

private theorem two_factor_product_bijective {H : Type*} [Group H] [Finite H]
    (K L : Subgroup H) (hcard : Nat.card K * Nat.card L = Nat.card H)
    (hd : Disjoint K L) :
    Function.Bijective (fun x : (i : Fin 2) → (![K, L] i : Subgroup H) =>
      (List.ofFn fun i => (x i : H)).prod) := by
  have hp : Function.Bijective (fun x : K × L => (x.1 : H) * (x.2 : H)) :=
    (Subgroup.isComplement_iff_bijective K L).mp
      (Subgroup.isComplement'_of_card_mul_and_disjoint hcard hd)
  have hh : Function.Bijective (fun x : (i : Fin 2) → (![K, L] i : Subgroup H) =>
      (x 0 : H) * (x 1 : H)) :=
    hp.comp (piFinTwoEquiv (fun i => (![K, L] i : Subgroup H))).bijective
  simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, Fin.succ_zero_eq_one] using hh

private theorem two_support_sum_bijective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (U : Fin 2 → Submodule (ZMod 2) V) (hU : IsCompl (U 0) (U 1)) :
    Function.Bijective (fun v : (i : Fin 2) → U i => ∑ i, (v i : V)) := by
  have hh := (Submodule.prodEquivOfIsCompl (U 0) (U 1) hU).bijective.comp
    (piFinTwoEquiv (fun i => U i)).bijective
  simpa only [Function.comp_def, piFinTwoEquiv_apply,
    Submodule.coe_prodEquivOfIsCompl', Fin.sum_univ_two] using hh

/-- The actual core and its moved planes form the literal two-factor datum. -/
theorem supportFactors_of_nine_four (hf : Function.Injective ρ)
    (P : Subgroup G) [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9) (hdim : Module.finrank (ZMod 2) V = 4)
    (hfixed : fixedSpace ρ P = ⊥) : Nonempty (SupportFactors ρ P 2) := by
  let : CommGroup P := IsMulCommutative.instCommGroup
  let σ : Representation (ZMod 2) P V := ρ.comp P.subtype
  let := action σ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hfσ : Function.Injective σ := fun x y he => Subtype.ext (hf he)
  let := Representation.BinaryGroupAction.faithful σ hfσ
  have hV : Nat.card (Multiplicative V) = 16 := by
    change Nat.card V = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
    norm_num
  have hf : FixedPoints.subgroup (⊤ : Subgroup P) (Multiplicative V) = ⊥ := by
    rw [fixedPoints_eq σ, fixedSpace_comp_map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hfixed]
    exact (submoduleEquivSubgroup (V := V)).map_bot
  obtain ⟨K, L, hK, hL, hKL, hFK, hFL, hF⟩ :=
    nine_sixteen_fixed_factor_decomposition hP hV hf
  have hC : IsCompl (fixedSpace σ K) (fixedSpace σ L) := by
    apply (submoduleEquivSubgroup (V := V)).isCompl_iff.mpr
    simpa only [← fixedPoints_eq σ] using hF
  have hdimF (M : Subgroup P)
      (hc : Nat.card (FixedPoints.subgroup M (Multiplicative V)) = 4) :
      Module.finrank (ZMod 2) (fixedSpace σ M) = 2 := by
    rw [fixedPoints_eq σ, card_submoduleEquivSubgroup,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  have hMK : subspaceCommutator ρ ⊤ (K.map P.subtype) = fixedSpace σ L := by
    rw [← moved_comp_subtype]
    exact moved_eq_opposite_fixed σ K L (hK ▸ (by decide : Odd 3)) hC
  have hML : subspaceCommutator ρ ⊤ (L.map P.subtype) = fixedSpace σ K := by
    rw [← moved_comp_subtype]
    exact moved_eq_opposite_fixed σ L K (hL ▸ (by decide : Odd 3)) hC.symm
  refine ⟨{
    factor := ![K, L]
    card_factor := ?_
    multiply_bijective := two_factor_product_bijective K L (by rw [hK, hL, hP]) hKL.disjoint
    support_dim := ?_
    add_bijective := ?_ }⟩
  · intro i
    fin_cases i
    · exact hK
    · exact hL
  · intro i
    fin_cases i
    · change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (K.map P.subtype)) = 2
      rw [hMK]
      exact hdimF L hFL
    · change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (L.map P.subtype)) = 2
      rw [hML]
      exact hdimF K hFK
  · apply two_support_sum_bijective
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, hMK, hML] using hC.symm

/-- The full-movement form supplied by the D.2 endpoint. -/
theorem supportFactors_of_nine_four_moved (hf : Function.Injective ρ)
    (P : Subgroup G) [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9) (hdim : Module.finrank (ZMod 2) V = 4)
    (hmoved : subspaceCommutator ρ ⊤ P = ⊤) : Nonempty (SupportFactors ρ P 2) := by
  apply supportFactors_of_nine_four ρ hf P hP hdim
  have h := (odd_fixed_moved_complement ρ (hP ▸ (by decide : Odd 9))).disjoint
  rw [hmoved] at h
  exact top_disjoint.mp h

/-- A proper invariant subspace prevents exchange of the two cubic actors. -/
theorem SupportFactors.two_normalized_of_reducible (hf : Function.Injective ρ)
    {P : Subgroup G} [P.Normal] [IsElementaryAbelian 3 P]
    (d : SupportFactors ρ P 2) (S : Subgroup G)
    (C : Submodule (ZMod 2) V) (hC0 : C ≠ ⊥) (hC1 : C ≠ ⊤)
    (hC : P ⊔ S ≤ subspaceStabilizer ρ C) :
    ∀ i, S ≤ normalizer (d.ambient i : Set G) := by
  classical
  have hmoved : subspaceCommutator ρ ⊤ P = ⊤ := by
    rw [← d.ambients_generate ρ, subspaceCommutator_iSup_family]
    exact d.supports_generate ρ
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (IsElementaryAbelian.isPGroup 3 P)
    rw [hn]
    exact (by decide : Odd 3).pow
  have hfixed : fixedSpace ρ P = ⊥ := by
    have hc := (odd_fixed_moved_complement ρ
      hodd).disjoint
    rw [hmoved] at hc
    exact top_disjoint.mp hc
  obtain ⟨i,hi⟩ : ∃ i, subspaceCommutator ρ ⊤ (d.ambient i) ≤ C := by
    by_contra hn
    push Not at hn
    have hh : C ≤ fixedSpace ρ P := by
      rw [← d.ambients_generate ρ, fixedSpace_iSup_family]
      apply le_iInf
      intro i
      exact (plane_separation ρ (d.ambient i)
        ((card_map_of_injective P.subtype_injective).trans (d.card_factor i))
        (d.support_dim i) C ((map_subtype_le _).trans (le_sup_left.trans hC))).resolve_left (hn i)
    exact hC0 (bot_unique (hfixed ▸ hh))
  have hni : S ≤ normalizer (d.ambient i : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    obtain ⟨j,hj⟩ := d.factor_conj_closed ρ hf g i
    have hji : j = i := by
      by_contra hne
      have hjC : subspaceCommutator ρ ⊤ (d.ambient j) ≤ C := by
        rw [← hj, Subgroup.conjBy, ← moved_map_conjugate]
        rintro v ⟨w,hw,rfl⟩
        exact (hC ((show S ≤ P ⊔ S from le_sup_right) hg) w).2 (hi hw)
      apply hC1
      apply top_unique
      rw [← d.supports_generate ρ]
      apply iSup_le
      intro k
      have hk : k = i ∨ k = j := by omega
      rcases hk with rfl | rfl
      · exact hi
      · exact hjC
    change (d.ambient i).conjBy g = d.ambient i
    rw [hji] at hj
    exact hj
  intro k g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  obtain ⟨j,hj⟩ := d.factor_conj_closed ρ hf g k
  by_cases hki : k = i
  · exact hki ▸ mem_normalizer_iff_map_conj_eq.mp (hni hg)
  have hji : j ≠ i := by
    intro he
    have hh : (d.ambient k).conjBy g = (d.ambient i).conjBy g :=
      hj.trans ((congrArg d.ambient he).trans
        (mem_normalizer_iff_map_conj_eq.mp (hni hg)).symm)
    have hh' := congrArg (fun X : Subgroup G => X.conjBy g⁻¹) hh
    simp only [conjBy_inv] at hh'
    exact hki (d.ambient_injective ρ hh')
  have hjk : j = k := by omega
  change (d.ambient k).conjBy g = d.ambient k
  rw [hjk] at hj
  exact hj

end CFSG.Quasithin.ChapterD.FittingConfigurations

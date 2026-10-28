module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialModel
public import Theory.Representation.CubicSixSpaceNilpotence
public import Theory.Representation.InvertedCubicSeed
public import Theory.Representation.CyclicFixedRank

/-!
# A small Sylow fixed space from a square root and cubic-center movement

In the binary six-space, an order-four actor centralizing a fixed-free cubic
and squaring to an involution of displacement two fixes a plane. If the
Sylow subgroup contains this actor and moves the cubic center, its common
fixed space has dimension at most one: the cubic doubles that space inside
the same plane. The square-root existence is kept explicit.

Source application: Aschbacher--Smith 15.1.13--14, printed pp.1090--1091.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01.SourceExtraspecialModel
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

omit [Finite D] in
/-- A square root of the small involution fixes a plane when it commutes
with a fixed-free normal cubic. -/
theorem square_root_fixed_plane
    (ρ : Representation (ZMod 2) D W) (h6 : Module.finrank (ZMod 2) W = 6)
    (Z : Subgroup D) (hZ : Nat.card Z = 3) (hfix : fixedSpace ρ Z = ⊥)
    (x t : D) (ht : t ^ 2 = 1) (hxt : x ^ 2 = t)
    (hxc : x ∈ centralizer (Z : Set D)) (hr : fixedCodim ρ (zpowers t) = 2) :
    fixedSpace ρ (zpowers x) = subspaceCommutator ρ ⊤ (zpowers t) ∧
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers x)) = 2 := by
  have h4 : (ρ x)^4 = 1 := by
    rw [←map_pow,show (4 : ℕ) = 2 * 2 by decide,pow_mul,hxt,ht,map_one]
  have hs : (ρ x)^2 = ρ t := by rw [←map_pow,hxt]
  have hr' : Module.finrank (ZMod 2) (((ρ x)^2-1).range) = 2 := by
    rw [hs]
    exact (fixedCodim_zpowers_eq_displacement_rank ρ t).symm.trans hr
  have hc : ∀ z : Z, Commute (ρ z) (ρ x) := by
    intro z
    exact (show Commute (z : D) x from mem_centralizer_iff.mp hxc z z.property).map ρ
  have hd := (Representation.order_four_fixed_plane_of_commuting_three_group ρ Z
    (IsPGroup.of_card (n := 1) hZ) hfix h6 (ρ x) h4 hr' hc)
  have hk : (ρ x - 1).ker = fixedSpace ρ (zpowers x) := by
    ext w
    rw [LinearMap.mem_ker,LinearMap.sub_apply,Module.End.one_apply,
      sub_eq_zero,mem_fixedSpace_zpowers_iff]
  rw [hk,hs] at hd
  exact ⟨hd.1.trans (CyclicFixedRank.commutator_eq_range ρ t).symm,hd.2⟩

omit [Finite D] in
/-- The square root fixes exactly two binary dimensions. -/
theorem square_root_fixed_dimension
    (ρ : Representation (ZMod 2) D W) (h6 : Module.finrank (ZMod 2) W = 6)
    (Z : Subgroup D) (hZ : Nat.card Z = 3) (hfix : fixedSpace ρ Z = ⊥)
    (x t : D) (ht : t ^ 2 = 1) (hxt : x ^ 2 = t)
    (hxc : x ∈ centralizer (Z : Set D)) (hr : fixedCodim ρ (zpowers t) = 2) :
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers x)) = 2 :=
  (square_root_fixed_plane ρ h6 Z hZ hfix x t ht hxt hxc hr).2

/-- An inverting cubic doubles the Sylow fixed space inside the square
root's fixed plane, so the original common fixed dimension is at most one. -/
theorem sylow_fixed_dimension_le_one_of_square_root
    (ρ : Representation (ZMod 2) D W) (h6 : Module.finrank (ZMod 2) W = 6)
    (Z : Subgroup D) [Z.Normal] (hZ : Nat.card Z = 3) (hfix : fixedSpace ρ Z = ⊥)
    (S : Subgroup D) (x t : D) (hxS : x ∈ S)
    (ht : t ^ 2 = 1) (hxt : x ^ 2 = t)
    (hxc : x ∈ centralizer (Z : Set D)) (hr : fixedCodim ρ (zpowers t) = 2)
    (hm : ¬ S ≤ centralizer (Z : Set D)) :
    Module.finrank (ZMod 2) (fixedSpace ρ S) ≤ 1 := by
  classical
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 (by rw [hZ])
  have hco : orderOf (c : D) = 3 := (orderOf_coe c).trans hc
  have hgen : zpowers (c : D) = Z := eq_of_le_of_card_ge (zpowers_le.mpr c.property)
    (by rw [Nat.card_zpowers,hco,hZ])
  obtain ⟨s,hsS,hsZ⟩ := SetLike.not_le_iff_exists.mp hm
  have hinv : s * (c : D) = (c : D)^2 * s := by
    have hn : (zpowers (c : D)).Normal := by rw [hgen]; infer_instance
    rcases RankTwo.commute_or_invert_of_normal_three (c : D) s hco hn with hh | hh
    · apply False.elim (hsZ ?_)
      rw [←hgen]
      rintro _ ⟨n,rfl⟩
      exact (hh.zpow_left n).eq
    · exact hh
  have hcfree : ∀ w, ρ (c : D) w = w → w = 0 := by
    intro w hw
    have hh := (mem_fixedSpace_zpowers_iff ρ (c : D) w).mpr hw
    rwa [hgen,hfix,Submodule.mem_bot] at hh
  let F := fixedSpace ρ S
  let U := fixedSpace ρ (zpowers x)
  have hFU : F ≤ U := fixedSpace_antitone ρ (zpowers_le.mpr hxS)
  have hU : Module.finrank (ZMod 2) U = 2 :=
    square_root_fixed_dimension ρ h6 Z hZ hfix x t ht hxt hxc hr
  obtain ⟨_,hdouble⟩ := InvertedCubicSeed.moved_seed_and_finrank ρ (c : D) s hco hinv hcfree F
    (fun w hw => hw ⟨s,hsS⟩)
  have hspan : subspaceCommutator ρ F (zpowers (c : D)) ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,w,hw,rfl⟩
    change ρ a w - w ∈ fixedSpace ρ (zpowers x)
    rw [mem_fixedSpace_zpowers_iff,map_sub]
    have hxa : x * a = a * x := (mem_centralizer_iff.mp hxc a (hgen ▸ ha)).symm
    have hxf : ρ x w = w := (mem_fixedSpace_zpowers_iff ρ x w).mp (hFU hw)
    rw [←Module.End.mul_apply,←map_mul,hxa,map_mul,Module.End.mul_apply,hxf]
  have hbound := Submodule.finrank_mono hspan
  rw [hU,hdouble] at hbound
  change Module.finrank (ZMod 2) F ≤ 1
  omega

/-- The central cubic of a faithful extraspecial action on six binary
dimensions has no nonzero fixed vector. -/
theorem extraspecial_center_fixedSpace_eq_bot
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (h6 : Module.finrank (ZMod 2) W = 6) :
    fixedSpace ρ ((center P).map P.subtype) = ⊥ := by
  let σ := ρ.comp P.subtype
  let : IsIrreducible σ := RankTwo.ExtraspecialModel.irreducible_of_faithful_six σ
    (hf.comp P.subtype_injective) hP h6
  rw [←fixedSpace_comp_map]
  change invariants (σ.comp (center P).subtype) = ⊥
  by_contra hh
  have hk := Representation.le_ker_of_normal_invariants_ne_bot σ (center P) hh
  have hb : center P = ⊥ := bot_unique (by
    simpa only [(MonoidHom.ker_eq_bot_iff σ).mpr (hf.comp P.subtype_injective)] using hk)
  have hc := IsExtraspecial.center_order_p 3 P
  rw [hb,card_bot] at hc
  omega

/-- In a faithful extraspecial six-space the square-root fixed plane is
exactly the space moved by its small involution. -/
theorem extraspecial_square_root_fixed_plane
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (h6 : Module.finrank (ZMod 2) W = 6)
    (x t : D) (ht : t ^ 2 = 1) (hxt : x ^ 2 = t)
    (hxc : x ∈ centralizer ((center P).map P.subtype : Set D))
    (hr : fixedCodim ρ (zpowers t) = 2) :
    fixedSpace ρ (zpowers x) = subspaceCommutator ρ ⊤ (zpowers t) ∧
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers x)) = 2 := by
  have hZ : Nat.card ((center P).map P.subtype) = 3 := by
    rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P]
  exact square_root_fixed_plane ρ h6 _ hZ
    (extraspecial_center_fixedSpace_eq_bot ρ hf P hP h6) x t ht hxt hxc hr

/-- Faithfulness in dimension six supplies the fixed-free central cubic
needed by the Sylow fixed-line bound. -/
theorem extraspecial_sylow_fixed_dimension_le_one_of_square_root
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (h6 : Module.finrank (ZMod 2) W = 6)
    (S : Subgroup D) (x t : D) (hxS : x ∈ S)
    (ht : t ^ 2 = 1) (hxt : x ^ 2 = t)
    (hxc : x ∈ centralizer ((center P).map P.subtype : Set D))
    (hr : fixedCodim ρ (zpowers t) = 2)
    (hm : ¬ S ≤ centralizer ((center P).map P.subtype : Set D)) :
    Module.finrank (ZMod 2) (fixedSpace ρ S) ≤ 1 := by
  let Z := (center P).map P.subtype
  have hZ : Nat.card Z = 3 := by
    rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P]
  have hfix : fixedSpace ρ Z = ⊥ := extraspecial_center_fixedSpace_eq_bot ρ hf P hP h6
  exact sylow_fixed_dimension_le_one_of_square_root ρ h6 Z hZ hfix S x t hxS ht hxt hxc hr hm

end CFSG.Quasithin.Chapter15.Section01.SourceExtraspecialModel

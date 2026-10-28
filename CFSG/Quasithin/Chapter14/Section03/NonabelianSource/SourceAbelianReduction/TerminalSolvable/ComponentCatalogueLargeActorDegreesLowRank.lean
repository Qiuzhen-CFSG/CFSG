module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesFiveExclusion
public import CFSG.Quasithin.ChapterG.Section10.Components.CentralizerDisplacement
public import CFSG.Quasithin.ChapterG.Section11.ExchangedModelReduction

/-!
# A low-rank witness for every original larger actor

The larger-center branch already supplies a low-rank element. In the remaining
branch the center is the original point, so the smaller dotted actor vanishes.
The G.10 dimension equation and the larger-actor inequality make the actor's
rank exceed the dimension of the marked isotropic space. Counting its centered
transvection functionals therefore gives a nonidentity actor fixing that space.
Commutation puts its displacement on the marked hyperplane in the common fixed
line, so its whole displacement has rank at most two. Orthogonality and the
original fixed-space bound put the marked point in that displacement.

This proves the exact G.11.1(3ii) witness without a separate fixed-line
classification. The checked low-rank reduction then leaves the requested degree
alternatives or the actual whole/exchanged component models. Exhaustive model
recognition, including an ambient exclusion of any additional exchanged action
in the corrected classifier, remains necessary for the unconditional result.

Source: Aschbacher--Smith G.10.1--2 and G.11.1, printed pp.357,364;
12.8.12--13 and 14.3.13--14, printed pp.855--856,993--994.
-/

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

private theorem exists_nonidentity_fixes_W_of_rank
    (hr : finrank (ZMod 2) W < finrank (ZMod 2) (Additive X)) :
    ∃ a : X, a ≠ 1 ∧ ∀ w : W, ρ a w = w := by
  by_contra! hn
  let f : X → Module.Dual (ZMod 2) W := fun x => (h.transvections x).choose
  have hf : Function.Injective f := by
    intro a b hab
    have he (w : W) : ρ a w = ρ b w := by
      rw [(h.transvections a).choose_spec.2 w, (h.transvections b).choose_spec.2 w]
      exact congrArg (fun t : Module.Dual (ZMod 2) W => (w : V) + t w • v) hab
    have hid : ∀ w : W, ρ (a⁻¹*b : X) w = w := by
      intro w
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply]
      rw [← he w, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    by_contra hab'
    obtain ⟨w,hw⟩ := hn (a⁻¹*b) (fun he => hab' (eq_of_inv_mul_eq_one he))
    exact hw (hid w)
  let : Finite (Module.Dual (ZMod 2) W) := Module.finite_of_finite (ZMod 2)
  have hc := Nat.card_le_card_of_injective f hf
  have hxcard : Nat.card X = 2 ^ finrank (ZMod 2) (Additive X) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X)
  have hwcard : Nat.card (Module.Dual (ZMod 2) W) = 2 ^ finrank (ZMod 2) W := by
    simpa only [Nat.card_zmod, Subspace.dual_finrank_eq] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) W)
  rw [hxcard,hwcard] at hc
  exact (not_le_of_gt hr) ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc)

private theorem low_rank_of_fixed_line_of_smaller_bot
    (hfix : fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (hzero : X₀ = ⊥)
    (hr : finrank (ZMod 2) W < finrank (ZMod 2) (Additive X)) :
    ChapterG.Section11.LowRankWitness ρ v X := by
  obtain ⟨a,ha,hW⟩ := h.exists_nonidentity_fixes_W_of_rank hr
  let δ := ρ a - LinearMap.id
  have hcomm (x : X) (u : V) : ρ x (δ u) = δ (ρ x u) := by
    change ρ x (ρ a u - u) = ρ a (ρ x u) - ρ x u
    rw [map_sub, ← Module.End.mul_apply, ← map_mul,
      show (x : D) * a = a * x from congrArg Subtype.val (mul_comm x a),
      map_mul, Module.End.mul_apply]
  have haxis (u : V) (hu : B v u = 0) : δ u ∈ Submodule.span (ZMod 2) {v} := by
    rw [← hfix]
    intro x
    change ρ x (δ u) = δ u
    rw [hcomm]
    have hd : δ (ρ x u - u) = 0 := by
      change ρ a (ρ x u - u) - (ρ x u - u) = 0
      exact sub_eq_zero.mpr (hW ⟨_,h.displacement x u hu⟩)
    exact sub_eq_zero.mp (by simpa only [map_sub] using hd)
  have hvB : B v ≠ 0 := by
    intro hz
    exact h.point_ne_zero (h.nondegenerate.1 v (fun u => LinearMap.congr_fun hz u))
  obtain ⟨b,hb⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hvB) 1
  have himage : δ.range ≤ Submodule.span (ZMod 2) {δ b} ⊔ Submodule.span (ZMod 2) {v} := by
    rintro _ ⟨u,rfl⟩
    have hz : B v (u - B v u • b) = 0 := by simp [hb]
    have he : δ u = δ (u - B v u • b) + B v u • δ b := by
      rw [map_sub,map_smul]; abel
    rw [he]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (haxis _ hz))
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  have hdim : finrank (ZMod 2) δ.range ≤ 2 := by
    have hh := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span (ZMod 2) {δ b}) (Submodule.span (ZMod 2) {v})
    have h1 : finrank (ZMod 2) (Submodule.span (ZMod 2) {δ b}) ≤ 1 := by
      simpa using finrank_span_le_card ({δ b} : Set V)
    have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) ≤ 1 := by
      simpa using finrank_span_le_card ({v} : Set V)
    have hm := Submodule.finrank_mono himage
    omega
  have hp : v ∈ B.orthogonal δ.ker := by
    intro u hu
    apply h.alternating.isRefl
    exact h.fixed_bound a (by simpa only [hzero,mem_bot] using ha) u (sub_eq_zero.mp hu)
  rw [h.displacement_ker_eq_orthogonal_range a,
    B.orthogonal_orthogonal h.nondegenerate h.alternating.isRefl] at hp
  exact ⟨a,a.property,hdim,hp⟩
end CFSG.Quasithin.ChapterG.Section10.Hypothesis

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

/-- The original smaller dotted actor vanishes when the center is the point. -/
theorem smaller_actor_eq_bot_of_center_point (hZ : F.ZU = F.Vi 1) :
    (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)) = ⊥ := by
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  have hk := Recognition.rankTwo_terminal_center_kernel h F d s.nonabelian
    g s.parabolic_mem s.normalizer_not_mem
  have hle : conjugate F.ZU g ≤ F.terminalHatAction.ker.map F.H.subtype := by
    intro a ha
    have hp : a ∈ conjugate (F.Vi 1) g := hZ ▸ ha
    exact (hk.symm ▸ hp).2
  have hz : F.terminalDot (conjugate F.ZU g) = ⊥ := by
    apply bot_unique
    rintro x ⟨a,ha,rfl⟩
    apply mem_bot.mpr
    apply (QuotientGroup.eq_one_iff a).mpr
    obtain ⟨b,hb,he⟩ := hle ha
    exact (F.H.subtype_injective he) ▸ hb
  rw [hz,bot_subgroupOf]

omit s in
private theorem elementary_rank_eq_finrank (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : Group.rank A = finrank (ZMod 2) (Additive A) := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  apply le_antisymm (IsElementaryAbelian.rank_le_finrank (p := 2) A)
  have hc : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [← hc]
  exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' A
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)))

/-- Every original larger actor supplies the literal G.11.1(3ii) witness. -/
theorem low_rank_witness :
    ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) := by
  rcases s.low_rank_or_extraspecial_fixed_line with hw | ⟨hZ,hfix⟩
  · exact hw
  have hz := s.smaller_actor_eq_bot_of_center_point hZ
  apply s.hypothesis.low_rank_of_fixed_line_of_smaller_bot hfix hz
  have hd := s.hypothesis.dimension
  rw [hz,Group.rank_congr (QuotientGroup.quotientBot),elementary_rank_eq_finrank] at hd
  have hm := s.half_degree_le_actor
  have hl := s.four_le_degree
  obtain ⟨n,hn⟩ := s.even_degree
  omega

/-- The original larger-actor source now reaches the checked low-rank
component reduction in every branch. The remaining model predicate retains
the literal whole component orbit or exchanged constituent action. -/
theorem degree_cases_or_remaining_models :
    ((finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ChapterG.Section11.WholeOrExchangedModelReduction F.terminalRepresentation B v
          (hatSpace F (F.E g)) (F.terminalDot (F.X g))) := by
  rcases ChapterG.Section11.conclusion_or_whole_or_exchanged_models s.hypothesis
      s.classification_input.1 s.low_rank_witness s.normal_sylow with
    hc | ⟨_,hd,hs | ⟨_,hr⟩⟩
  · exact Or.inl (s.degree_cases_of_catalogue hc)
  · exact (s.nonsolvable hs.1).elim
  · exact Or.inr ⟨hd,hr⟩

/-- Apply the numerical branch to the actual component consumer. Only the
explicit remaining whole/exchanged models still require recognition here;
the degree-four and A₆ inputs retain their independent source contracts. -/
theorem component_or_remaining_models
    (hfour : finrank (ZMod 2) (Additive F.Uhat) = 4 →
      ∀ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D →
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ → SmallComponentImage D)
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    ((∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
      (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
        Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
        F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
          pCore 2 (K.subgroupOf F.H))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ChapterG.Section11.WholeOrExchangedModelReduction F.terminalRepresentation B v
          (hatSpace F (F.E g)) (F.terminalDot (F.X g))) := by
  rcases s.degree_cases_or_remaining_models with hd | hr
  · exact Or.inl (source_component_large_actor_of_degree_cases s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis hd hfour hsix)
  · exact Or.inr hr

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

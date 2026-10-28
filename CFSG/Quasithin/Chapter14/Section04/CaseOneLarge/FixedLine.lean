module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedPoint
public import CFSG.Quasithin.ChapterG.Section10.Components.CentralizerDisplacement
public import CFSG.Quasithin.ChapterG.Section11.LowRank

/-!
# Exact ranks in the original fixed-line branch

An actor fixing E pointwise has displacement on the marked hyperplane
contained in the fixed line, so its total displacement has rank at most two.
When no such low-rank witness exists and the smaller actor is trivial, the
centered transvection action on E is therefore faithful. Its functionals lie
in the annihilator of the marked point. Counting them, using isotropy and
the original rank balance, forces E to have half the ambient dimension.

The source application retains the original flag, conjugator, terminal
quotient and marked line. It proves the rank equalities needed in the
fixed-line branch, without claiming recognition of the acting group.

Source: Aschbacher--Smith, G.10.1--2, G.11.1(3i) and 14.4.1--2,
printed pp.357,364,1006.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLine
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {B : LinearMap.BilinForm (ZMod 2) W}
  {v : W} {E : Submodule (ZMod 2) W} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

private theorem lowRank_of_kernel
    (h : ChapterG.Section10.Hypothesis ρ B v E X X₀)
    (hfix : fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (hzero : X₀ = ⊥) (a : X) (ha : a ≠ 1)
    (hE : ∀ w : E, ρ a w = w) : ChapterG.Section11.LowRankWitness ρ v X := by
  let δ := ρ a - LinearMap.id
  have hcomm (x : X) (u : W) : ρ x (δ u) = δ (ρ x u) := by
    change ρ x (ρ a u - u) = ρ a (ρ x u) - ρ x u
    rw [map_sub, ← Module.End.mul_apply, ← map_mul,
      show (x : D) * a = a * x from congrArg Subtype.val (mul_comm x a),
      map_mul, Module.End.mul_apply]
  have haxis (u : W) (hu : B v u = 0) : δ u ∈ Submodule.span (ZMod 2) {v} := by
    rw [← hfix]
    intro x
    change ρ x (δ u) = δ u
    rw [hcomm]
    have hd : δ (ρ x u - u) = 0 :=
      sub_eq_zero.mpr (hE ⟨_, h.displacement x u hu⟩)
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
      simpa using finrank_span_le_card ({δ b} : Set W)
    have h2 : finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) ≤ 1 := by
      simpa using finrank_span_le_card ({v} : Set W)
    have hm := Submodule.finrank_mono himage
    omega
  have hp : v ∈ B.orthogonal δ.ker := by
    intro u hu
    apply h.alternating.isRefl
    exact h.fixed_bound a (by simpa only [hzero,mem_bot] using ha) u (sub_eq_zero.mp hu)
  rw [h.displacement_ker_eq_orthogonal_range a,
    B.orthogonal_orthogonal h.nondegenerate h.alternating.isRefl] at hp
  exact ⟨a,a.property,hdim,hp⟩

private theorem faithful_centered_rank
    (h : ChapterG.Section10.Hypothesis ρ B v E X X₀)
    (hinj : ∀ a b : X, (∀ w : E, ρ a w = ρ b w) → a = b) :
    finrank (ZMod 2) (Additive X) + 1 ≤ finrank (ZMod 2) E := by
  let P := Submodule.span (ZMod 2) {(⟨v,h.point_mem⟩ : E)}
  let f : X → P.dualAnnihilator := fun a => ⟨(h.transvections a).choose, by
    apply (Submodule.mem_dualAnnihilator _).mpr
    change P ≤ LinearMap.ker (h.transvections a).choose
    apply (Submodule.span_le.mpr ?_)
    exact Set.singleton_subset_iff.mpr (h.transvections a).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply hinj a b
    intro w
    rw [(h.transvections a).choose_spec.2 w, (h.transvections b).choose_spec.2 w]
    exact congrArg (fun t : P.dualAnnihilator => (w : W) + t.val w • v) hab
  let : Finite P.dualAnnihilator := Module.finite_of_finite (ZMod 2)
  have hc := Nat.card_le_card_of_injective f hf
  have hxcard : Nat.card X = 2 ^ finrank (ZMod 2) (Additive X) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X)
  have hpcard : Nat.card P.dualAnnihilator = 2 ^ finrank (ZMod 2) P.dualAnnihilator := by
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := P.dualAnnihilator)
  rw [hxcard,hpcard] at hc
  have hr := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  have hp := Subspace.finrank_add_finrank_dualAnnihilator_eq P
  have hdim : finrank (ZMod 2) P = 1 := finrank_span_singleton
    (fun he => h.point_ne_zero (congrArg Subtype.val he))
  omega

/-- The fixed-line branch without a low-rank element has a faithful centered
transvection action on a half-dimensional isotropic space. -/
private theorem ranks_of_no_lowRank
    (h : ChapterG.Section10.Hypothesis ρ B v E X X₀)
    (hfix : fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (hzero : X₀ = ⊥) (hn : ¬ ChapterG.Section11.LowRankWitness ρ v X) :
    2 * finrank (ZMod 2) E = finrank (ZMod 2) W ∧
      finrank (ZMod 2) (Additive X) + 1 = finrank (ZMod 2) E ∧
      ∀ a b : X, (∀ w : E, ρ a w = ρ b w) → a = b := by
  have hk (a : X) (hE : ∀ w : E, ρ a w = w) : a = 1 := by
    by_contra ha
    exact hn (lowRank_of_kernel h hfix hzero a ha hE)
  have hinj : ∀ a b : X, (∀ w : E, ρ a w = ρ b w) → a = b := by
    intro a b hab
    apply eq_of_inv_mul_eq_one
    apply hk
    intro w
    change ρ ((a:D)⁻¹ * b) w = (w:W)
    rw [map_mul,Module.End.mul_apply,← hab w,← Module.End.mul_apply,
      ← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hr := faithful_centered_rank h hinj
  have hd := h.dimension
  rw [hzero, Group.rank_congr (QuotientGroup.quotientBot)] at hd
  have he := B.twice_finrank_le_of_isotropic h.nondegenerate E h.isotropic
  have hx := IsElementaryAbelian.rank_le_finrank (p := 2) X
  have hv : 0 < finrank (ZMod 2) W := by
    let : Nontrivial W := ⟨⟨v,0,h.point_ne_zero⟩⟩
    exact Module.finrank_pos
  exact ⟨by omega,by omega,hinj⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLine

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In the absence of the low-rank branch, the original fixed-line action
already has the exact rank equalities required by 14.4.2. -/
theorem source_terminal_ranks_of_no_lowRank (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat)
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v
      (F.terminalDot (F.X g))) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
      2 * finrank (ZMod 2) (hatSpace F (F.E g)) = finrank (ZMod 2) (Additive F.Uhat) ∧
      Group.rank (F.terminalDot (F.X g)) + 1 = finrank (ZMod 2) (hatSpace F (F.E g)) ∧
      ∀ a b : F.terminalDot (F.X g),
        (∀ w : hatSpace F (F.E g), F.terminalRepresentation a w = F.terminalRepresentation b w) →
        a = b := by
  have hf : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v} := by
    rcases source_terminal_fixed_point_alternative d earlier hq chosen structural alternatives
      F hne g hgP hgH v hline with hf | ⟨a,_,hr,hv⟩
    · exact hf
    · exact (hn ⟨a,a.property,hr,hv⟩).elim
  obtain ⟨_,heX,B,v',hyp,hline',_⟩ :=
    source_terminal_marked_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  have hv' : v' ∈ Submodule.span (ZMod 2) {v} :=
    hline.symm ▸ (hline' ▸ Submodule.mem_span_singleton_self v')
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hv'
  have hc1 : c = 1 := by
    have hb := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
    rcases hb with he | he
    · exact (hyp.point_ne_zero (by simpa [he] using hc.symm)).elim
    · exact he
  have hv : v = v' := by simpa only [hc1,one_smul] using hc
  rw [← hv] at hyp
  have hzero : ((F.terminalDot (conjugate F.ZU g)).subgroupOf
      (F.terminalDot (F.X g))) = ⊥ := by
    rw [source_terminal_conjugate_center F d earlier hq chosen structural alternatives hne hZ g hgP hgH]
    exact bot_subgroupOf _
  obtain ⟨he,_,hinj⟩ := FixedLine.ranks_of_no_lowRank hyp hf hzero hn
  have hr := source_terminal_rank_balance F d earlier hq chosen structural alternatives hne hZ g hgP hgH
  have hvpos : 0 < finrank (ZMod 2) (Additive F.Uhat) := by
    let : Nontrivial (Additive F.Uhat) := ⟨⟨v,0,hyp.point_ne_zero⟩⟩
    exact Module.finrank_pos
  exact ⟨hf.trans hline,he,by omega,hinj⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

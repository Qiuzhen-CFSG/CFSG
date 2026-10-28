module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSelectionFrattini

public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The original inverter and the index-p normalizer subgroup

The disjoint conjugate pair makes the inverter of g unique in V.
In the extraspecial branch, Φ(P) centralizes g and the preceding fixed-point
argument makes it preserve V. It therefore fixes the original inverter,
which normalizes Φ(P)⟨g⟩. This subgroup has order p², index p in P,
and is normalized by P; all statements concern the original ambient G.

LocalConfigurationCyclicConstructionSelectionFrattiniAssembly supplies these
facts with the actual constructed seed. The Baer–Suzuki step in the quotient
of its H-normalizer, the small odd alternatives and terminal source argument
remain with qt-d-12213-cyclic-block.
Source: Aschbacher–Smith, the construction before 12.2.22, printed p.803.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d p : ℕ} {g : G}
namespace CyclicConstructionSeed
variable (S : CyclicConstructionSeed T L V d p H P U g)
include S

omit [Finite G] in
/-- The disjoint pair determines at most one inverter of its rotation in V. -/
theorem inverter_unique {v w : G} (hv : v ∈ V) (hw : w ∈ V)
    (hi : v * g * v⁻¹ = g⁻¹) (hj : w * g * w⁻¹ = g⁻¹) : v = w := by
  have hcV : v⁻¹ * w ∈ V := V.mul_mem (V.inv_mem hv) hw
  have hc : (v⁻¹ * w) * g * (v⁻¹ * w)⁻¹ = g := by
    calc
      _ = v⁻¹ * (w * g * w⁻¹) * v := by group
      _ = v⁻¹ * (v * g * v⁻¹) * v := by rw [hj, hi]
      _ = g := by group
  have hcomm : (v⁻¹ * w) * g = g * (v⁻¹ * w) := mul_inv_eq_iff_eq_mul.mp hc
  have hconj : g * (v⁻¹ * w) * g⁻¹ = v⁻¹ * w := by
    rw [← hcomm, mul_inv_cancel_right]
  have hcB : v⁻¹ * w ∈ V.map (MulAut.conj g).toMonoidHom :=
    ⟨v⁻¹ * w, hcV, hconj⟩
  exact inv_mul_eq_one.mp (mem_bot.mp (S.pair_disjoint.le_bot ⟨hcV, hcB⟩))

/-- In the extraspecial branch the original inverter already centralizes
Φ(P): the latter centralizes g and preserves V, where the inverter is unique. -/
theorem inverter_centralizes_frattini_of_extraspecial
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (he : IsExtraspecial p P) {v : G} (hv : v ∈ V)
    (hi : v * g * v⁻¹ = g⁻¹) :
    v ∈ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) := by
  let : Fact p.Prime := ⟨S.prime⟩
  let := he
  have hn := S.frattini_normalizes_chosen_of_extraspecial D A hTV hTI he
  rintro z ⟨z, hz, rfl⟩
  have hzg : (MulAut.conj (z : G)) g = g := by
    have hc := congrArg Subtype.val (mem_center_iff.mp
      ((IsExtraspecial.frattini_eq_center (p := p) (P := P)) ▸ hz)
      (⟨g, S.generator_mem⟩ : P))
    change g * (z : G) = (z : G) * g at hc
    change (z : G) * g * (z : G)⁻¹ = g
    rw [← hc, mul_inv_cancel_right]
  have hv' : (z : G) * v * (z : G)⁻¹ ∈ V :=
    (mem_normalizer_iff.mp (hn (mem_map_of_mem P.subtype hz)) v).mp hv
  have hi' : ((z : G) * v * (z : G)⁻¹) * g *
      ((z : G) * v * (z : G)⁻¹)⁻¹ = g⁻¹ := by
    have hh := congrArg (MulAut.conj (z : G)) hi
    simp only [map_mul, map_inv, hzg] at hh
    change ((z : G) * v * (z : G)⁻¹) * g *
      ((z : G) * v * (z : G)⁻¹)⁻¹ = g⁻¹ at hh
    exact hh
  exact mul_inv_eq_iff_eq_mul.mp (S.inverter_unique hv' hv hi' hi)


/-- The subgroup Φ(P)⟨g⟩ used in the final normalizer-quotient selection
is invariant under the original inverter. -/
theorem inverter_normalizes_frattini_rotation
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (he : IsExtraspecial p P) {v : G} (hv : v ∈ V)
    (hi : v * g * v⁻¹ = g⁻¹) :
    v ∈ normalizer (((frattini P).map P.subtype ⊔ zpowers g : Subgroup G) : Set G) := by
  have hvΦ := (Subgroup.centralizer_le_normalizer _)
    (S.inverter_centralizes_frattini_of_extraspecial D A hTV hTI he hv hi)
  have hvg : v ∈ normalizer (zpowers g : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (v * g * v⁻¹) = zpowers g
    rw [hi, zpowers_inv]
  exact normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hvΦ, hvg⟩

/-- The original pair rotation is outside Φ(P) once Φ(P) preserves V. -/
theorem generator_not_mem_frattini_of_extraspecial
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (he : IsExtraspecial p P) : g ∉ (frattini P).map P.subtype := by
  intro hg
  have hn := S.frattini_normalizes_chosen_of_extraspecial D A hTV hTI he hg
  have hh := S.pair_disjoint
  have heq : V.map (MulAut.conj g).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hn
  rw [heq] at hh
  exact D.ne_bot (disjoint_self.mp hh)

/-- The elementary plane Φ(P)⟨g⟩ has the literal index p in an
extraspecial odd Sylow of order p³. -/
theorem frattini_rotation_index_of_extraspecial
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (he : IsExtraspecial p P) (hc : Nat.card P = p ^ 3) (hg : orderOf g = p) :
    Nat.card ((frattini P).map P.subtype ⊔ zpowers g : Subgroup G) = p ^ 2 ∧
      ((frattini P).map P.subtype ⊔ zpowers g).relIndex P = p ∧
      P ≤ normalizer (((frattini P).map P.subtype ⊔ zpowers g : Subgroup G) : Set G) := by
  let : Fact p.Prime := ⟨S.prime⟩
  let := he
  let Φ := (frattini P).map P.subtype
  let B := Φ ⊔ zpowers g
  have hΦc : Φ ≤ centralizer (P : Set G) := by
    rintro z ⟨z, hz, rfl⟩ x hx
    exact congrArg Subtype.val (mem_center_iff.mp
      ((IsExtraspecial.frattini_eq_center (p := p) (P := P)) ▸ hz) (⟨x, hx⟩ : P))
  have hBcard : Nat.card B = p ^ 2 := by
    have hn : zpowers g ≤ normalizer (Φ : Set G) :=
      (zpowers_le.mpr S.generator_mem).trans
        ((le_centralizer_iff.mp hΦc).trans (Subgroup.centralizer_le_normalizer _))
    have hd : Disjoint Φ (zpowers g) := Φ.disjoint_zpowers_of_prime_order_not_mem g hg
      (S.generator_not_mem_frattini_of_extraspecial D A hTV hTI he)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint Φ (zpowers g) hn hd,
      card_map_of_injective P.subtype_injective, IsExtraspecial.frattini_eq_center (p := p),
      IsExtraspecial.center_order_p p P, Nat.card_zpowers, hg, pow_two]
  have hBP : B ≤ P := sup_le (map_subtype_le _) (zpowers_le.mpr S.generator_mem)
  have hidx : B.relIndex P = p := by
    have hmul := relIndex_mul_relIndex (⊥ : Subgroup G) B P bot_le hBP
    rw [relIndex_bot_left, relIndex_bot_left, hBcard, hc,
      show p ^ 3 = p ^ 2 * p by ring] at hmul
    exact Nat.eq_of_mul_eq_mul_left (pow_pos S.prime.pos _) hmul
  refine ⟨hBcard, hidx, ?_⟩
  have hcomm : ⁅P, P⁆ = Φ := by
    have hh := map_commutator (⊤ : Subgroup P) ⊤ P.subtype
    rw [← MonoidHom.range_eq_map, P.range_subtype] at hh
    rw [← hh]
    change (_root_.commutator P).map P.subtype = Φ
    rw [IsExtraspecial.commutator_eq_center (p := p),
      ← IsExtraspecial.frattini_eq_center (p := p)]
  apply le_normalizer_iff_commutator_le_right.mpr
  exact (commutator_mono le_rfl hBP).trans (hcomm.le.trans le_sup_left)


/-- Both nonprime alternatives supply the literal index-p normalizer seed:
⟨g⟩ in the elementary-square case and Φ(P)⟨g⟩ in the extraspecial case. -/
theorem exists_index_prime_normalizer_seed
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (halt : Nat.card P = p ∨
      (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
      (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p))
    (hne : Nat.card P ≠ p) (hg : orderOf g = p) {v : G} (hv : v ∈ V)
    (hi : v * g * v⁻¹ = g⁻¹) :
    ∃ B : Subgroup G, B ≤ P ∧ (frattini P).map P.subtype ≤ B ∧
      g ∈ B ∧ B.relIndex P = p ∧ P ≤ normalizer (B : Set G) ∧
      v ∈ normalizer (B : Set G) := by
  let : Fact p.Prime := ⟨S.prime⟩
  rcases halt with hc | ⟨he, hc⟩ | ⟨he, hc, _⟩
  · exact (hne hc).elim
  · let := he
    let : Fact (IsPGroup p P) := ⟨S.pgroup⟩
    have hBP : zpowers g ≤ P := zpowers_le.mpr S.generator_mem
    have hidx : (zpowers g).relIndex P = p := by
      have hm := relIndex_mul_relIndex (⊥ : Subgroup G) (zpowers g) P bot_le hBP
      rw [relIndex_bot_left, relIndex_bot_left, Nat.card_zpowers, hg, hc, pow_two] at hm
      exact Nat.eq_of_mul_eq_mul_left S.prime.pos hm
    refine ⟨zpowers g, hBP, ?_, mem_zpowers g, hidx, ?_, ?_⟩
    · rw [frattini_eq_bot_of_isElementaryAbelian (p := p), Subgroup.map_bot]
      exact bot_le
    · exact ((le_centralizer P).trans (centralizer_le hBP)).trans
        (Subgroup.centralizer_le_normalizer _)
    · rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      change zpowers (v * g * v⁻¹) = zpowers g
      rw [hi, zpowers_inv]
  · obtain ⟨_, hidx, hn⟩ := S.frattini_rotation_index_of_extraspecial D A hTV hTI he hc hg
    exact ⟨(frattini P).map P.subtype ⊔ zpowers g,
      sup_le (map_subtype_le _) (zpowers_le.mpr S.generator_mem), le_sup_left,
      mem_sup_right (mem_zpowers g), hidx, hn,
      S.inverter_normalizes_frattini_rotation D A hTV hTI he hv hi⟩
end CyclicConstructionSeed
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

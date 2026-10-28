module

public import CFSG.Quasithin.Chapter12.Section08.Defs
public import Theory.GroupTheory.IntersectingConjugates
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Elementary source deductions for the marked flag

The actual point normalizer contains L₁T and has nontrivial two-core. Thus
its escape from M puts it in H_z. Its conjugate span is normal there.
The transporter criterion identifies the first three abelian alternatives
of 12.8.6 once 12.8.3 supplies transitivity and escape. These two premises
remain explicit source obligations.

For the nonabelian branch, a conjugator normalizing V gives V≤E and
[Z(U)^g,V]=1, the elementary conclusions 12.8.13(1–2). The final consumer
uses the literal flag parabolic P, not an arbitrary action certificate.
The remaining assertions of 12.8.4–13 are not claimed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 12.8.2 and Lemmas 12.8.3, 12.8.6, 12.8.13, pp.849–855.
-/

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

public theorem Li_le (F : InvariantFlag T V n) (L : Subgroup G) (i : ℕ) :
    F.Li L i ≤ L ⊓ F.Gi i := by
  unfold Li
  split_ifs <;> exact map_subtype_le _

public theorem H_mem_Hz (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (L M : Subgroup G) (hescape : ¬ F.H ≤ M) : F.H ∈ F.Hz L M := by
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 hn
  have htwo : IsPGroup 2 (F.Vi 1) := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hpoint : F.Vi 1 ≤ F.H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes htwo (F.Vi 1).le_normalizer le_rfl
  have hcore : F.H.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hp := le_bot_iff.mp (he ▸ hpoint)
    simp [hp] at hcard
  refine ⟨⟨hcore, ?_⟩, le_rfl, hescape⟩
  exact sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)

public theorem H_eq_centralizer (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (z : G) (hz : F.Vi 1 = zpowers z) : F.H = centralizer ({z} : Set G) := by
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 hn
  have heq : F.H = centralizer (F.Vi 1 : Set G) :=
    le_antisymm (normalizer_le_centralizer_of_card_two _ hcard) (centralizer_le_normalizer _)
  rw [heq, hz, zpowers_eq_closure, centralizer_closure]

public theorem U_le_H (F : InvariantFlag T V n) [IsMulCommutative V] : F.U ≤ F.H := by
  apply conjugateSpanBy_le_self
  exact ((le_centralizer V).trans (centralizer_le (F.le_seed 1))).trans
    (centralizer_le_normalizer _)

public theorem U_normal (F : InvariantFlag T V n) [IsMulCommutative V] :
    (F.U.subgroupOf F.H).Normal :=
  (normal_subgroupOf_iff_le_normalizer F.U_le_H).mpr (le_normalizer_conjugateSpanBy V F.H)

public theorem P_rankTwo (F : InvariantFlag T V 2) (L : Subgroup G) :
    F.P L = L ⊔ (T : Subgroup G) := by
  simp only [P]
  apply inf_eq_left.mpr
  apply le_iInf
  intro i
  apply le_iInf
  intro hi
  omega

public theorem abelian_U_iff_intersections_commute (F : InvariantFlag T V n)
    (hn : 1 ≤ n) (z : G) (hz : F.Vi 1 = zpowers z) (hne : z ≠ 1)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ a ∈ normalizer (V : Set G), (MulAut.conj a) z = x) :
    IsMulCommutative F.U ↔ ∀ g : G, V ⊓ conjugate V g ≠ ⊥ → ⁅V, conjugate V g⁆ = ⊥ := by
  have hzV : z ∈ V := F.le_seed 1 (hz ▸ mem_zpowers z)
  have hcrit := point_span_abelian_iff_intersecting_conjugates_commute V hzV hne htrans
  change IsMulCommutative (conjugateSpanBy V F.H) ↔ _
  rw [F.H_eq_centralizer hn z hz]
  rw [hcrit]
  constructor
  · intro h g
    exact h g⁻¹
  · intro h g
    simpa only [conjugate, inv_inv] using h g⁻¹

public theorem all_local_spans_abelian_iff (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (L M : Subgroup G) (hescape : ¬ F.H ≤ M) :
    (∀ J ∈ F.Hz L M, IsMulCommutative (F.UH J)) ↔ IsMulCommutative F.U := by
  constructor
  · exact fun h => h F.H (F.H_mem_Hz hn L M hescape)
  · intro hc J hJ
    let : IsMulCommutative (conjugateSpanBy V F.H) := hc
    exact conjugateSpanBy_isMulCommutative_of_le (K := F.H) (le_refl V) hJ.2.1

private theorem le_conjugate_of_seed
    (A : Subgroup G) (hVA : V ≤ A) (g : G) (hg : g ∈ normalizer (V : Set G)) :
    V ≤ conjugate A g := by
  intro x hx
  refine ⟨(MulAut.conj g) x, hVA ((mem_normalizer_iff.mp hg x).mp hx), ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

public theorem seed_le_W (F : InvariantFlag T V n) [IsMulCommutative V] : V ≤ F.W :=
  le_inf (le_conjugateSpanBy V F.H)
    ((le_centralizer V).trans (centralizer_le (F.le_seed 2)))

public theorem seed_le_E_of_normalizes (F : InvariantFlag T V n) [IsMulCommutative V]
    (g : G) (hg : g ∈ normalizer (V : Set G)) : V ≤ F.E g :=
  le_inf F.seed_le_W (le_conjugate_of_seed F.W F.seed_le_W g hg)

public theorem conjugate_center_centralizes_seed (F : InvariantFlag T V n)
    (g : G) (hg : g ∈ normalizer (V : Set G)) :
    conjugate F.ZU g ≤ centralizer (V : Set G) := by
  have hc : F.ZU ≤ centralizer (F.U : Set G) := by
    rintro x ⟨x, hx, rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)
  have hmap : conjugate F.ZU g ≤ centralizer (conjugate F.U g : Set G) :=
    (map_mono hc).trans (map_centralizer_le_centralizer_image _ _)
  exact hmap.trans (centralizer_le
    (le_conjugate_of_seed F.U (le_conjugateSpanBy V F.H) g hg))

/-- The marked parabolic normalizes the actual natural module. -/
public theorem P_le_seed_normalizer (F : InvariantFlag T V n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) : F.P L ≤ normalizer (V : Set G) := by
  apply inf_le_left.trans
  apply sup_le hL
  simpa only [F.last] using F.invariant n

/-- The literal parabolic application giving 12.8.13(1–2). Natural-action
normalization is supplied by the setup, independently of the nonabelian analysis. -/
public theorem parabolic_seed_geometry (F : InvariantFlag T V n) [IsMulCommutative V]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hg : g ∈ F.P L) :
    V ≤ F.E g ∧ conjugate F.ZU g ≤ centralizer (V : Set G) := by
  have hn := F.P_le_seed_normalizer L hL hg
  exact ⟨F.seed_le_E_of_normalizes g hn, F.conjugate_center_centralizes_seed g hn⟩

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag

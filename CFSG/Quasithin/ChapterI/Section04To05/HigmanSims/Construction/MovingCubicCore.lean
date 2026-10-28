module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCore
public import Theory.GroupTheory.CoprimeCentralizerCard
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.PGroup.HomocyclicFourRecognition
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# The actual rank-two moving factor of the HS normalizer core

For an overlap cubic x, the whole P=O₂(N_G(V)) splits as its literal
commutator D=[P,⟨x⟩] and its literal centralizer C_P(x). Multiplication
is the marked direct-product equivalence. The moving factor has order16
and inherits square roots from P through this product, identifying it as
C₄². Its first omega subgroup is precisely [V,⟨x⟩], of order4.

These are consequences of HS1--HS2 and retain the original ambient
embeddings needed for the PSL₃(4) endpoint construction at I.4.8, printed
p.418. No endpoint marking, complement or recognition is assumed.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private noncomputable def coordinates (h : TypeAt z V) :
    (normalizer (V : Set G)).pCoreIn 2 ≃* (Fin 3 → Multiplicative (ZMod 4)) :=
  ((pCore 2 (normalizer (V : Set G))).equivMapOfInjective
    (normalizer (V : Set G)).subtype (normalizer (V : Set G)).subtype_injective).symm.trans
    ((MulEquiv.subgroupCongr h.normalizer_fitting.symm).trans h.normalizer_core.some)

private theorem abelian (h : TypeAt z V) :
    IsMulCommutative ((normalizer (V : Set G)).pCoreIn 2) :=
  ⟨⟨fun a b => (coordinates h).injective (by simp only [map_mul, mul_comm])⟩⟩

private theorem core_card (h : TypeAt z V) :
    Nat.card ((normalizer (V : Set G)).pCoreIn 2) = 64 := by
  rw [Nat.card_congr (coordinates h).toEquiv, Nat.card_fun, Nat.card_fin]
  change Nat.card (ZMod 4) ^ 3 = 64
  rw [Nat.card_zmod]
  decide

private theorem fourth (h : TypeAt z V)
    (a : (normalizer (V : Set G)).pCoreIn 2) : a ^ 4 = 1 := by
  apply (coordinates h).injective
  rw [map_pow, map_one]
  have he : ∀ t : Multiplicative (ZMod 4), t ^ 4 = 1 := by decide +kernel
  exact funext (fun i => he (coordinates h a i))

private theorem roots (h : TypeAt z V)
    (a : (normalizer (V : Set G)).pCoreIn 2) (ha : a ^ 2 = 1) :
    ∃ b : (normalizer (V : Set G)).pCoreIn 2, b ^ 2 = a := by
  have hr : ∀ a : Multiplicative (ZMod 4), a ^ 2 = 1 → ∃ b, b ^ 2 = a := by decide +kernel
  have hc (i : Fin 3) : ∃ b : Multiplicative (ZMod 4), b ^ 2 = coordinates h a i :=
    hr _ (by simpa only [map_pow, map_one, Pi.pow_apply, Pi.one_apply] using
      (congrArg (fun c => coordinates h c i) ha))
  choose b hb using hc
  refine ⟨(coordinates h).symm b, (coordinates h).injective ?_⟩
  rw [map_pow, MulEquiv.apply_symm_apply]
  exact funext hb

omit [Finite G] in
private theorem normalizes_core : normalizer (V : Set G) ≤
    normalizer (((normalizer (V : Set G)).pCoreIn 2 : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg a ha
  obtain ⟨aM, haM, he⟩ := ha
  refine ⟨⟨g, hg⟩ * aM * (⟨g, hg⟩ : normalizer (V : Set G))⁻¹,
    (inferInstance : (pCore 2 (normalizer (V : Set G))).Normal).conj_mem aM haM ⟨g, hg⟩, ?_⟩
  change g * (aM : G) * g⁻¹ = g * a * g⁻¹
  rw [show (aM : G) = a from he]

/-- The literal moving factor has order sixteen and multiplies with the
literal cyclic-four centralizer to give the whole original core. -/
theorem TypeAt.cubic_core_product (h : TypeAt z V) (x : G)
    (hx : x ∈ involutionCentralizer z ⊓ normalizer (V : Set G))
    (hx3 : orderOf x = 3) :
    let P := (normalizer (V : Set G)).pCoreIn 2
    let D := ⁅P, zpowers x⁆
    let C := P ⊓ centralizer ({x} : Set G)
    Nat.card D = 16 ∧ D ⊔ C = P ∧ Disjoint D C ∧
      ∃ e : D × C ≃* P, ∀ d c, (e (d, c) : G) = (d : G) * (c : G) := by
  dsimp only
  let P := (normalizer (V : Set G)).pCoreIn 2
  let D := ⁅P, zpowers x⁆
  let C := P ⊓ centralizer ({x} : Set G)
  let := abelian h
  have hn : zpowers x ≤ normalizer (P : Set G) := zpowers_le.mpr (normalizes_core hx.2)
  have hcop : Nat.Coprime (Nat.card (zpowers x)) (Nat.card P) := by
    rw [Nat.card_zpowers, hx3, core_card h]
    decide
  have hd : Disjoint D C := by
    simpa only [D, C, zpowers_eq_closure, centralizer_closure] using
      commutator_disjoint_centralizer_of_coprime P (zpowers x) hn hcop
  have hgen : D ⊔ C = P := by
    simpa only [D, C, zpowers_eq_closure, centralizer_closure] using
      (eq_commutator_sup_centralizer_of_solvable_coprime P (zpowers x) hn
        (Group.isSolvable_of_comm fun a b => mul_comm a b) hcop).symm
  have hDP : D ≤ P := le_normalizer_iff_commutator_le_left.mp hn
  have hDC : D ≤ centralizer (C : Set G) := hDP.trans
    ((le_centralizer P).trans (centralizer_le inf_le_left))
  obtain ⟨c, _, _, hc4, hc⟩ := h.cubic_normalizer_core x hx hx3
  have hcardC : Nat.card C = 4 := by rw [show C = zpowers c from hc, Nat.card_zpowers, hc4]
  have hcent : centralizer (zpowers x : Set G) = centralizer ({x} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hm := commutator_card_mul_centralizer_card P (zpowers x) hn hcop
  have hcardD : Nat.card D = 16 := by
    rw [hcent] at hm
    change Nat.card D * Nat.card C = Nat.card P at hm
    rw [hcardC, core_card h] at hm
    omega
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting D C hd hDC
  exact ⟨hcardD, hgen, hd, e.trans (MulEquiv.subgroupCongr hgen), he⟩

/-- The actual coprime commutator of the full normalizer core is C₄².
Square roots are projected through the marked internal product. -/
theorem TypeAt.cubic_moving_core (h : TypeAt z V) (x : G)
    (hx : x ∈ involutionCentralizer z ⊓ normalizer (V : Set G))
    (hx3 : orderOf x = 3) :
    Nonempty ((⁅(normalizer (V : Set G)).pCoreIn 2, zpowers x⁆ : Subgroup G) ≃*
      (Fin 2 → Multiplicative (ZMod 4))) := by
  let P := (normalizer (V : Set G)).pCoreIn 2
  let D := ⁅P, zpowers x⁆
  let C := P ⊓ centralizer ({x} : Set G)
  obtain ⟨hcard, hgen, _, e, he⟩ := h.cubic_core_product x hx hx3
  have hDP : D ≤ P := le_sup_left.trans hgen.le
  let := abelian h
  let : IsMulCommutative D := ⟨⟨fun a b => Subtype.ext
    (congrArg (fun p : P => (p : G))
      (mul_comm (⟨a, hDP a.property⟩ : P) (⟨b, hDP b.property⟩ : P)))⟩⟩
  have hfourth (a : D) : a ^ 4 = 1 := Subtype.ext
    (congrArg (fun p : P => (p : G)) (fourth h ⟨a, hDP a.property⟩))
  have hroot (a : D) (ha : a ^ 2 = 1) : ∃ b : D, b ^ 2 = a := by
    let aP : P := ⟨a, hDP a.property⟩
    obtain ⟨b, hb⟩ := roots h aP (Subtype.ext (congrArg (fun d : D => (d : G)) ha))
    obtain ⟨⟨d, c⟩, hedc⟩ := e.surjective b
    have hea : e (a, 1) = aP := Subtype.ext (by
      rw [he, coe_one, mul_one])
    have heq : (d, c) ^ 2 = (a, 1) := e.injective (by
      rw [map_pow, hedc, hb, hea])
    exact ⟨d, congrArg Prod.fst heq⟩
  obtain ⟨f⟩ := homocyclicFour_of_square_roots hfourth hroot (n := 2) hcard
  exact ⟨f.trans (MulEquiv.funMultiplicative (Fin 2) (ZMod 4))⟩

/-- The omega subgroup of the actual rank-two moving core is exactly the
actual moved plane of V, and this plane has order four. -/
theorem TypeAt.cubic_moving_omega (h : TypeAt z V) (x : G)
    (hx : x ∈ involutionCentralizer z ⊓ normalizer (V : Set G))
    (hx3 : orderOf x = 3) :
    omegaOneAmbient (⁅(normalizer (V : Set G)).pCoreIn 2, zpowers x⁆) = ⁅V, zpowers x⁆ ∧
      Nat.card (⁅V, zpowers x⁆ : Subgroup G) = 4 := by
  let P := (normalizer (V : Set G)).pCoreIn 2
  let D := ⁅P, zpowers x⁆
  let C := P ⊓ centralizer ({x} : Set G)
  let E := ⁅V, zpowers x⁆
  let Z := zpowers z
  let := abelian h
  let := h.elementary
  have heP : centralizer (V : Set G) = P := h.seed_centralizer
  have hVP : V ≤ P := heP ▸ le_centralizer V
  have hn : zpowers x ≤ normalizer (V : Set G) := zpowers_le.mpr hx.2
  have hEV : E ≤ V := le_normalizer_iff_commutator_le_left.mp hn
  have hED : E ≤ D := commutator_mono hVP le_rfl
  have hcop : Nat.Coprime (Nat.card (zpowers x)) (Nat.card V) := by
    rw [Nat.card_zpowers, hx3, h.seed_card]
    decide
  have hcent : centralizer (zpowers x : Set G) = centralizer ({x} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hgenV : E ⊔ Z = V := by
    have hh := eq_commutator_sup_centralizer_of_solvable_coprime V (zpowers x) hn
      (Group.isSolvable_of_comm fun a b => mul_comm a b) hcop
    rw [hcent, h.cubic_seed_fixed x hx hx3] at hh
    exact hh.symm
  have hEcard : Nat.card E = 4 := by
    have hh := commutator_card_mul_centralizer_card V (zpowers x) hn hcop
    rw [hcent, h.cubic_seed_fixed x hx hx3, Nat.card_zpowers, h.involution, h.seed_card] at hh
    change Nat.card E * 2 = 8 at hh
    omega
  obtain ⟨_, hgen, hdis, _⟩ := h.cubic_core_product x hx hx3
  have hDP : D ≤ P := le_sup_left.trans hgen.le
  have hZC : Z ≤ C := by
    change zpowers z ≤ P ⊓ centralizer ({x} : Set G)
    rw [← h.cubic_seed_fixed x hx hx3]
    exact inf_le_inf hVP le_rfl
  have hDZ : Disjoint D Z := hdis.mono_right hZC
  have hEZ : E ≤ normalizer (Z : Set G) := hEV.trans
    ((le_centralizer V).trans ((centralizer_le (zpowers_le.mpr h.involution_mem_seed)).trans
      (centralizer_le_normalizer _)))
  have hDV : D ⊓ V = E := by
    apply le_antisymm ?_ (le_inf hED hEV)
    intro a ha
    have hm : a ∈ (E : Set G) * (Z : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right E Z hEZ, hgenV]
      exact ha.2
    obtain ⟨e, he, c, hc, hec⟩ := hm
    have hcD : c ∈ D := by
      have hh := D.mul_mem (D.inv_mem (hED he)) ha.1
      rw [← hec] at hh
      simpa only [inv_mul_cancel_left] using hh
    have hc1 : c = 1 := hDZ.le_bot ⟨hcD, hc⟩
    change e * c = a at hec
    rw [hc1, mul_one] at hec
    exact hec ▸ he
  have hsquare (a : G) (ha : a ∈ P) : a ^ 2 = 1 ↔ a ∈ V := by
    constructor
    · intro hsq
      obtain ⟨aM, haM, rfl⟩ := ha
      have hw : aM ∈ (omega (pCore 2 (normalizer (V : Set G))) (p := 2) 1).map
          (pCore 2 (normalizer (V : Set G))).subtype :=
        ⟨⟨aM, haM⟩, subset_closure (show (⟨aM, haM⟩ : pCore 2 (normalizer (V : Set G))) ^ (2^1) = 1 from
          Subtype.ext (Subtype.ext hsq)), rfl⟩
      rw [← h.seed_eq_omega_normalizer_core] at hw
      exact hw
    · exact fun hv => elemPow_eq_one_of_isElementaryAbelian (p := 2) a hv
  refine ⟨le_antisymm ?_ ?_, hEcard⟩
  · apply (omegaOneAmbient_le_iff D E).mpr
    intro a ha hs
    exact hDV.le ⟨ha, (hsquare a (hDP ha)).mp hs⟩
  · intro a ha
    apply (omegaOneAmbient_le_iff D (omegaOneAmbient D)).mp le_rfl a (hED ha)
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) a (hEV ha)

end CFSG.Quasithin.HigmanSims

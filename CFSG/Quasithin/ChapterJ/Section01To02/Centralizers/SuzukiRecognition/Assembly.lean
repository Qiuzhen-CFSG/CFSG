module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.FullCentralizer
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.CubicAction

/-!
# Assembly of J.2.9 and the local Suzuki input to J.2.10

The explicit preceding J.2.3/J.2.7 witnesses supply the local Sylow product,
fusion and embedded Z₂ × Sz(2). Two model involutions whose product has order
five produce a non-core member, eliminating normality of V in the residual.
The checked strong-embedding theorem then recognizes the whole two-residual
as the actual matrix group Sz(8), without an ambient SQTK assumption.

Borel rigidity, the residual supplement and the cubic orbit construct all
three clauses of J.2.9. The consumed odd-torus results retain the actual
Sylow images and the outer action. In particular the corrected intersection
is C_G(Y) ∩ N_G(S₀) = YS₀; the source's printed S₀ omits Y.
The parent Centralizers task constructs the earlier witnesses and the odd
complement used by the final J.2.10 adapter.

Source: Aschbacher–Smith, J.2.9–10, printed p.438 (PDF p.449).
-/

@[expose] public section
open Subgroup BenderSuzuki.PFAppendixIII BenderSuzuki.MatrixGroups
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalSetup G} (c : Choices d)

/-- The literal conclusions of J.2.9 and the residual geometry used to prove them.
The constructor below proves these fields from earlier local witnesses. -/
structure SuzukiSourceConclusion where
  model : c.Ls ≃* SuzukiMatrixGroup 1
  sylow : Sylow 2 c.Ls
  sylow_eq : (sylow : Subgroup c.Ls) = c.S1.subgroupOf c.Ls
  sylow_card : Nat.card sylow = 64
  omega_eq : (omega₁ c.S1 (p := 2)).map c.S1.subtype = d.V
  centralizers : ∀ v : c.Ls, v ∈ d.V.subgroupOf c.Ls → v ≠ 1 →
    centralizer ({v} : Set c.Ls) = c.S1.subgroupOf c.Ls
  proper_normalizer : normalizer (d.V.subgroupOf c.Ls : Set c.Ls) ≠ ⊤
  ti : IsTISubgroup (d.V.subgroupOf c.Ls)
  strong_embedding : BenderSuzuki.IsStronglyEmbedded
    (normalizer (d.V.subgroupOf c.Ls : Set c.Ls))
  product : c.S0 × c.Ls ≃* c.Gs
  product_apply : ∀ a l, (product (a,l) : G) = (a : G) * (l : G)
  central : c.S0 ≤ centralizer (c.Ls : Set G)
  centralizer_eq : c.Gs = c.S0 ⊔ c.Ls
  centralizer_nonidentity : ∀ s0 ∈ c.S0, s0 ≠ 1 →
    centralizer ({s0} : Set G) = c.S0 ⊔ c.Ls
  normalizer_product : (normalizer (c.S0 : Set G) : Set G) =
    (c.Gs : Set G) * (c.B : Set G)
  normalizes_residual : normalizer (c.S0 : Set G) ≤ normalizer (c.Ls : Set G)
  outer : ∀ b ∈ c.B, b ≠ 1 →
    ¬ ∃ l ∈ c.Ls, ∀ x ∈ c.Ls, b*x*b⁻¹ = l*x*l⁻¹
  involutions : {x : G | IsConj c.z x} ∩ (c.Gs : Set G) =
    {x : G | x ∈ c.Ls ∧ IsInvolution x}
  cubic : SuzukiRecognition.CubicProduct (normalizer (c.S0 : Set G))
  cubic_E : cubic.E = c.S0.subgroupOf (normalizer (c.S0 : Set G))
  cubic_L : cubic.L = c.Ls.subgroupOf (normalizer (c.S0 : Set G))
  cubic_B : cubic.B = c.B.subgroupOf (normalizer (c.S0 : Set G))

/-- J.2.9 from explicit J.2.3 and J.2.7 witnesses.

The small-model embedding and its fusion are J.2.7(7); the H-fusion and
Sylow-centralizer identity are J.2.7(8),(10). The other local product,
Suzuki two-group, orders and Singer orbit are J.2.3. No residual-model,
non-core, SQTK, simplicity, outer-action or J.2.10 premise is assumed. -/
theorem source_suzuki_recognition [IsElementaryAbelian 2 c.S0]
    (P : Sylow 2 c.Gs) (hP : (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs)
    (e : P ≃* c.S0 × c.S1)
    (he : ∀ x : P, ((x : c.Gs) : G) = ((e x).1 : G) * ((e x).2 : G))
    (hS0 : Nat.card c.S0 = 4) (hTs : Nat.card c.Ts = 256)
    (hB : Nat.card c.B = 3)
    (hsuzuki : IsSuzukiTwoGroup c.S1) (htrans : c.B7TransitiveOnV)
    (hCL : d.L ⊓ c.Gs = c.Ts ⊔ c.B7)
    (hH : centralizer ({c.z} : Set G) = d.toTypeRuSetup.H)
    (hHs : d.toTypeRuSetup.H ⊓ c.Gs = c.Ts)
    (hzV : c.z ∈ d.V) (hz1 : c.z ≠ 1)
    (hsfusion : ∀ t ∈ d.toTypeRuSetup.H, IsConj c.s t →
      ∃ h ∈ d.toTypeRuSetup.H, h*c.s*h⁻¹ = t)
    {t : G} (hst : IsConj c.s t)
    (f : Multiplicative (ZMod 2) × SuzukiMatrixGroup 0 →*
      centralizer ({t} : Set G)) (hf : Function.Injective f)
    (hzfusion : ∀ u : Multiplicative (ZMod 2) × SuzukiMatrixGroup 0,
      u.1 = 1 → orderOf u = 2 → IsConj c.z (f u : G)) :
    Nonempty (c.SuzukiSourceConclusion) := by
  have hVL := (c.V_le_S1 hsuzuki.2.1 htrans).trans c.S1_le_Ls
  have hzn := c.z_not_mem_twoCore_of_suzukiZero_embedding hH hsfusion hst f hf hzfusion
  obtain ⟨hd, _, hω, Q, hQ, hV, hC, hn, hti, hstrong⟩ :=
    c.residual_recognition_inputs P hP e he hsuzuki htrans hCL hH hHs hzV hz1
      hsfusion (IsConj.refl c.s) (c.Ls_le_Gs (hVL hzV)) (IsConj.refl c.z) hzn
  have hQcard : Nat.card Q = 64 := by
    rw [hQ, natCard_subgroupOf_eq c.S1 c.Ls c.S1_le_Ls]
    exact c.S1_card_of_local_product P hP e hS0 hTs
  obtain ⟨model⟩ := c.suzuki_of_residual_inputs Q hQ hQcard hVL hV hC hn
  obtain ⟨hc,prod,hprod⟩ := c.Gs_internalProduct_of_suzuki P hP e he model Q hQ hd
    (c.local_product_transfer_geometry P hP e he hsuzuki htrans).1
  have hGs := c.Gs_eq_S0_sup_Ls_of_local_product P hP e he
  have horbit := c.B_orbit_S0 hB
  have hfused : ∀ s0 ∈ c.S0, s0 ≠ 1 → IsConj c.s s0 := by
    intro s0 hs hs1
    obtain ⟨b,hb,hbEq⟩ := horbit s0 hs hs1
    exact isConj_iff.mpr ⟨b,hbEq⟩
  have hall (s0 : G) (hs : s0 ∈ c.S0) (hs1 : s0 ≠ 1) :=
    c.centralizer_S0_nonidentity hGs hc hfused hs hs1
  obtain ⟨hgen,hLN,hfactor⟩ := c.normalizer_S0_factorization hGs hc c.B_normalizes_S0 horbit
  have houter := c.B_outer_on_Ls model hB (c.B_normalizes_S0.trans hLN) hVL
  have hGsCard : Nat.card c.Gs = 116480 := by
    rw [← Nat.card_congr prod.toEquiv, Nat.card_prod, hS0,
      Nat.card_congr model.toEquiv, suzukiMatrixGroup_card 1 (by decide)]
    norm_num
  have hfree : ∀ b ∈ c.B, b ≠ 1 → ∀ s0 ∈ c.S0, s0 ≠ 1 → b*s0*b⁻¹ ≠ s0 := by
    intro b hb hb1 s0 hs hs1 hfix
    have hbGs : b ∈ c.Gs := by
      rw [← hall s0 hs hs1]
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)
    have hdis : Disjoint c.B c.Gs := disjoint_of_coprime_natCard (by
      rw [hB,hGsCard]; decide)
    exact hb1 (disjoint_def.mp hdis hb hbGs)
  let k := c.normalizerCubicProduct model hS0 hB hc hd hLN c.B_normalizes_S0
    (by rw [← hGs]; exact hgen) hfree houter
  refine ⟨{
    model := model
    sylow := Q
    sylow_eq := hQ
    sylow_card := hQcard
    omega_eq := hω
    centralizers := hC
    proper_normalizer := hn
    ti := hti
    strong_embedding := hstrong
    product := prod
    product_apply := hprod
    central := hc
    centralizer_eq := hGs
    centralizer_nonidentity := ?_
    normalizer_product := ?_
    normalizes_residual := hLN
    outer := houter
    involutions := c.z_class_intersection_Gs Q hQ hsuzuki htrans hzV hz1 hH hsfusion
    cubic := k
    cubic_E := rfl
    cubic_L := rfl
    cubic_B := rfl }⟩
  · intro s0 hs hs1
    exact (hall s0 hs hs1).trans hGs
  · ext n
    constructor
    · intro hn
      obtain ⟨g,hg,b,hb,heq⟩ := hfactor n hn
      exact Set.mem_mul.mpr ⟨g,hg,b,hb,heq.symm⟩
    · rintro ⟨g,hg,b,hb,rfl⟩
      rw [← hgen]
      exact (c.Gs ⊔ c.B).mul_mem ((show c.Gs ≤ c.Gs ⊔ c.B from le_sup_left) hg)
        ((show c.B ≤ c.Gs ⊔ c.B from le_sup_right) hb)

/-- The exact local input consumed by J.2.10, including the corrected
intersection and the full automizer on the literal Sylow image. -/
theorem SuzukiSourceConclusion.oddPrime_local_consequences
    (r : c.SuzukiSourceConclusion)
    {p : ℕ} [Fact p.Prime] (hp : p = 7 ∨ p = 13) (Y : Sylow p c.Ls) :
    let YG := (Y : Subgroup c.Ls).map c.Ls.subtype
    Nat.card (normalizer (c.S0 : Set G)) = 349440 ∧
      Nat.card Y = p ∧ Nat.card YG = p ∧
      centralizer (YG : Set G) ⊓ normalizer (c.S0 : Set G) = YG ⊔ c.S0 ∧
      (∀ s0 ∈ c.S0, s0 ≠ 1 →
        centralizer (YG : Set G) ⊓ centralizer ({s0} : Set G) = YG ⊔ c.S0) ∧
      ∀ α : MulAut YG, ∃ n : normalizer (YG : Set G),
        (n : G) ∈ normalizer (c.S0 : Set G) ∧ YG.normalizerMonoidHom n = α := by
  obtain ⟨hcard,himage,hinter⟩ := c.oddPrime_model_card_and_intersection r.model r.central hp Y
    (r.centralizer_nonidentity c.s c.s_mem c.s_ne_one)
  obtain ⟨hN,hAut⟩ := c.oddPrime_normalizer_model r.cubic r.cubic_E r.cubic_L r.central hp Y
  exact ⟨r.cubic.card,hcard,himage,hN,fun s0 hs hs1 =>
    (c.oddPrime_model_card_and_intersection r.model r.central hp Y
      (r.centralizer_nonidentity s0 hs hs1)).2.2,hAut⟩

/-- The parent only has to construct the odd complement in J.2.10.
All Suzuki and local automizer premises have been discharged. -/
theorem SuzukiSourceConclusion.oddPrime_conclusions [IsElementaryAbelian 2 c.S0]
    (r : c.SuzukiSourceConclusion)
    {p : ℕ} [Fact p.Prime] (hp : p = 7 ∨ p = 13) (Y : Sylow p c.Ls)
    (P : Subgroup G) (hodd : Odd (Nat.card P))
    (a b : normalizer (P : Set G))
    (ha : a^2 = 1) (hb : b^2 = 1) (hab : Commute a b)
    (hdecomp : centralizer ((Y : Subgroup c.Ls).map c.Ls.subtype : Set G) = P ⊔ c.S0)
    (hfour : ∀ t ∈ ({(a : G), (b : G), ((a*b : normalizer (P : Set G)) : G)} : Set G),
      t ∈ c.S0 ∧ t ≠ 1) :
    let YG := (Y : Subgroup c.Ls).map c.Ls.subtype
    Nat.card YG = p ∧ (∃ S : Sylow p G, (S : Subgroup G) = YG) ∧
      normalizer (YG : Set G) ≤ normalizer (c.S0 : Set G) ∧
      centralizer (YG : Set G) = YG ⊔ c.S0 ∧
      IsCyclic YG.normalizerMonoidHom.range ∧
      Nat.card YG.normalizerMonoidHom.range = p-1 := by
  exact c.oddPrime_conclusions_of_model r.model r.cubic r.cubic_E r.cubic_L r.central
    hp Y P hodd a b ha hb hab hdecomp
    (fun t ht => r.centralizer_nonidentity t (hfour t ht).1 (hfour t ht).2)

end CFSG.Quasithin.ChapterJ.Centralizers.Choices

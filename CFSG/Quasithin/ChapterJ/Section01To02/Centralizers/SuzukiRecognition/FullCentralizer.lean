module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Identification
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.ModelConsequences
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Involutions
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# The full centralizer and four-group normalizer in J.2.9

The Sylow subgroup supplements the two-residual, so the local product gives
C_G(s) = S₀L_s. Pointwise Borel rigidity makes the factors commute, and
transfer makes their intersection trivial. Multiplication then supplies the
actual internal direct product, retaining both factor inclusions.

Conjugacy of S₀ minus the identity and equality of finite centralizer orders
show that all three centralizers coincide. The B-orbit then factors every
normalizer element as a member of C_G(s) times a member of B. Characteristicity
of the two-residual gives its normalization by the whole normalizer of S₀.

Source: Aschbacher–Smith, J.2.9, printed p.438 (PDF p.449).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalSetup G} (c : Choices d)

theorem Gs_eq_S0_sup_Ls_of_local_product
    (P : Sylow 2 c.Gs) (hP : (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs)
    (e : P ≃* c.S0 × c.S1)
    (he : ∀ x : P, ((x : c.Gs) : G) = ((e x).1 : G) * ((e x).2 : G)) :
    c.Gs = c.S0 ⊔ c.Ls := by
  have hTs : c.Ts = c.S0 ⊔ c.S1 := by
    apply le_antisymm
    · intro x hx
      let xG : c.Gs := ⟨x, (show c.Ts ≤ c.Gs from inf_le_right) hx⟩
      let xP : P := ⟨xG, by change xG ∈ (P : Subgroup c.Gs); rw [hP]; exact hx⟩
      have heq : x = ((e xP).1 : G) * ((e xP).2 : G) := he xP
      rw [heq]
      exact (c.S0 ⊔ c.S1).mul_mem ((show c.S0 ≤ c.S0 ⊔ c.S1 from le_sup_left) (e xP).1.property)
        ((show c.S1 ≤ c.S0 ⊔ c.S1 from le_sup_right) (e xP).2.property)
    · apply sup_le ?_ c.S1_le_Ts
      intro a ha
      obtain ⟨x, hx⟩ := e.surjective (⟨a,ha⟩,1)
      have heq := he x
      rw [hx] at heq
      simp only [OneMemClass.coe_one, mul_one] at heq
      rw [← heq]
      have hm := x.property
      have hm' : (x : c.Gs) ∈ c.Ts.subgroupOf c.Gs := hP ▸ hm
      exact hm'
  have hs := congrArg (map c.Gs.subtype) (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup, hP, map_subgroupOf_eq_of_le
    (show c.Ts ≤ c.Gs from inf_le_right), ← MonoidHom.range_eq_map, range_subtype] at hs
  change c.Ls ⊔ c.Ts = c.Gs at hs
  rw [← hs, hTs]
  rw [sup_left_comm, sup_eq_left.mpr c.S1_le_Ls]

theorem Gs_internalProduct_of_suzuki
    (P : Sylow 2 c.Gs) (hP : (P : Subgroup c.Gs) = c.Ts.subgroupOf c.Gs)
    (e : P ≃* c.S0 × c.S1)
    (he : ∀ x : P, ((x : c.Gs) : G) = ((e x).1 : G) * ((e x).2 : G))
    (model : c.Ls ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)
    (Q : Sylow 2 c.Ls) (hQ : (Q : Subgroup c.Ls) = c.S1.subgroupOf c.Ls)
    (hd : Disjoint c.S0 c.Ls) (hc : c.S0 ≤ centralizer (c.Ts : Set G)) :
    c.S0 ≤ centralizer (c.Ls : Set G) ∧
      ∃ f : c.S0 × c.Ls ≃* c.Gs,
        ∀ a l, (f (a,l) : G) = (a : G) * (l : G) := by
  have h := c.S0_centralizes_Ls_of_suzuki_model model Q hQ hc
  obtain ⟨f,hf⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting c.S0 c.Ls hd h
  exact ⟨h, f.trans (MulEquiv.subgroupCongr (c.Gs_eq_S0_sup_Ls_of_local_product P hP e he).symm), hf⟩

theorem centralizer_S0_nonidentity [IsElementaryAbelian 2 c.S0]
    (hGs : c.Gs = c.S0 ⊔ c.Ls)
    (hc : c.S0 ≤ centralizer (c.Ls : Set G))
    (hfused : ∀ t ∈ c.S0, t ≠ 1 → IsConj c.s t)
    {t : G} (ht : t ∈ c.S0) (ht1 : t ≠ 1) :
    centralizer ({t} : Set G) = c.Gs := by
  have hle : c.Gs ≤ centralizer ({t} : Set G) := by
    rw [hGs]
    exact sup_le ((le_centralizer c.S0).trans
      (centralizer_le (Set.singleton_subset_iff.mpr ht)))
      ((le_centralizer_iff.mp hc).trans
        (centralizer_le (Set.singleton_subset_iff.mpr ht)))
  obtain ⟨g,hg⟩ := isConj_iff.mp (hfused t ht ht1)
  have hm := Theory.GroupTheory.map_centralizer_singleton (MulAut.conj g) c.s
  change c.Gs.map (MulAut.conj g).toMonoidHom = centralizer ({g*c.s*g⁻¹} : Set G) at hm
  rw [hg] at hm
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [← hm, card_map_of_injective (MulAut.conj g).injective]

theorem normalizer_S0_factorization [IsElementaryAbelian 2 c.S0]
    (hGs : c.Gs = c.S0 ⊔ c.Ls)
    (hc : c.S0 ≤ centralizer (c.Ls : Set G))
    (hBN : c.B ≤ normalizer (c.S0 : Set G))
    (horbit : ∀ t ∈ c.S0, t ≠ 1 → ∃ b ∈ c.B, b * c.s * b⁻¹ = t) :
    c.Gs ⊔ c.B = normalizer (c.S0 : Set G) ∧
      normalizer (c.S0 : Set G) ≤ normalizer (c.Ls : Set G) ∧
      ∀ n ∈ normalizer (c.S0 : Set G), ∃ g ∈ c.Gs, ∃ b ∈ c.B, n = g*b := by
  have hfused : ∀ t ∈ c.S0, t ≠ 1 → IsConj c.s t := by
    intro t ht ht1
    obtain ⟨b,hb,he⟩ := horbit t ht ht1
    exact isConj_iff.mpr ⟨b,he⟩
  have hCN (n : G) (hn : n ∈ normalizer (c.S0 : Set G)) :
      c.Gs.map (MulAut.conj n).toMonoidHom = c.Gs := by
    have ht := (mem_normalizer_iff.mp hn c.s).mp c.s_mem
    have ht1 : n*c.s*n⁻¹ ≠ 1 := by
      intro he
      apply c.s_ne_one
      exact (MulAut.conj n).injective (he.trans (map_one _).symm)
    exact (Theory.GroupTheory.map_centralizer_singleton (MulAut.conj n) c.s).trans
      (c.centralizer_S0_nonidentity hGs hc hfused ht ht1)
  have hLN : normalizer (c.S0 : Set G) ≤ normalizer (c.Ls : Set G) := by
    intro n hn
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Theory.GroupTheory.centralizerTwoResidual c.s).map (MulAut.conj n).toMonoidHom = _
    rw [Theory.GroupTheory.map_centralizerTwoResidual]
    have he := (Theory.GroupTheory.map_centralizer_singleton (MulAut.conj n) c.s).symm.trans (hCN n hn)
    change (pResidual 2 (centralizer ({(MulAut.conj n) c.s} : Set G))).map _ = _
    rw [he]
  have hGN : c.Gs ≤ normalizer (c.S0 : Set G) := by
    rw [hGs]
    exact sup_le le_normalizer ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))
  have hfactor : ∀ n ∈ normalizer (c.S0 : Set G), ∃ g ∈ c.Gs, ∃ b ∈ c.B, n = g*b := by
    intro n hn
    have ht := (mem_normalizer_iff.mp hn c.s).mp c.s_mem
    have ht1 : n*c.s*n⁻¹ ≠ 1 := by
      intro he
      apply c.s_ne_one
      exact (MulAut.conj n).injective (he.trans (map_one _).symm)
    obtain ⟨b,hb,he⟩ := horbit _ ht ht1
    have hg : b⁻¹*n ∈ c.Gs := by
      apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      calc
        (b⁻¹*n)*c.s*(b⁻¹*n)⁻¹ = b⁻¹*(n*c.s*n⁻¹)*b := by group
        _ = c.s := by rw [← he]; group
    have hgb : b*(b⁻¹*n)*b⁻¹ ∈ c.Gs :=
      (mem_normalizer_iff_map_conj_eq.mpr (hCN b (hBN hb)) _).mp hg
    refine ⟨b*(b⁻¹*n)*b⁻¹,hgb,b,hb,?_⟩
    group
  refine ⟨le_antisymm (sup_le hGN hBN) ?_, hLN, hfactor⟩
  intro n hn
  obtain ⟨g,hg,b,hb,rfl⟩ := hfactor n hn
  exact (c.Gs ⊔ c.B).mul_mem ((show c.Gs ≤ c.Gs ⊔ c.B from le_sup_left) hg)
    ((show c.B ≤ c.Gs ⊔ c.B from le_sup_right) hb)

end CFSG.Quasithin.ChapterJ.Centralizers.Choices

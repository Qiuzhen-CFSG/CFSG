module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.FixedSpan
public import Theory.GroupTheory.IndexTwoConjugatePair
public import Theory.ElementaryAbelian.Join

/-!
# The commuting ambient pair and its normalizer

The index-two local Sylow subgroup has two cosets, so its invariant
subgroup U has T-span U+Uˢ. The actual product M=YT and Y-invariance
of U then make this pair M-invariant. Y-invariance itself follows from
the literal source product Y=Y_E Y_F O₂(Y).

Once U=V_E places it inside V_Mc, source 15.3.50 supplies commutation
with Uˢ. Thus Uˢ lies in the actual centralizer of V, and UUˢ is a
nontrivial elementary subgroup. No rank bound is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.50, 15.3.67 and the terminal argument, printed pp.1145,1153–1155.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
variable {G : Type*} [Group G]

/-- An index-two actor generates just the two conjugate subgroup factors. -/
theorem index_two_span_eq_pair (S T U : Subgroup G)
    (hi : (S.subgroupOf T).index = 2) (hSU : S ≤ normalizer (U : Set G))
    (s : G) (hs : s ∈ T) (hsS : s ∉ S) :
    conjugateSpanBy U T = U ⊔ U.map (MulAut.conj s).toMonoidHom := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨t,ht,u,hu,rfl⟩
    by_cases htS : t ∈ S
    · exact mem_sup_left ((mem_normalizer_iff.mp (hSU htS) u).mp hu)
    · have hd : s⁻¹*t ∈ S := by
        apply ((S.subgroupOf T).mul_mem_iff_of_index_two hi
          (a := (⟨s,hs⟩ : T)⁻¹) (b := ⟨t,ht⟩)).mpr
        change s⁻¹ ∈ S ↔ t ∈ S
        simp only [S.inv_mem_iff, hsS, htS]
      have hv := (mem_normalizer_iff.mp (hSU hd) u).mp hu
      apply mem_sup_right
      refine mem_map.mpr ⟨(s⁻¹*t)*u*(s⁻¹*t)⁻¹,hv,?_⟩
      change s * ((s⁻¹*t)*u*(s⁻¹*t)⁻¹) * s⁻¹ = t*u*t⁻¹
      group
  · refine sup_le (le_conjugateSpanBy U T) ?_
    rintro _ ⟨u,hu,rfl⟩
    exact subset_closure ⟨s,hs,u,hu,rfl⟩

/-- The source YT and index-two data give the ambient normalizer of UUˢ. -/
theorem pair_normalized_by_product (M Y S T U : Subgroup G)
    (hM : (M : Set G) = (Y : Set G) * (T : Set G))
    (hTY : T ≤ normalizer (Y : Set G))
    (hYU : Y ≤ normalizer (U : Set G)) (hSU : S ≤ normalizer (U : Set G))
    (hi : (S.subgroupOf T).index = 2) (s : G) (hs : s ∈ T) (hsS : s ∉ S) :
    M ≤ normalizer ((U ⊔ U.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
  have hYUs : Y ≤ normalizer (U.map (MulAut.conj s).toMonoidHom : Set G) :=
    normalizes_conjugate_of_normalizes (hTY hs) hYU
  have hYA := (le_inf hYU hYUs).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hTA : T ≤ normalizer ((U ⊔ U.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
    rw [← index_two_span_eq_pair S T U hi hSU s hs hsS]
    exact le_normalizer_conjugateSpanBy U T
  intro m hm
  have hm' : m ∈ (Y : Set G) * (T : Set G) := by rw [← hM]; exact hm
  obtain ⟨y,hy,t,ht,rfl⟩ := hm'
  exact (normalizer _).mul_mem (hYA hy) (hTA ht)

/-- Placement in the genuine abelian V_Mc supplies commutation, Uˢ≤C_G(V),
and a nontrivial elementary product. No rank bound is assumed. -/
theorem ambient_pair_in_local_span (V Mc U : Subgroup G)
    [IsElementaryAbelian 2 U] [IsMulCommutative (conjugateSpanBy V Mc)]
    (hVU : V ≤ U) (hV : V ≠ ⊥) (hU : U ≤ conjugateSpanBy V Mc)
    (s : G) (hs : s ∈ Mc) :
    let Us := U.map (MulAut.conj s).toMonoidHom
    Us ≤ conjugateSpanBy V Mc ∧ Us ≤ centralizer (V : Set G) ∧
      ⁅Us,U⁆ = ⊥ ∧ IsElementaryAbelian 2 (U ⊔ Us : Subgroup G) ∧ U ⊔ Us ≠ ⊥ := by
  let Us := U.map (MulAut.conj s).toMonoidHom
  have hUs : Us ≤ conjugateSpanBy V Mc := by
    rintro _ ⟨u,hu,rfl⟩
    exact (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V Mc hs) u).mp (hU hu)
  have hC : Us ≤ centralizer (U : Set G) :=
    hUs.trans ((conjugateSpanBy V Mc).le_centralizer.trans (centralizer_le hU))
  let : IsElementaryAbelian 2 Us := IsElementaryAbelian.map (MulAut.conj s).toMonoidHom
  exact ⟨hUs,hC.trans (centralizer_le hVU),commutator_eq_bot_iff_le_centralizer.mpr hC,
    IsElementaryAbelian.sup_of_le_centralizer hC,
    fun he => hV (bot_unique (hVU.trans (le_sup_left.trans he.le)))⟩

/-- The literal source product Y=Y_E Y_F O₂(Y) normalizes U. -/
theorem terminal_Y_normalizes_span [Finite G]
    (T : Sylow 2 G) (M Y V E F : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d)
    (hYM : Y ≤ M)
    (hYcore : twoCoreAmbient Y = Y ⊓ centralizer (V : Set G))
    (hRH : centralizer (V : Set G) ≤ amalgamGroup Y T E F) :
    Y ≤ normalizer (conjugateSpanBy V (amalgamGroup Y T E F) : Set G) := by
  let H := amalgamGroup Y T E F
  let U := conjugateSpanBy V H
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy V H
  have hBU := external_normalizes_span H (lineY Y E) V c.normalizes_lineY
    ((lineY_le Y E).trans (inf_le_left.trans (hYM.trans d.normalizes)))
  have hFY : lineY Y F ≤ H := le_sup_left.trans le_sup_left
  have h0H : twoCoreAmbient Y ≤ H := hYcore.le.trans (inf_le_right.trans hRH)
  intro y hy
  have hy' : y ∈ (lineY Y E : Set G) * (lineY Y F : Set G) * (twoCoreAmbient Y : Set G) := by
    rw [← c.product_Y]; exact hy
  obtain ⟨_,⟨b,hb,f,hf,rfl⟩,a,ha,rfl⟩ := hy'
  exact (normalizer _).mul_mem ((normalizer _).mul_mem (hBU hb) (hHU (hFY hf))) (hHU (h0H ha))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear

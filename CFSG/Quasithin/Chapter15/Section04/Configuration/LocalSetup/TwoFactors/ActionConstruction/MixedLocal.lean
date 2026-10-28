module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.MixedLocal.Setup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.MixedLocal.Quotients

/-!
# Construction of the mixed local configuration

From the raw preceding witnesses and the realized factor action, construct
`T_I=N_T(Y₂)`, `G_i=Y_i T_I`, `I=⟨G₁,G₂⟩`, and
`E₀=C_E(Y₁)∩C_E(Y₂)`. The fixed-space calculation gives `|E|=8`,
`E₀≠1`, and `E₀≤T_I≤I≤C_G(E₀)`.

The action on two factors identifies the normal stabilizer and proves its
index two. Since `E₀` centralizes exactly one factor, its local centralizer
lies in the stabilizer. Sylow restriction constructs the actual local Sylow
image; Baumann control then promotes it to `C_G(E₀)` and `I`.
The order-three factor quotients and Thompson commutator identities give
both actual symmetric-three quotients. Relative normality of the first
local group and the distinct unique overgroups separate the two-core images;
the common index-three calculation proves `G₁∩G₂=T_I`.

The resulting SQTK Goldschmidt triple is the input to the subsequent
amalgam and generalized-Fitting analysis. `RealizedFactors` lists the raw
inputs whose realization remains with the parent; no classification branch
or additional mixed-configuration conclusion is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, the first three paragraphs of 15.4.18, printed p.1162.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.MixedLocal
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The constructed mixed configuration, before either generalized-Fitting
branch. Every subgroup is fixed by the displayed source definitions. -/
structure Configuration (K : GroupClass) (T : Sylow 2 G) (Y X M : Subgroup G)
    (L : Bool → Subgroup G) : Prop where
  index_stabilizer : (stabilizer T L).relIndex (T : Subgroup G) = 2
  normalizes_stabilizer : (T : Subgroup G) ≤ normalizer (stabilizer T L : Set G)
  normalizes_first : Y ⊔ (T : Subgroup G) ≤ normalizer (firstGroup T Y L : Set G)
  normalizes_factor : stabilizer T L ≤ normalizer (L true : Set G)
  centralizes_omega : stabilizer T L ≤ centralizer (omega T : Set G)
  omega_card : Nat.card (omega T) = 8
  fixed_X_card : Nat.card (fixed (omega T) X) = 2
  fixed_disjoint : fixed (omega T) Y ⊓ fixed (omega T) X = ⊥
  first_sylow : ∃ P : Sylow 2 (firstGroup T Y L),
    (P : Subgroup (firstGroup T Y L)).map (firstGroup T Y L).subtype = stabilizer T L
  second_sylow : ∃ P : Sylow 2 (secondGroup T L),
    (P : Subgroup (secondGroup T L)).map (secondGroup T L).subtype = stabilizer T L
  common_ne_bot : commonFixed T Y L ≠ ⊥
  common_le_stabilizer : commonFixed T Y L ≤ stabilizer T L
  common_le_generated : commonFixed T Y L ≤ generated T Y L
  generated_centralizes : generated T Y L ≤ centralizer (commonFixed T Y L : Set G)
  local_sylow : ∃ P : Sylow 2 (M ⊓ centralizer (commonFixed T Y L : Set G) : Subgroup G),
    (P : Subgroup (M ⊓ centralizer (commonFixed T Y L : Set G) : Subgroup G)).map
      (M ⊓ centralizer (commonFixed T Y L : Set G) : Subgroup G).subtype = stabilizer T L
  centralizer_sylow : ∃ P : Sylow 2 (centralizer (commonFixed T Y L : Set G)),
    (P : Subgroup (centralizer (commonFixed T Y L : Set G))).map
      (centralizer (commonFixed T Y L : Set G)).subtype = stabilizer T L
  sylow_intersection : (T : Subgroup G) ⊓ centralizer (commonFixed T Y L : Set G) = stabilizer T L
  generated_sylow : ∃ P : Sylow 2 (generated T Y L),
    (P : Subgroup (generated T Y L)).map (generated T Y L).subtype = stabilizer T L
  sqtk : IsSQTK K (generated T Y L)
  first_index : (stabilizer T L).relIndex (firstGroup T Y L) = 3
  second_index : (stabilizer T L).relIndex (secondGroup T L) = 3
  first_quotient : Nonempty (((firstGroup T Y L) ⧸ pCore 2 (firstGroup T Y L)) ≃* Equiv.Perm (Fin 3))
  second_quotient : Nonempty (((secondGroup T L) ⧸ pCore 2 (secondGroup T L)) ≃* Equiv.Perm (Fin 3))
  intersection : firstGroup T Y L ⊓ secondGroup T L = stabilizer T L
  different_cores : (firstGroup T Y L).pCoreIn 2 ≠ (secondGroup T L).pCoreIn 2
  goldschmidt : ChapterF.IsGoldschmidtTriple
    ((firstGroup T Y L).subgroupOf (generated T Y L))
    ((secondGroup T L).subgroupOf (generated T Y L))

/-- Construct the mixed stabilizer, fixed geometry, Sylow witnesses, symmetric
quotients and Goldschmidt triple from the realized factors. The only global
normalizer input is the universal implication of 15.4.16. -/
theorem construct {K : GroupClass} (hG : IsSimpleQTKE K G) (T : Sylow 2 G)
    {Y X M₁ M₂ : Subgroup G} {L : Bool → Subgroup G}
    (d : RealizedFactors T Y X M₁ M₂ L)
    (h16 : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      normalizer (baum T : Set G) ≤ M) : Configuration K T Y X M₂ L := by
  let : IsElementaryAbelian 2 (omega T) := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    d.sylow_le₁.trans d.normalizer₁.le
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    d.sylow_le₂.trans d.normalizer₂.le
  have hTE : (T : Subgroup G) ≤ normalizer (omega T : Set G) := normalizes_alpha _
  have hSU : baum T ≤ stabilizer T L := le_inf inf_le_left d.baumann_invariant
  have hEU : omega T ≤ stabilizer T L := (alpha_le_baumann _).trans hSU
  have hBE : commonFixed T Y L ≤ omega T := inf_le_left.trans inf_le_left
  have hBU : commonFixed T Y L ≤ stabilizer T L := hBE.trans hEU
  have hUI : stabilizer T L ≤ generated T Y L := le_sup_right.trans le_sup_left
  have hBI : commonFixed T Y L ≤ generated T Y L := hBU.trans hUI
  have hswap : (L false).map (MulAut.conj d.swapper).toMonoidHom = L true := by
    have he := d.pairAction.conjugation ⟨d.swapper, d.sylow_le₂ d.swapper_mem⟩ false
    cases hp : d.pairAction.permutation ⟨d.swapper, d.sylow_le₂ d.swapper_mem⟩ false with
    | false =>
      have hn := mem_normalizer_iff_map_conj_eq.mpr (he.trans (congrArg L hp))
      exact (d.swapper_moves hn).elim
    | true => exact he.trans (congrArg L hp)
  have hline : (movedLine (omega T) (L false)).map (MulAut.conj d.swapper).toMonoidHom =
      movedLine (omega T) (L true) := map_movedLine (hTE d.swapper_mem) hswap
  have hcard' : Nat.card (movedLine (omega T) (L true)) = 2 := by
    rw [← hline, card_map_of_injective (MulAut.conj d.swapper).injective]
    exact d.single_card₂
  have hcomm : movedLine (omega T) (L false) ≤
      centralizer (movedLine (omega T) (L true) : Set G) := by
    intro f hf g hg
    exact setLike_mul_comm (show g ∈ omega T from hg.2) (show f ∈ omega T from hf.2)
  have hcardX : Nat.card (movedLine (omega T) (L false) ⊔
      movedLine (omega T) (L true) : Subgroup G) = 4 := by
    obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
      (movedLine (omega T) (L false)) (movedLine (omega T) (L true)) d.lines_disjoint hcomm
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, d.single_card₂, hcard']
  obtain ⟨hdis, hEX, hEcard, _, _, hBne⟩ := fixed_geometry T rfl hTY hTX
    d.unique₁ d.unique₂ d.different d.single_split₁ d.single_disjoint₁ d.single_card₁
    d.single_split₂ d.single_disjoint₂ d.single_card₂ d.double_split d.double_disjoint hcardX
    d.central_fixed_card
  have hUL' : stabilizer T L ≤ normalizer (L true : Set G) := by
    intro u hu
    have hk : (⟨u, d.sylow_le₂ hu.1⟩ : M₂) ∈ d.pairAction.permutation.ker := by
      rw [d.pairAction.kernel]
      exact hu.2
    have he := d.pairAction.conjugation ⟨u, d.sylow_le₂ hu.1⟩ true
    have hp : d.pairAction.permutation ⟨u, d.sylow_le₂ hu.1⟩ = 1 := hk
    rw [hp] at he
    exact mem_normalizer_iff_map_conj_eq.mpr he
  have hUE : stabilizer T L ≤ normalizer (omega T : Set G) := inf_le_left.trans hTE
  have hUEX : stabilizer T L ≤ normalizer (fixed (omega T) X : Set G) :=
    (le_inf hUE (inf_le_left.trans (hTX.trans (normalizer_le_normalizer_centralizer X)))).trans
      inf_normalizer_le_normalizer_inf
  have hUCE : stabilizer T L ≤ centralizer (omega T : Set G) :=
    centralizes_of_three_fixed_lines d.double_split hEX d.single_card₂ hcard' hUEX
      (normalizes_movedLine hUE inf_le_right) (normalizes_movedLine hUE hUL')
  have hIC : generated T Y L ≤ centralizer (commonFixed T Y L : Set G) :=
    mixed_join_centralizes hUCE
  have hUC : stabilizer T L ≤ centralizer (commonFixed T Y L : Set G) :=
    hUCE.trans (centralizer_le hBE)
  have hnot := common_fixed_not_centralizes_partner d.product hdis hBne
  obtain ⟨P, hP⟩ := local_sylow_of_pair_action T d.pairAction d.sylow_le₂
    (inf_le_right.trans inf_le_right) hnot hUC
  obtain ⟨S, hS, hTC⟩ := sylow_centralizer_of_baumann_control T inf_le_left hSU hUC
    P hP d.maximal₂ d.sylow_le₂ h16
  have hSI : (S : Subgroup (centralizer (commonFixed T Y L : Set G))).map
      (centralizer (commonFixed T Y L : Set G)).subtype ≤ generated T Y L := hS.le.trans hUI
  let Q : Sylow 2 (generated T Y L) := restrictSylow S hIC hSI
  have hQ : (Q : Subgroup (generated T Y L)).map (generated T Y L).subtype = stabilizer T L :=
    (restrictSylow_image S hIC hSI).trans hS
  have hBp : IsPGroup 2 (commonFixed T Y L) := T.isPGroup'.to_le (hBU.trans inf_le_left)
  have hSQTK := (sqtk_of_nontrivial_normal_two_subgroup hG hBp hBne hBI
    (hIC.trans (Subgroup.centralizer_le_normalizer _))).2
  have hU : IsPGroup 2 (stabilizer T L) := T.isPGroup'.to_le inf_le_left
  obtain ⟨hi₁, hSyl₁, hq₁⟩ := factor_join_symmetric_quotient hU hSU (thompson_le_baumann _)
    (inf_le_left.trans hTY) d.thompson_commutator₁ d.factor_core_index₁
    d.earlierSylow₁ d.earlierSylow₁_image
  have hY₂X : L false ≤ X := d.product ▸ le_sup_left
  have hYS : L false ⊔ baum T ≤ X ⊔ baum T := sup_le_sup hY₂X le_rfl
  have hPX : (d.earlierSylowX : Subgroup (X ⊔ baum T : Subgroup G)).map
      (X ⊔ baum T : Subgroup G).subtype ≤ L false ⊔ baum T :=
    d.earlierSylowX_image.le.trans le_sup_right
  let P₂ : Sylow 2 (L false ⊔ baum T : Subgroup G) := restrictSylow d.earlierSylowX hYS hPX
  have hP₂ : (P₂ : Subgroup (L false ⊔ baum T : Subgroup G)).map
      (L false ⊔ baum T : Subgroup G).subtype = baum T :=
    (restrictSylow_image d.earlierSylowX hYS hPX).trans d.earlierSylowX_image
  obtain ⟨hi₂, hSyl₂, hq₂⟩ := factor_join_symmetric_quotient hU hSU (thompson_le_baumann _)
    inf_le_right d.thompson_commutator₂ d.factor_core_index₂ P₂ hP₂
  have hnG₁ := firstGroup_normalized d.pairAction d.sylow_le₂ hTY
  have hncore : Y ⊔ (T : Subgroup G) ≤ normalizer ((firstGroup T Y L).pCoreIn 2 : Set G) :=
    hnG₁.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (firstGroup T Y L)))
  have hc₁ : (firstGroup T Y L).pCoreIn 2 ≠ ⊥ := by
    intro hb
    apply hBne
    apply le_bot_iff.mp
    have hle := le_pCoreIn_of_normalizes hBp (hBU.trans le_sup_right)
      ((le_sup_left.trans hIC).trans (Subgroup.centralizer_le_normalizer _))
    exact hle.trans hb.le
  have hgen := pair_join_eq_of_swap d.product d.swapper_mem hswap
  have hcores := mixed_twoCores_ne hgen d.unique₁ d.unique₂ d.different hc₁ hncore
  have hgroups : firstGroup T Y L ≠ secondGroup T L := by
    intro he
    exact hcores (congrArg (fun A : Subgroup G => A.pCoreIn 2) he)
  have hint := intersection_of_common_index_three le_sup_right le_sup_right hi₁ hi₂ hgroups
  exact {
    index_stabilizer := (d.pairAction.restrict d.sylow_le₂).stabilizer_index
      d.swapper_mem d.swapper_moves
    normalizes_stabilizer := (d.pairAction.restrict d.sylow_le₂).normalizes_stabilizer
    normalizes_first := hnG₁
    normalizes_factor := hUL'
    centralizes_omega := hUCE
    omega_card := hEcard
    fixed_X_card := hEX
    fixed_disjoint := hdis
    first_sylow := hSyl₁
    second_sylow := hSyl₂
    common_ne_bot := hBne
    common_le_stabilizer := hBU
    common_le_generated := hBI
    generated_centralizes := hIC
    local_sylow := ⟨P, hP⟩
    centralizer_sylow := ⟨S, hS⟩
    sylow_intersection := hTC
    generated_sylow := ⟨Q, hQ⟩
    sqtk := hSQTK
    first_index := hi₁
    second_index := hi₂
    first_quotient := hq₁
    second_quotient := hq₂
    intersection := hint
    different_cores := hcores
    goldschmidt := goldschmidt_triple_in_join _ _ _ hq₁ hq₂ Q hQ hint }

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.MixedLocal

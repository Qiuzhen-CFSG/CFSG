module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.SetupSource
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CentralizingCore
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PrimeRankElementary
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Solvable
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# The actual component in the double linear branch

The natural elementary module of a rank-one block survives any central
kernel, retaining two-rank at least twice the field degree. Consequently
an index-two local block centralizing the ambient two-core lies in an
ordinary quasisimple component. If its two-conjugate span is normal,
component commutation identifies that span with the selected component.
The final theorem applies this argument to the literal double-source
carriers, without imposing an abstract component or model hypothesis.

Source: Aschbacher–Smith, 2.4.7, double-block conclusion, printed p.541,
using 1.2.5 and 1.2.1(5).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.LinearShadows.Double
variable {G : Type*} [Group G] [Finite G]

/-- A central kernel preserves the rank of the natural elementary module. -/
theorem natural_block_image_two_rank {L Y : Type*} [Group L] [Finite L]
    [Group Y] [Finite Y] {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (f : L →* Y) (hk : f.ker ≤ center L) : n * 2 ≤ primeRank 2 Y := by
  let U := ChapterC.blockU L
  let g := f.comp U.subtype
  have hker : g.ker ≤ ChapterC.blockFixed L := by
    intro u hu
    exact hk hu
  let q := QuotientGroup.map g.ker (ChapterC.blockFixed L) (MonoidHom.id U) hker
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (ChapterC.blockFixed L) a
    exact ⟨QuotientGroup.mk' g.ker u,rfl⟩
  have hc : 2 ^ (n*2) ≤ Nat.card g.range := by
    rw [← hL.module_card]
    exact (Nat.card_le_card_of_surjective q hq).trans_eq
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv)
  let : IsElementaryAbelian 2 U := hL.2.1.elementary
  let : IsElementaryAbelian 2 g.range := IsElementaryAbelian.of_surjective
    g.rangeRestrict g.rangeRestrict_surjective
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (hc.trans ((primeRank_le_iff_elementary_card_le Y).mp le_rfl g.range inferInstance))

/-- The actual index-two local block yields a quasisimple component; its
natural elementary module survives the central ambient two-core. -/
theorem quasisimple_component_of_index_two
    {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X))
    (P : Sylow 2 X) (B L : Subgroup X) {n : ℕ}
    (hBP : B ≤ P) (hindex : B.relIndex (P : Subgroup X) ≤ 2)
    (hlocal : L ∈ Chapter1.L X B) (hnatural : ChapterC.IsL2EvenBlock L n)
    (hcentral : L ≤ centralizer (pCore 2 X : Set X)) :
    ∃ K : Subgroup X, Theory.GroupTheory.IsComponent X K ∧ L ≤ K ∧
      K ≤ centralizer (pCore 2 X : Set X) ∧
      n*2 ≤ primeRank 2 (K.map (QuotientGroup.mk' (pCore 2 X))) := by
  obtain ⟨K,⟨hK,hLK⟩,_⟩ := Chapter1.Section02.index_le_two_local_component_source
    hX P hBP hindex hlocal
  have hc := ChapterA.Section03.NoncentralFitting.component_centralizes_of_nonsolvable_subgroup
    K L (pCore 2 X) hK hLK (by intro hs; let := hs; exact hnatural.not_solvable) hcentral
  let q := QuotientGroup.mk' (pCore 2 X)
  let f := (q.subgroupMap K).comp (inclusion hLK)
  have hk : f.ker ≤ center L := by
    intro l hl
    have hlQ : (l:X) ∈ pCore 2 X := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val hl)
    apply mem_center_iff.mpr
    intro a
    exact Subtype.ext ((mem_centralizer_iff.mp (hcentral a.property)) l hlQ).symm
  have hr := natural_block_image_two_rank hnatural f hk
  have hquasi := ChapterA.Section03.NoncentralFitting.quasisimple_of_core_centralizes_and_image_rank
    hX K hK (le_centralizer_iff.mp hc) ((by have := hnatural.1; omega : 2≤n*2).trans hr)
  exact ⟨K,⟨hK.subnormal,hquasi⟩,hLK,hc,hr⟩

/-- A natural block has a noncentral two-core and hence is not quasisimple. -/
theorem natural_block_not_quasisimple {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n) : ¬ IsQuasisimple L := by
  intro hq
  let := hq
  apply hL.2.1.blockU_ne_bot
  exact commutator_top_right_eq_bot_iff_le_center.mpr (IsQuasisimple.pCore_le_center 2)

private theorem component_eq_normal_pair
    (L K E : Subgroup G) (x : G) [K.Normal] [Group.IsPerfect L]
    (hE : IsComponent G E) (hLE : L ≤ E)
    (hgen : K = L ⊔ L.map (MulAut.conj x).toMonoidHom)
    (hnonsolvable : ¬ Group.IsSolvable L) (hnotquasi : ¬ IsQuasisimple L) : K = E := by
  have hLK : L ≤ K := by rw [hgen]; exact le_sup_left
  have hne : L ≠ ⊥ := by
    intro he
    subst L
    exact hnonsolvable inferInstance
  have hEK : E ≤ K := by
    rcases hE.normal_dichotomy K with he | hc
    · exact he
    · have hcL : ⁅L,L⁆ = ⊥ := bot_unique ((commutator_mono hLE hLK).trans hc.le)
      rw [Subgroup.isPerfect_iff.mp (inferInstance : Group.IsPerfect L)] at hcL
      exact (hne hcL).elim
  by_cases he : E.map (MulAut.conj x).toMonoidHom = E
  · exact le_antisymm (by rw [hgen]; exact sup_le hLE ((map_mono hLE).trans_eq he)) hEK
  · have hc : L.map (MulAut.conj x).toMonoidHom ≤ centralizer (L : Set G) :=
      (map_mono hLE).trans ((commutator_eq_bot_iff_le_centralizer.mp
        ((hE.map_conj x).commutator_eq_bot_of_ne hE he)).trans (centralizer_le hLE))
    have hn : K ≤ normalizer (L : Set G) := by
      rw [hgen]
      exact sup_le L.le_normalizer (hc.trans (Subgroup.centralizer_le_normalizer _))
    have hnormal := normal_subgroupOf_of_le_normalizer hn
    have hsub : L.IsSubnormal := by
      have hs := hnormal.isSubnormal.trans' (inferInstance : K.Normal).isSubnormal
      rwa [map_subgroupOf_eq_of_le hLK] at hs
    have hEq : L = E := le_antisymm hLE
      (hE.isCComponent.minimal L hLE hne inferInstance hsub)
    exact (hnotquasi (hEq.symm ▸ hE.2)).elim

/-- Normality of the literal two-conjugate span identifies the selected
component, before any inspection of the model catalogue. -/
theorem normal_pair_isComponent_of_index_two
    (hG : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    (P : Sylow 2 G) (B L K : Subgroup G) (x : G) {n : ℕ} [K.Normal]
    (hBP : B ≤ P) (hindex : B.relIndex (P : Subgroup G) ≤ 2)
    (hlocal : L ∈ Chapter1.L G B) (hnatural : ChapterC.IsL2EvenBlock L n)
    (hcentral : L ≤ centralizer (pCore 2 G : Set G))
    (hgen : K = L ⊔ L.map (MulAut.conj x).toMonoidHom) : IsComponent G K := by
  obtain ⟨E,hE,hLE,_,_⟩ := quasisimple_component_of_index_two hG P B L
    hBP hindex hlocal hnatural hcentral
  let := Chapter1.mem_L_isPerfect hlocal
  have he := component_eq_normal_pair L K E x hE hLE hgen
    (by intro hs; let := hs; exact hnatural.not_solvable) (natural_block_not_quasisimple hnatural)
  exact he.symm ▸ hE

/-- The component conclusion on the exact double-source carrier
`K = L₂ ⊔ L₂^(x⁻¹)` inside `X = K ⊔ S₁`. -/
theorem source_pair_component
    {M M₀ : Subgroup G} (d : MinimalBlockSetup M) {n : ℕ}
    (c : DoubleLinearSourceSetup d M₀ n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (x : G) (B S₁ R₁ : Subgroup G) (hx : x ∈ S₁) (hBS : B ≤ S₁)
    (hindex : B.relIndex S₁ = 2) (hR : R₁ ≠ ⊥) :
    let K := c.second ⊔ c.second.map (MulAut.conj x⁻¹).toMonoidHom
    let X := K ⊔ S₁
    twoCore X = R₁ → K ≤ centralizer (R₁ : Set G) →
      (∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = S₁) →
      c.second.subgroupOf X ∈ Chapter1.L X (B.subgroupOf X) →
      (K.subgroupOf X).Normal → IsComponent X (K.subgroupOf X) := by
  dsimp only
  let K := c.second ⊔ c.second.map (MulAut.conj x⁻¹).toMonoidHom
  let X := K ⊔ S₁
  change twoCore X = R₁ → K ≤ centralizer (R₁ : Set G) → _
  intro hcore hcentral hSylow hlocal hnormal
  obtain ⟨P,hP⟩ := hSylow
  have hKX : K ≤ X := le_sup_left
  have hLX : c.second ≤ X := le_sup_left.trans hKX
  have hSX : S₁ ≤ X := le_sup_right
  have hPin : (P : Subgroup X) = S₁.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSX]
  have hBP : B.subgroupOf X ≤ P := by
    rw [hPin]
    exact subgroupOf_mono X hBS
  have hi : (B.subgroupOf X).relIndex (P : Subgroup X) ≤ 2 := by
    rw [hPin,relIndex_subgroupOf hSX,hindex]
  have hc : c.second.subgroupOf X ≤ centralizer (pCore 2 X : Set X) := by
    intro l hl u hu
    apply Subtype.ext
    exact hcentral ((show c.second ≤ K from le_sup_left) hl) u (hcore ▸ mem_map_of_mem X.subtype hu)
  let xX : X := ⟨x⁻¹,X.inv_mem (hSX hx)⟩
  have hgen : K.subgroupOf X = c.second.subgroupOf X ⊔
      (c.second.subgroupOf X).map (MulAut.conj xX).toMonoidHom := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hKX,Subgroup.map_sup,
      map_subgroupOf_eq_of_le hLX,map_map]
    have he : X.subtype.comp (MulAut.conj xX).toMonoidHom =
        (MulAut.conj x⁻¹).toMonoidHom.comp X.subtype := rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hLX]
  let := hnormal
  exact normal_pair_isComponent_of_index_two
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG (by change twoCore X ≠ ⊥; rwa [hcore]))
    P (B.subgroupOf X) (c.second.subgroupOf X) (K.subgroupOf X) xX hBP hi hlocal
    (c.second_type.of_mulEquiv (subgroupOfEquivOfLe hLX).symm) hc hgen

/-- The same literal component conclusion requires only centralization of the
actual ambient two-core; no identification of that core is needed. -/
theorem source_pair_component_of_core_centralized
    {M M₀ : Subgroup G} (d : MinimalBlockSetup M) {n : ℕ}
    (c : DoubleLinearSourceSetup d M₀ n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (x : G) (B S₁ : Subgroup G) (hx : x ∈ S₁) (hBS : B ≤ S₁)
    (hindex : B.relIndex S₁ = 2) :
    let K := c.second ⊔ c.second.map (MulAut.conj x⁻¹).toMonoidHom
    let X := K ⊔ S₁
    twoCore X ≠ ⊥ → c.second ≤ centralizer (twoCore X : Set G) →
      (∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = S₁) →
      c.second.subgroupOf X ∈ Chapter1.L X (B.subgroupOf X) →
      (K.subgroupOf X).Normal → IsComponent X (K.subgroupOf X) := by
  dsimp only
  let K := c.second ⊔ c.second.map (MulAut.conj x⁻¹).toMonoidHom
  let X := K ⊔ S₁
  change twoCore X ≠ ⊥ → c.second ≤ centralizer (twoCore X : Set G) → _
  intro hcore hcentral hSylow hlocal hnormal
  obtain ⟨P,hP⟩ := hSylow
  have hKX : K ≤ X := le_sup_left
  have hLX : c.second ≤ X := le_sup_left.trans hKX
  have hSX : S₁ ≤ X := le_sup_right
  have hPin : (P : Subgroup X) = S₁.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSX]
  have hBP : B.subgroupOf X ≤ P := by
    rw [hPin]
    exact subgroupOf_mono X hBS
  have hi : (B.subgroupOf X).relIndex (P : Subgroup X) ≤ 2 := by
    rw [hPin,relIndex_subgroupOf hSX,hindex]
  have hc : c.second.subgroupOf X ≤ centralizer (pCore 2 X : Set X) := by
    intro l hl u hu
    apply Subtype.ext
    exact hcentral hl u (mem_map_of_mem X.subtype hu)
  let xX : X := ⟨x⁻¹,X.inv_mem (hSX hx)⟩
  have hgen : K.subgroupOf X = c.second.subgroupOf X ⊔
      (c.second.subgroupOf X).map (MulAut.conj xX).toMonoidHom := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hKX,Subgroup.map_sup,
      map_subgroupOf_eq_of_le hLX,map_map]
    have he : X.subtype.comp (MulAut.conj xX).toMonoidHom =
        (MulAut.conj x⁻¹).toMonoidHom.comp X.subtype := rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hLX]
  let := hnormal
  exact normal_pair_isComponent_of_index_two
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG (by change twoCore X ≠ ⊥; exact hcore))
    P (B.subgroupOf X) (c.second.subgroupOf X) (K.subgroupOf X) xX hBP hi hlocal
    (c.second_type.of_mulEquiv (subgroupOfEquivOfLe hLX).symm) hc hgen
end CFSG.Quasithin.Chapter2.LinearShadows.Double

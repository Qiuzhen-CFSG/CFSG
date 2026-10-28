module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.RawQuotient
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.KernelCoordinates
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Residuals
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.FactorRecognition
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Splitting
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Components
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Invariance
public import Theory.GroupTheory.NormalClosureCentralizerCore

/-!
# Local structure from the selected A₆/S₆ case

Start with the realized mixed factors and the genuine configuration constructed
from them, the source two-perfectness of Y₁ and Y₂, and the selected actual
component L ≃ A₆ and subgroup L*Z* ≃ S₆. The faithful action of Z on L is
exactly the applicable 1.1.5 conclusion; |Z| = 4 is the earlier 15.4.14 fact.
No later local identification, factor containment or centralizer index is assumed.

Whole-quotient coverage and faithful component coordinates first identify
I/O_{3′}(I) with S₆. The local calculations then give Yᵢ ≤ L and
L = O^{3′}(I) = O²(I) = ⟨Y₁,Y₂⟩. Transport along the actual inclusion I → G
supplies both centralizer indices in the ambient group. Applying the proved
index-two invariance argument gives C_{T_I}(L) = E₀ of order two, discharging
the final premise of the splitting theorem. The original factors are A₄,
and the original local groups are E₄ × S₄ with complements Gᵢ ∩ L.

The ambient centralizer product uses C_Z(Y₁). Its multiplication map is
constructed from the fixed planes in the order-eight Thompson omega subgroup.
The printed Z ∩ L fails the independent S₆ model calculation recorded in
`ComponentLocals.printed_factor_obstruction`; no such false model identity is
used. The corrected product gives precisely the index required by invariance.
Model selection and the terminal component-branch rank contradiction remain
with the parent; all local-coordinate and recognition premises are discharged here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of 15.4.18, printed pp.1162–1163.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Mixed
open MixedLocal
variable {G : Type*} [Group G] [Finite G]

/-- Construct the compatible coordinates from the selected component and the
actual selected star subgroup, using whole-quotient coverage first. -/
noncomputable def quotientCoordinates
    {K : GroupClass} (T : Sylow 2 G) {Y X M₁ M₂ : Subgroup G}
    {F : Bool → Subgroup G} (d : RealizedFactors T Y X M₁ M₂ F)
    (c : Configuration K T Y X M₂ F)
    (L : Subgroup (generated T Y F))
    (hL : Theory.GroupTheory.IsComponent (generated T Y F) L)
    (eL : L ≃* alternatingGroup (Fin 6))
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hfaithful : RawQuotient.mixedZ T Y F ⊓
      centralizer (L : Set (generated T Y F)) = ⊥)
    (eSelected : RawQuotient.selectedJoin L (RawQuotient.mixedZ T Y F) ≃*
      Equiv.Perm (Fin 6)) : QuotientCoordinates L :=
  KernelCoordinates.ofGoldschmidtTriple c.goldschmidt hL eL
    (Classical.choice (RawQuotient.whole_star_quotient_of_mixed T d c L hL eL hZ
      hfaithful eSelected))

omit [Finite G] in
private theorem sylow_eq_subgroupOf {J U : Subgroup G} (S : Sylow 2 J)
    (hS : (S : Subgroup J).map J.subtype = U) :
    (S : Subgroup J) = U.subgroupOf J := by
  rw [← hS, Subgroup.subgroupOf, comap_map_eq, J.ker_subtype, sup_bot_eq]

omit [Finite G] in
private theorem local_inputs {J U A : Subgroup G} (S : Sylow 2 J)
    (hS : (S : Subgroup J).map J.subtype = U) (hAJ : A ≤ J)
    (hp : IsPPerfect 2 A) (hn : U ≤ normalizer (A : Set G))
    (hi : U.relIndex (A ⊔ U) = 3) :
    IsPPerfect 2 (A.subgroupOf J) ∧
      (S : Subgroup J) ≤ normalizer (A.subgroupOf J : Set J) ∧
      (S : Subgroup J).relIndex (A.subgroupOf J ⊔ (S : Subgroup J)) = 3 := by
  have hp' := hp.of_surjective (subgroupOfEquivOfLe hAJ).symm.toMonoidHom
    (subgroupOfEquivOfLe hAJ).symm.surjective
  refine ⟨hp', ?_, ?_⟩
  · rw [← subgroupOf_normalizer_eq hAJ, sylow_eq_subgroupOf S hS]
    exact comap_mono hn
  · rw [← relIndex_map_map_of_injective _ _ J.subtype_injective,
      Subgroup.map_sup, hS, map_subgroupOf_eq_of_le hAJ]
    exact hi

omit [Finite G] in
private theorem centralizer_image {J U : Subgroup G} (S : Sylow 2 J)
    (hS : (S : Subgroup J).map J.subtype = U) (A : Subgroup J) :
    ((S : Subgroup J) ⊓ centralizer (A : Set J)).map J.subtype =
      U ⊓ centralizer (A.map J.subtype : Set G) := by
  rw [Subgroup.map_inf _ _ _ J.subtype_injective, hS, map_centralizer_subtype]
  have hUJ : U ≤ J := hS ▸ map_subtype_le (S : Subgroup J)
  rw [← inf_assoc, inf_eq_left.mpr hUJ]

/-- The component contains the original factors in the ambient group. -/
theorem factor_containment {K : GroupClass} (T : Sylow 2 G)
    {Y X M₁ M₂ : Subgroup G} {F : Bool → Subgroup G}
    (d : RealizedFactors T Y X M₁ M₂ F) (c : Configuration K T Y X M₂ F)
    (L : Subgroup (generated T Y F))
    (hL : Theory.GroupTheory.IsComponent (generated T Y F) L)
    (eL : L ≃* alternatingGroup (Fin 6))
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hfaithful : RawQuotient.mixedZ T Y F ⊓
      centralizer (L : Set (generated T Y F)) = ⊥)
    (eSelected : RawQuotient.selectedJoin L (RawQuotient.mixedZ T Y F) ≃*
      Equiv.Perm (Fin 6)) (hY : IsPPerfect 2 Y) (hF : IsPPerfect 2 (F false)) :
    Y ≤ L.map (generated T Y F).subtype ∧
      F false ≤ L.map (generated T Y F).subtype := by
  let J := generated T Y F
  let q := quotientCoordinates T d c L hL eL hZ hfaithful eSelected
  have contain (A : Subgroup G) (hA : A ≤ J) (hp : IsPPerfect 2 A) :
      A ≤ L.map J.subtype := by
    have hp' := hp.of_surjective (subgroupOfEquivOfLe hA).symm.toMonoidHom
      (subgroupOfEquivOfLe hA).symm.surjective
    simpa only [map_subgroupOf_eq_of_le hA] using
      map_mono (f := J.subtype) (q.factor_le_component (A.subgroupOf J) hp')
  exact ⟨contain Y (le_sup_left.trans le_sup_left) hY,
    contain (F false) (le_sup_left.trans le_sup_right) hF⟩

section Assembly
variable {K : GroupClass} (T : Sylow 2 G)
    {Y X M₁ M₂ : Subgroup G} {F : Bool → Subgroup G}
    (d : RealizedFactors T Y X M₁ M₂ F) (c : Configuration K T Y X M₂ F)
    (L : Subgroup (generated T Y F))
    (hL : Theory.GroupTheory.IsComponent (generated T Y F) L)
    (eL : L ≃* alternatingGroup (Fin 6))
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hfaithful : RawQuotient.mixedZ T Y F ⊓
      centralizer (L : Set (generated T Y F)) = ⊥)
    (eSelected : RawQuotient.selectedJoin L (RawQuotient.mixedZ T Y F) ≃*
      Equiv.Perm (Fin 6)) (hY : IsPPerfect 2 Y) (hF : IsPPerfect 2 (F false))

include d c hY hF in
private theorem mixed_inputs (S : Sylow 2 (generated T Y F))
    (hS : (S : Subgroup (generated T Y F)).map (generated T Y F).subtype = stabilizer T F) :
    let A := Y.subgroupOf (generated T Y F)
    let B := (F false).subgroupOf (generated T Y F)
    (IsPPerfect 2 A ∧ (S : Subgroup (generated T Y F)) ≤ normalizer (A : Set _) ∧
      (S : Subgroup (generated T Y F)).relIndex (A ⊔ (S : Subgroup _)) = 3) ∧
    (IsPPerfect 2 B ∧ (S : Subgroup (generated T Y F)) ≤ normalizer (B : Set _) ∧
      (S : Subgroup (generated T Y F)).relIndex (B ⊔ (S : Subgroup _)) = 3) ∧
    (A ⊔ (S : Subgroup _)) ⊔ (B ⊔ (S : Subgroup _)) = ⊤ := by
  let J := generated T Y F
  have hAJ : Y ≤ J := le_sup_left.trans le_sup_left
  have hBJ : F false ≤ J := le_sup_left.trans le_sup_right
  refine ⟨local_inputs S hS hAJ hY
    (inf_le_left.trans (d.sylow_le₁.trans d.normalizer₁.le)) c.first_index,
    local_inputs S hS hBJ hF inf_le_right c.second_index, ?_⟩
  apply (map_injective (f := J.subtype) J.subtype_injective)
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup,
    map_subgroupOf_eq_of_le hAJ, map_subgroupOf_eq_of_le hBJ, hS,
    ← MonoidHom.range_eq_map, range_subtype]

include d c hL eL hZ hfaithful eSelected hY hF

/-- Both residual conventions give the same embedded component; the star
quotient throughout remains the quotient by the three-prime core. -/
theorem component_residuals :
    L = primeToResidual 3 (generated T Y F) ∧
      L = pResidual 2 (generated T Y F) ∧
      L = (Y ⊔ F false).subgroupOf (generated T Y F) := by
  let J := generated T Y F
  let q := quotientCoordinates T d c L hL eL hZ hfaithful eSelected
  obtain ⟨S, hS⟩ := c.generated_sylow
  obtain ⟨⟨hp₁, hn₁, _⟩, ⟨hp₂, hn₂, _⟩, hg⟩ := mixed_inputs T d c hY hF S hS
  have hg' : (Y.subgroupOf J ⊔ (F false).subgroupOf J) ⊔ (S : Subgroup J) = ⊤ := by
    rw [sup_sup_sup_comm, sup_idem] at hg
    exact hg
  obtain ⟨hr, hj⟩ := component_eq_twoResidual_of_factor_containment L
    (Y.subgroupOf J) ((F false).subgroupOf J) (S : Subgroup J) hL hp₁ hp₂
    S.isPGroup' hn₁ hn₂ hg'
    (q.factor_le_component _ hp₁) (q.factor_le_component _ hp₂)
  refine ⟨q.component_eq_primeToResidual, hr, ?_⟩
  rw [subgroupOf_sup (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right)]
  exact hj

/-- The actual ambient centralizer indices supplied to `Invariance`, for
both original factors. No index or factor containment is an input. -/
theorem centralizer_indices :
    (stabilizer T F ⊓ centralizer (L.map (generated T Y F).subtype : Set G)).relIndex
      (stabilizer T F ⊓ centralizer (Y : Set G)) = 2 ∧
    (stabilizer T F ⊓ centralizer (L.map (generated T Y F).subtype : Set G)).relIndex
      (stabilizer T F ⊓ centralizer (F false : Set G)) = 2 := by
  let J := generated T Y F
  let q := quotientCoordinates T d c L hL eL hZ hfaithful eSelected
  obtain ⟨S, hS⟩ := c.generated_sylow
  obtain ⟨⟨hp₁, hn₁, hi₁⟩, ⟨hp₂, hn₂, hi₂⟩, _⟩ := mixed_inputs T d c hY hF S hS
  have transfer (A : Subgroup G) (hAJ : A ≤ J)
      (hp : IsPPerfect 2 (A.subgroupOf J))
      (hn : (S : Subgroup J) ≤ normalizer (A.subgroupOf J : Set J))
      (hi : (S : Subgroup J).relIndex (A.subgroupOf J ⊔ (S : Subgroup J)) = 3) :
      (stabilizer T F ⊓ centralizer (L.map J.subtype : Set G)).relIndex
        (stabilizer T F ⊓ centralizer (A : Set G)) = 2 := by
    have h := q.factor_centralizer_index S (A.subgroupOf J) hp hn hi
    rw [← relIndex_map_map_of_injective _ _ J.subtype_injective,
      centralizer_image S hS, centralizer_image S hS,
      map_subgroupOf_eq_of_le hAJ] at h
    exact h
  exact ⟨transfer Y (le_sup_left.trans le_sup_left) hp₁ hn₁ hi₁,
    transfer (F false) (le_sup_left.trans le_sup_right) hp₂ hn₂ hi₂⟩

/-- Recognition concerns the original subgroups, with their actual inclusion
in `I`, rather than just their star images. -/
theorem factors_alternating_four :
    Nonempty (Y ≃* alternatingGroup (Fin 4)) ∧
      Nonempty (F false ≃* alternatingGroup (Fin 4)) := by
  let J := generated T Y F
  let q := quotientCoordinates T d c L hL eL hZ hfaithful eSelected
  obtain ⟨S, hS⟩ := c.generated_sylow
  obtain ⟨⟨hp₁, hn₁, hi₁⟩, ⟨hp₂, hn₂, hi₂⟩, hg⟩ := mixed_inputs T d c hY hF S hS
  obtain ⟨⟨e₁⟩, ⟨e₂⟩⟩ := factors_equiv_from_coordinates S L
    (Y.subgroupOf J) ((F false).subgroupOf J) q hp₁ hp₂ hn₁ hn₂ hi₁ hi₂ hg
  exact ⟨⟨(subgroupOfEquivOfLe (le_sup_left.trans le_sup_left : Y ≤ J)).symm.trans e₁⟩,
    ⟨(subgroupOfEquivOfLe (le_sup_left.trans le_sup_right : F false ≤ J)).symm.trans e₂⟩⟩

/-- Apply the established index-two invariance theorem to the ambient
subgroups. This discharges the centralizer-order premise of local splitting. -/
theorem centralizer_eq_common_fixed :
    stabilizer T F ⊓ centralizer (L.map (generated T Y F).subtype : Set G) =
      commonFixed T Y F ∧ Nat.card (commonFixed T Y F) = 2 := by
  let J := generated T Y F
  let q := quotientCoordinates T d c L hL eL hZ hfaithful eSelected
  let : L.Normal := q.component_normal
  have hUJ : stabilizer T F ≤ J := le_sup_right.trans le_sup_left
  have hnJ : J ≤ normalizer (L.map J.subtype : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using L.le_normalizer_map J.subtype
  have hdis : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      (stabilizer T F ⊓ centralizer (L.map J.subtype : Set G)) = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    let zJ : J := ⟨z, hUJ hz.2.1⟩
    have hc : zJ ∈ centralizer (L : Set J) := by
      intro l hl
      exact Subtype.ext (hz.2.2 l (mem_map_of_mem J.subtype hl))
    have hz' : zJ ∈ RawQuotient.mixedZ T Y F ⊓ centralizer (L : Set J) := ⟨hz.1, hc⟩
    have hzOne : zJ = 1 := mem_bot.mp (hfaithful ▸ hz')
    exact mem_bot.mpr (congrArg (fun a : J => (a : G)) hzOne)
  have hE : commonFixed T Y F ≤ centralizer (L.map J.subtype : Set G) :=
    (le_centralizer_iff.mp c.generated_centralizes).trans (centralizer_le (map_subtype_le L))
  exact component_centralizer_eq_common_fixed T.isPGroup' inf_le_left c.index_stabilizer
    (d.sylow_le₁.trans d.normalizer₁.le) (hUJ.trans hnJ)
    (factor_containment T d c L hL eL hZ hfaithful eSelected hY hF).1
    (centralizer_indices T d c L hL eL hZ hfaithful eSelected hY hF).1
    hdis c.common_ne_bot (le_inf c.common_le_stabilizer hE)

end Assembly

omit [Finite G] in
private theorem fixed_plane {E A D : Subgroup G} [IsElementaryAbelian 2 E]
    (hsplit : fixed E A ⊔ D = E) (hdis : Disjoint (fixed E A) D)
    (hD : Nat.card D = 2) (hE : Nat.card E = 8) :
    IsElementaryAbelian 2 (fixed E A) ∧ Nat.card (fixed E A) = 4 := by
  have hcomm : fixed E A ≤ centralizer (D : Set G) := by
    intro x hx y hy
    exact setLike_mul_comm (show y ∈ E from hsplit ▸ mem_sup_right hy) (show x ∈ E from hx.1)
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hdis hcomm
  have hc := Nat.card_congr e.toEquiv
  rw [Nat.card_prod, hsplit, hD, hE] at hc
  refine ⟨?_, by omega⟩
  refine { toIsMulCommutative := ?_, exponent_dvd_p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · exact ⟨⟨fun x y => Subtype.ext (setLike_mul_comm
      (show (x : G) ∈ E from x.property.1) (show (y : G) ∈ E from y.property.1))⟩⟩
  · intro x
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := E) (p := 2) x x.property.1)

private theorem local_split {J U A E : Subgroup G} (L : Subgroup J)
    (q : QuotientCoordinates L) (S : Sylow 2 J)
    (hS : (S : Subgroup J).map J.subtype = U) (hAJ : A ≤ J)
    (hp : IsPPerfect 2 (A.subgroupOf J))
    (hn : (S : Subgroup J) ≤ normalizer (A.subgroupOf J : Set J))
    (hi : (S : Subgroup J).relIndex (A.subgroupOf J ⊔ (S : Subgroup J)) = 3)
    (hC : Nat.card (U ⊓ centralizer (L.map J.subtype : Set G) : Subgroup G) = 2)
    [IsElementaryAbelian 2 E] (hEU : E ≤ U) (hEA : E ≤ centralizer (A : Set G))
    (hE : Nat.card E = 4) :
    Nonempty (↥(A ⊔ U) ≃* (Multiplicative (ZMod 2 × ZMod 2) × Equiv.Perm (Fin 4))) := by
  have hUJ : U ≤ J := hS ▸ map_subtype_le (S : Subgroup J)
  have hEJ := hEU.trans hUJ
  let : IsElementaryAbelian 2 (E.subgroupOf J) := IsElementaryAbelian.subgroupOf hEJ
  have hES : E.subgroupOf J ≤ (S : Subgroup J) := by
    rw [sylow_eq_subgroupOf S hS]
    exact comap_mono hEU
  have hEC : E.subgroupOf J ≤ centralizer (A.subgroupOf J : Set J) := by
    intro e he a ha
    exact Subtype.ext (hEA he a ha)
  have hE' : Nat.card (E.subgroupOf J) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEJ).toEquiv).trans hE
  have hC' : Nat.card ((S : Subgroup J) ⊓ centralizer (L : Set J) : Subgroup J) = 2 := by
    rw [← card_map_of_injective J.subtype_injective, centralizer_image S hS]
    exact hC
  obtain ⟨e⟩ := q.local_equiv_e4_s4 S (A.subgroupOf J) (E.subgroupOf J)
    hp hn hi hC' hES hEC hE'
  have heq : A.subgroupOf J ⊔ (S : Subgroup J) = (A ⊔ U).subgroupOf J := by
    rw [sylow_eq_subgroupOf S hS, subgroupOf_sup hAJ hUJ]
  exact ⟨(subgroupOfEquivOfLe (sup_le hAJ hUJ)).symm.trans
    ((MulEquiv.subgroupCongr heq.symm).trans e)⟩

private theorem product_of_planes (E Z A B : Subgroup G)
    (hZE : Z ≤ E) (hAE : A ≤ E) (hBA : B ≤ A)
    (hE : Nat.card E = 8) (hZ : Nat.card Z = 4) (hA : Nat.card A = 4)
    (hB : Nat.card B = 2) (hd : Disjoint B Z) (hc : B ≤ centralizer (Z : Set G)) :
    ∃ e : B × ↥(Z ⊓ A) ≃* A, ∀ b z, (e (b, z) : G) = (b : G) * (z : G) := by
  have index_two (D : Subgroup G) (hDE : D ≤ E) (hD : Nat.card D = 4) :
      D.relIndex E = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) D E bot_le hDE
    rw [relIndex_bot_left, relIndex_bot_left, hD, hE] at hh
    omega
  have hi := relIndex_inf_le (H := Z) (K := A) (L := E)
  rw [index_two Z hZE hZ, index_two A hAE hA] at hi
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (Z ⊓ A) E bot_le
    (inf_le_left.trans hZE)
  rw [relIndex_bot_left, relIndex_bot_left, hE] at hh
  have hlo : 2 ≤ Nat.card (Z ⊓ A : Subgroup G) := by
    have hb := Nat.mul_le_mul_left (Nat.card (Z ⊓ A : Subgroup G)) hi
    rw [hh] at hb
    omega
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting B (Z ⊓ A)
    (hd.mono_right inf_le_left) (hc.trans (centralizer_le inf_le_left))
  have hle : B ⊔ (Z ⊓ A) ≤ A := sup_le hBA inf_le_right
  have hcard : Nat.card (B ⊔ (Z ⊓ A) : Subgroup G) = 2 * Nat.card (Z ⊓ A : Subgroup G) := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, hB]
  have hgen : B ⊔ (Z ⊓ A) = A := by
    apply eq_of_le_of_card_ge hle
    rw [hcard, hA]
    omega
  exact ⟨e.trans (MulEquiv.subgroupCongr hgen), he⟩

section Recognition
variable {K : GroupClass} (T : Sylow 2 G)
    {Y X M₁ M₂ : Subgroup G} {F : Bool → Subgroup G}
    (d : RealizedFactors T Y X M₁ M₂ F) (c : Configuration K T Y X M₂ F)
    (L : Subgroup (generated T Y F))
    (hL : Theory.GroupTheory.IsComponent (generated T Y F) L)
    (eL : L ≃* alternatingGroup (Fin 6))
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hfaithful : RawQuotient.mixedZ T Y F ⊓
      centralizer (L : Set (generated T Y F)) = ⊥)
    (eSelected : RawQuotient.selectedJoin L (RawQuotient.mixedZ T Y F) ≃*
      Equiv.Perm (Fin 6)) (hY : IsPPerfect 2 Y) (hF : IsPPerfect 2 (F false))
include d c hL eL hZ hfaithful eSelected hY hF

/-- Both actual local groups split as E₄ × S₄. The elementary factors are
the source fixed planes, and the complements are the actual intersections
with the component. The centralizer order is proved by invariance. -/
theorem local_groups :
    Nonempty (firstGroup T Y F ≃*
      (Multiplicative (ZMod 2 × ZMod 2) × Equiv.Perm (Fin 4))) ∧
    Nonempty (secondGroup T F ≃*
      (Multiplicative (ZMod 2 × ZMod 2) × Equiv.Perm (Fin 4))) := by
  let J := generated T Y F
  let q := quotientCoordinates T d c L hL eL hZ hfaithful eSelected
  obtain ⟨S, hS⟩ := c.generated_sylow
  obtain ⟨⟨hp₁, hn₁, hi₁⟩, ⟨hp₂, hn₂, hi₂⟩, _⟩ := mixed_inputs T d c hY hF S hS
  obtain ⟨he, hc⟩ := centralizer_eq_common_fixed T d c L hL eL hZ hfaithful eSelected hY hF
  have hC : Nat.card (stabilizer T F ⊓ centralizer (L.map J.subtype : Set G) : Subgroup G) = 2 :=
    he ▸ hc
  let : IsElementaryAbelian 2 (omega T) := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  obtain ⟨hE₁, hc₁⟩ := fixed_plane d.single_split₁ d.single_disjoint₁ d.single_card₁ c.omega_card
  obtain ⟨hE₂, hc₂⟩ := fixed_plane d.single_split₂ d.single_disjoint₂ d.single_card₂ c.omega_card
  let := hE₁
  let := hE₂
  have hEU : MixedLocal.omega T ≤ stabilizer T F :=
    (alpha_le_baumann _).trans (le_inf inf_le_left d.baumann_invariant)
  exact ⟨local_split L q S hS (le_sup_left.trans le_sup_left) hp₁ hn₁ hi₁ hC
      (inf_le_left.trans hEU) inf_le_right hc₁,
    local_split L q S hS (le_sup_left.trans le_sup_right) hp₂ hn₂ hi₂ hC
      (inf_le_left.trans hEU) inf_le_right hc₂⟩

/-- The corrected source product, as an actual ambient multiplication map.
The complement is C_Z(Y), whose order follows from the source fixed planes;
it is not the printed Z ∩ L. -/
theorem first_centralizer_product :
    ∃ e : ↥(stabilizer T F ⊓ centralizer (L.map (generated T Y F).subtype : Set G)) ×
        ↥(Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (Y : Set G)) ≃*
        ↥(stabilizer T F ⊓ centralizer (Y : Set G)),
      ∀ b z, (e (b, z) : G) = (b : G) * (z : G) := by
  let J := generated T Y F
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let A := stabilizer T F ⊓ centralizer (Y : Set G)
  let B := stabilizer T F ⊓ centralizer (L.map J.subtype : Set G)
  have hYL := (factor_containment T d c L hL eL hZ hfaithful eSelected hY hF).1
  have hBA : B ≤ A := inf_le_inf_left _ (centralizer_le hYL)
  obtain ⟨heB, hcB⟩ := centralizer_eq_common_fixed T d c L hL eL hZ hfaithful eSelected hY hF
  have hB : Nat.card B = 2 := by
    change Nat.card (stabilizer T F ⊓ centralizer (L.map J.subtype : Set G) : Subgroup G) = 2
    rw [heB]
    exact hcB
  have hi := (centralizer_indices T d c L hL eL hZ hfaithful eSelected hY hF).1
  have hA : Nat.card A = 4 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) B A bot_le hBA
    rw [relIndex_bot_left, relIndex_bot_left, hB, hi] at hh
    omega
  have hEU : MixedLocal.omega T ≤ stabilizer T F :=
    (alpha_le_baumann _).trans (le_inf inf_le_left d.baumann_invariant)
  have hZE : Z ≤ MixedLocal.omega T := centralOmega_le_thompsonAlpha _
  have hZU := hZE.trans hEU
  let : IsElementaryAbelian 2 (MixedLocal.omega T) :=
    Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  have hplane := (fixed_plane d.single_split₁ d.single_disjoint₁ d.single_card₁ c.omega_card).2
  have hplane_eq : fixed (MixedLocal.omega T) Y = A :=
    eq_of_le_of_card_ge (inf_le_inf_right _ hEU) (by rw [hplane, hA])
  have hAE : A ≤ MixedLocal.omega T := hplane_eq ▸ inf_le_left
  have hBZ : Disjoint B Z := by
    apply disjoint_iff_inf_le.mpr
    intro b hb
    have hbJ : b ∈ J := (show stabilizer T F ≤ J from le_sup_right.trans le_sup_left) hb.1.1
    have hbc : (⟨b, hbJ⟩ : J) ∈ centralizer (L : Set J) := by
      intro l hl
      exact Subtype.ext (hb.1.2 l (mem_map_of_mem J.subtype hl))
    have hb1 : (⟨b, hbJ⟩ : J) = 1 := mem_bot.mp
      (hfaithful ▸ (show (⟨b, hbJ⟩ : J) ∈ RawQuotient.mixedZ T Y F ⊓
        centralizer (L : Set J) from ⟨hb.2, hbc⟩))
    exact mem_bot.mpr (congrArg (fun x : J => (x : G)) hb1)
  have hBC : B ≤ centralizer (Z : Set G) := by
    intro b hb z hz
    exact (((Stellmacher.mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz).2.2
      b hb.1.1).symm
  obtain ⟨e, he⟩ := product_of_planes (MixedLocal.omega T) Z A B hZE hAE hBA
    c.omega_card hZ hA hB hBZ hBC
  have hline : Z ⊓ A = Z ⊓ centralizer (Y : Set G) := by
    change Z ⊓ (stabilizer T F ⊓ centralizer (Y : Set G)) = _
    rw [← inf_assoc, inf_eq_left.mpr hZU]
  exact ⟨(MulEquiv.prodCongr (MulEquiv.refl B) (MulEquiv.subgroupCongr hline.symm)).trans e,
    fun b z => he b _⟩

end Recognition
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Mixed

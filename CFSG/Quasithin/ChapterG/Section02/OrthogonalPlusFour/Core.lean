module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Source
public import Theory.GroupTheory.CentralPPerfectProduct
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Eliminating the central two-kernel in G.2.6

Put P = W ∨ Wᵍ. The normal-layer calculation makes P normal in I and
S/P central in I/P. The map from I/P to the marked S₃ × S₃ model has a
two-group kernel. Its restriction to U⁺ is injective since U ∩ S = W ≤ P.
Its restriction to L⁺ is injective by two-perfectness and the abelian
exponent-three image: commutator and power maps into the central kernel
must vanish. Finally I = LU gives I⁺ = L⁺U⁺; the two images intersect
trivially by their coprime exponents, eliminating the whole kernel.
This proves S = P and the literal ordered-product statement S = WWᵍ.

Generation, normalization of U by S, and the marked I/S model are the
preceding source conclusions, produced by the separate model/generation
branch. No splitting or odd-order assumption on L⁺ is made. The final
image equivalences also retain that branch's explicit compatibility with
the original projection LT → LT/O₂(LT), so they concern actual starred
images. Final G.2.6 assembly must discharge these preceding premises.

Source: Aschbacher–Smith, G.2.6(2), combined manuscript of 1 March 2004,
printed p.336, PDF p.347.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup
variable {G : Type*} [Group G] [Finite G]

/-- The concrete two symmetric factors in the preceding model calculation. -/
abbrev SymmetricPair := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)

/-- The marked elementary nine-subgroup of the concrete model. -/
def alternatingPair : Subgroup SymmetricPair :=
  (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))

/-- The model map uses exactly the intrinsic two-core quotient of I. -/
def coreModelProjection (D : Setup G) (g : G)
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* SymmetricPair) : D.I g →* SymmetricPair :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I g)))

private theorem alternatingPair_commute {x y : SymmetricPair}
    (hx : x ∈ alternatingPair) (hy : y ∈ alternatingPair) : Commute x y := by
  let := alternatingGroup.isMulCommutative_of_card_le_three (α := Fin 3) (by simp)
  apply Prod.ext
  · exact congrArg Subtype.val (mul_comm (⟨x.1, hx.1⟩ : alternatingGroup (Fin 3)) ⟨y.1, hy.1⟩)
  · exact congrArg Subtype.val (mul_comm (⟨x.2, hx.2⟩ : alternatingGroup (Fin 3)) ⟨y.2, hy.2⟩)

private theorem alternatingPair_pow {x : SymmetricPair} (hx : x ∈ alternatingPair) :
    x ^ 3 = 1 := by
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  apply Prod.ext
  · exact congrArg Subtype.val (hc ▸ pow_card_eq_one' (x := (⟨x.1, hx.1⟩ : alternatingGroup (Fin 3))))
  · exact congrArg Subtype.val (hc ▸ pow_card_eq_one' (x := (⟨x.2, hx.2⟩ : alternatingGroup (Fin 3))))

/-- G.2.6(2) from the earlier generation and marked-model conclusions.
The U-image need only be a two-group here, which follows from G.2.2;
its stronger Sylow E₄ identification is not required for this deduction. -/
theorem core_eq_coreProduct_of_model {D : Setup G} {g : G}
    (d : Hypothesis D g) (hgen : D.I g = D.L ⊔ D.U)
    (hSU : D.S g ≤ normalizer (D.U : Set G))
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* SymmetricPair)
    (hmark : (D.L.subgroupOf (D.I g)).map (coreModelProjection D g e) = alternatingPair) :
    D.S g = coreProduct D g := by
  have hLI : D.L ≤ D.I g := by rw [hgen]; exact le_sup_left
  have hUI : D.U ≤ D.I g := le_sup_left
  have hgI : g ∈ D.I g := hLI d.g_mem
  obtain ⟨hPS, hPN, hcomm⟩ := coreProduct_normal_and_commutator hgI hSU
  let P := (coreProduct D g).subgroupOf (D.I g)
  let : P.Normal := (normal_subgroupOf_iff_le_normalizer
    (hPS.trans (pCoreIn_le 2 (D.I g)))).mpr hPN
  let q := QuotientGroup.mk' P
  let t := coreModelProjection D g e
  have htker : t.ker = pCore 2 (D.I g) := by
    rw [show t = e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I g))) from rfl,
      MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hcore (x : D.I g) : x ∈ pCore 2 (D.I g) ↔ (x : G) ∈ D.S g := by
    constructor
    · intro hx
      exact mem_map.mpr ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      have hyx : y = x := Subtype.ext he
      exact hyx ▸ hy
  have hPt : P ≤ t.ker := by
    intro x hx
    rw [htker]
    exact (hcore x).mpr (hPS hx)
  let f := QuotientGroup.lift P t hPt
  have hfker : f.ker = (pCore 2 (D.I g)).map q := by
    rw [show f = QuotientGroup.lift P t hPt from rfl, QuotientGroup.ker_lift, htker]
  have hfp : IsPGroup 2 f.ker := by
    rw [hfker]
    exact pCore_isPGroup.map q
  have hfc : f.ker ≤ center (D.I g ⧸ P) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := show x ∈ (pCore 2 (D.I g)).map q from hfker ▸ hx
    apply mem_center_iff.mpr
    intro y
    obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective P y
    have hc : ⁅s, i⁆ ∈ P := hcomm (commutator_mem_commutator ((hcore s).mp hs) i.property)
    have hcq : ⁅q s, q i⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff ⁅s, i⁆).mpr hc
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcq).symm
  let Li := D.L.subgroupOf (D.I g)
  let Ui := D.U.subgroupOf (D.I g)
  let A := Li.map q
  let B := Ui.map q
  have hLn : (D.I g) ≤ normalizer (D.L : Set G) := by
    rw [hgen]
    exact sup_le D.L.le_normalizer (d.closure.normal.1.trans d.base.T_normalizes_L)
  let : Li.Normal := (normal_subgroupOf_iff_le_normalizer hLI).mpr hLn
  have hBA : B ≤ normalizer (A : Set (D.I g ⧸ P)) :=
    (map_mono (show Ui ≤ normalizer (Li : Set (D.I g)) from le_normalizer_of_normal)).trans
      (Li.le_normalizer_map q)
  have hLi : IsPPerfect 2 Li :=
    ((pResidual_eq_top_iff 2 D.L).mp d.base.residual).of_surjective
      (subgroupOfEquivOfLe hLI).symm.toMonoidHom (subgroupOfEquivOfLe hLI).symm.surjective
  have hA : IsPPerfect 2 A := hLi.of_surjective (q.subgroupMap Li) (q.subgroupMap_surjective Li)
  have hB : IsPGroup 2 B := ((U_isPGroup d.base d.closure).comap_subtype).map q
  have hLiUi : Li ⊔ Ui = ⊤ := by
    apply map_injective (D.I g).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLI, map_subgroupOf_eq_of_le hUI,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hgen.symm
  have hAB : A ⊔ B = ⊤ := by
    rw [show A ⊔ B = (Li ⊔ Ui).map q from (map_sup Li Ui q).symm,
      hLiUi, map_top_of_surjective q (QuotientGroup.mk'_surjective P)]
  have hBi : Function.Injective (f.domRestrict B) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro b hb
    obtain ⟨u, hu, he⟩ := b.property
    have ht : t u = 1 := by
      change f (q u) = 1
      rw [he]
      exact hb
    have huS : (u : G) ∈ D.S g := (hcore u).mp (htker ▸ ht)
    have huP : u ∈ P := mem_sup_left (show (u : G) ∈ D.W g from ⟨hu, huS⟩)
    apply Subtype.ext
    exact he.symm.trans ((QuotientGroup.eq_one_iff u).mpr huP)
  have hAmem (a : A) : f a ∈ alternatingPair := by
    obtain ⟨l, hl, he⟩ := a.property
    rw [← hmark]
    exact mem_map.mpr ⟨l, hl, by change f (q l) = f a; rw [he]⟩
  have hfi : Function.Injective f :=
    f.injective_of_isPPerfect_product A B hfc hfp hA hB hBA hAB hBi
      (fun a b => alternatingPair_commute (hAmem a) (hAmem b))
      (by decide : Nat.Coprime 2 3) (fun a => alternatingPair_pow (hAmem a))
  apply le_antisymm ?_ hPS
  intro s hs
  let si : D.I g := ⟨s, pCoreIn_le 2 (D.I g) hs⟩
  have hts : t si = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [htker]
    exact (hcore si).mpr hs
  have hqs : q si = 1 := hfi (by change t si = f 1; rw [hts, map_one])
  exact (QuotientGroup.eq_one_iff si).mp hqs

/-- Relative normality, before eliminating the kernel. -/
theorem coreProduct_normal {D : Setup G} {g : G}
    (d : Hypothesis D g) (hgen : D.I g = D.L ⊔ D.U)
    (hSU : D.S g ≤ normalizer (D.U : Set G)) :
    ((coreProduct D g).subgroupOf (D.I g)).Normal := by
  have hgI : g ∈ D.I g := hgen.symm ▸ mem_sup_left d.g_mem
  obtain ⟨hPS, hPN, _⟩ := coreProduct_normal_and_commutator hgI hSU
  exact (normal_subgroupOf_iff_le_normalizer
    (hPS.trans (pCoreIn_le 2 (D.I g)))).mpr hPN

/-- The literal ordered product in G.2.6(2). -/
theorem core_eq_product_of_model {D : Setup G} {g : G}
    (d : Hypothesis D g) (hgen : D.I g = D.L ⊔ D.U)
    (hSU : D.S g ≤ normalizer (D.U : Set G))
    (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* SymmetricPair)
    (hmark : (D.L.subgroupOf (D.I g)).map (coreModelProjection D g e) = alternatingPair) :
    (D.S g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G) := by
  rw [core_eq_coreProduct_of_model d hgen hSU e hmark]
  exact coreProduct_product (hgen.symm ▸ mem_sup_left d.g_mem) hSU

/-- The plus image uses the literal projection I → I/P. -/
def coreImage (D : Setup G) (g : G)
    [((coreProduct D g).subgroupOf (D.I g)).Normal] (A : Subgroup G) :
    Subgroup (D.I g ⧸ (coreProduct D g).subgroupOf (D.I g)) :=
  (A.subgroupOf (D.I g)).map (QuotientGroup.mk' ((coreProduct D g).subgroupOf (D.I g)))

/-- The restricted plus projection retains the actual subgroup image. -/
def coreImageProjection (D : Setup G) (g : G)
    [((coreProduct D g).subgroupOf (D.I g)).Normal]
    (A : Subgroup G) (hAI : A ≤ D.I g) : A →* coreImage D g A :=
  ((QuotientGroup.mk' ((coreProduct D g).subgroupOf (D.I g))).comp
    (inclusion hAI)).codRestrict _
      (fun a => mem_map.mpr ⟨inclusion hAI a, a.property, rfl⟩)

/-- The genuine inclusion used by the starred projection. -/
theorem Hypothesis.I_le_LT {D : Setup G} {g : G} (d : Hypothesis D g) : D.I g ≤ D.LT :=
  d.I_le_LU.trans (sup_le le_sup_left (d.closure.normal.1.trans le_sup_right))

section Images
variable {D : Setup G} {g : G}
variable (d : Hypothesis D g) (hgen : D.I g = D.L ⊔ D.U)
  (hSU : D.S g ≤ normalizer (D.U : Set G))
  (e : (D.I g ⧸ pCore 2 (D.I g)) ≃* SymmetricPair)
  (hmark : (D.L.subgroupOf (D.I g)).map (coreModelProjection D g e) = alternatingPair)
  [((coreProduct D g).subgroupOf (D.I g)).Normal]

/-- The map I/P → I/S induced by the identity on I is an isomorphism. -/
def coreQuotientEquiv :
    (D.I g ⧸ (coreProduct D g).subgroupOf (D.I g)) ≃* (D.I g ⧸ pCore 2 (D.I g)) :=
  QuotientGroup.quotientMulEquivOfEq (by
    rw [← core_eq_coreProduct_of_model d hgen hSU e hmark]
    change ((pCore 2 (D.I g)).map (D.I g).subtype).comap (D.I g).subtype = _
    exact comap_map_eq_self_of_injective (D.I g).subtype_injective _)

@[simp] theorem coreQuotientEquiv_mk (x : D.I g) :
    coreQuotientEquiv d hgen hSU e hmark
      (QuotientGroup.mk' ((coreProduct D g).subgroupOf (D.I g)) x) =
      QuotientGroup.mk' (pCore 2 (D.I g)) x := rfl

include d hgen hSU e hmark in
/-- The central two-kernel S⁺ vanishes in the literal quotient I/P. -/
theorem coreImage_S_eq_bot : coreImage D g (D.S g) = ⊥ := by
  rw [coreImage, core_eq_coreProduct_of_model d hgen hSU e hmark,
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

variable
  (estar : (D.I g ⧸ pCore 2 (D.I g)) ≃* D.star (D.I g))
  (hcompatible : ∀ x : D.I g,
    estar (QuotientGroup.mk' (pCore 2 (D.I g)) x) = starProjection D (D.I g) d.I_le_LT x)

/-- Transport plus images to the actual starred images. The extra premise
is exactly the preceding model producer's compatibility with the literal
LT/O₂(LT) projection; it is not an arbitrary abstract isomorphism. -/
noncomputable def coreImageEquivStar (A : Subgroup G) (hAI : A ≤ D.I g) :
    coreImage D g A ≃* D.star A := by
  let ei := coreQuotientEquiv d hgen hSU e hmark
  let r := (D.star (D.I g)).subtype.comp (estar.toMonoidHom.comp ei.toMonoidHom)
  have hr : Function.Injective r := Subtype.val_injective.comp (estar.injective.comp ei.injective)
  have hrapply (x : D.I g) :
      r (QuotientGroup.mk' ((coreProduct D g).subgroupOf (D.I g)) x) =
        QuotientGroup.mk' (pCore 2 D.LT) (inclusion d.I_le_LT x) :=
    congrArg Subtype.val (hcompatible x)
  refine ((coreImage D g A).equivMapOfInjective r hr).trans (MulEquiv.subgroupCongr ?_)
  rw [coreImage, map_map]
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    change r (QuotientGroup.mk' ((coreProduct D g).subgroupOf (D.I g)) a) ∈ D.star A
    rw [hrapply]
    exact mem_map.mpr ⟨inclusion d.I_le_LT a, ha, rfl⟩
  · rintro x ⟨a, ha, he⟩
    let ai : D.I g := ⟨a, hAI ha⟩
    exact mem_map.mpr ⟨ai, ha, (hrapply ai).trans he⟩

/-- The image equivalence intertwines the literal plus and star projections. -/
@[simp] theorem coreImageEquivStar_comp (A : Subgroup G) (hAI : A ≤ D.I g) :
    (coreImageEquivStar d hgen hSU e hmark estar hcompatible A hAI).toMonoidHom.comp
      (coreImageProjection D g A hAI) = starProjection D A (hAI.trans d.I_le_LT) := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  change (estar (QuotientGroup.mk' (pCore 2 (D.I g)) (inclusion hAI a)) : D.Star) =
    (starProjection D (D.I g) d.I_le_LT (inclusion hAI a) : D.Star)
  exact congrArg Subtype.val (hcompatible (inclusion hAI a))

/-- The source U⁺ ≃ U*, with both quotients and the original U fixed. -/
noncomputable def coreUEquivStar : coreImage D g D.U ≃* D.star D.U :=
  coreImageEquivStar d hgen hSU e hmark estar hcompatible D.U le_sup_left

/-- The source L⁺ ≃ E₉, using the given actual starred L coordinates. -/
noncomputable def coreLEquivNine : coreImage D g D.L ≃* Multiplicative (Fin 2 → ZMod 3) :=
  (coreImageEquivStar d hgen hSU e hmark estar hcompatible D.L
    (hgen.symm ▸ le_sup_left)).trans d.L_model

end Images
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour

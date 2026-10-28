module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointCentralCover
public import Theory.SpecificGroups.SmallRankTwoPointMotion.CubicSymmetric

/-!
# The cubic S₆ point action with its sign kernel

The normal cubic kernel is inverted by odd permutations. The two local
index-three groups map faithfully to the two S₆ parabolics: collapse of a
local cubic would make its image Sylow and force the other solvable local
group to generate S₆. Each parabolic has a central odd involution in the
common Sylow; its inversion of the cubic kernel lifts containment of the
point stabilizer. The stabilizer meets that prime normal kernel trivially
because the original point generates the full conjugate span.

Thus the stabilizer is Sylow, contradicted by the cubic fixer on the literal
B.5 section, including its nonsplit extensions. The original comparison map
then excludes the source cubic S₆ cover without erasing its sign action.
Source: Aschbacher--Smith 13.2.12, printed p.882; F.6.18(8).
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open ClassificationComparison ClassificationComparison.FFAlternatives NativeSections
private theorem sections_cubic
    {E V : Type*} [Group E] [Finite E] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) E V) (N : Subgroup E) (K : Subgroup N)
    (s : MovedSection (ρ.comp N.subtype) K)
    (h : SectionAlternatives s) (S : Sylow 2 E) :
    ∃ c : E, c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup E), ρ c v = v := by
  let T : Sylow 2 N := Classical.choice inferInstance
  have lift (h : ∃ d : N, d ∉ T ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (ρ.comp N.subtype) (T : Subgroup N), ρ d v = v) :
      ∃ c : E, c ∉ S ∧ c ^ 3 = 1 ∧
        ∀ v ∈ fixedSpace ρ (S : Subgroup E), ρ c v = v := by
    obtain ⟨d,hd,h3,hf⟩ := h
    exact sylow_fixedSpace_enlargement_of_embedded_cubic ρ N.subtype N.subtype_injective
      (T : Subgroup N) T.isPGroup' d h3 (fun he => hd (he ▸ T.one_mem)) hf S
  rcases h with h | h | h
  · exact lift (movedSection_model_enlargement s h T)
  · exact lift (movedSpace_model_enlargement s h T)
  · cases h with
    | binaryG2 _ e => exact lift (ExceptionalFixedSpace.BinaryG2.enlargement s e T)
    | tripleSix hf a => exact lift (ExceptionalFixedSpace.TripleSix.movedSection_enlargement s hf a T)
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d
/-- Both moving point groups exclude a cubic sign-kernel quotient onto S₆.
No centrality of the cubic kernel is assumed. -/
theorem point_action_no_cubic_symmetric_quotient
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hPv : P₁ ≤ Gv (markedV d.flag.flag.module))
    (hinter : P₁ ⊓ (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)) =
      ChapterB.baumann (T : Subgroup G)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let U := conjugateSpanBy (zpowers x) ⊤
      let E := J ⧸ centralizer (U : Set J)
      let ρ := ChapterB.InternalThompsonAction.action U
      let N := offenderSubgroup ρ
      let σ := ρ.comp N.subtype
      ¬ Group.IsSolvable E →
      ∀ b : QuasisimpleComparison.BoundedBranch σ,
        SectionAlternatives b.source.sectionData →
        ∀ q : E →* Equiv.Perm (Fin 6), Function.Surjective q →
          Nat.card q.ker = 3 →
          (∀ g : E, Equiv.Perm.sign (q g) = -1 →
            ∀ z ∈ q.ker, g*z*g⁻¹ = z⁻¹) → False := by
  intro P₂ J hg x hx hr
  let := hr.normal
  let := hr.elementary
  intro U E ρ N σ hns b hsections q hq hk hinv
  let f := QuotientGroup.mk' (centralizer (U : Set J))
  let A := P₁.subgroupOf J
  let B := P₂.subgroupOf J
  obtain ⟨S,hS⟩ := hg.intersection_sylow
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective (centralizer (U : Set J)))
  let v : Additive U := Additive.ofMul ⟨x,le_conjugateSpanBy _ _ (mem_zpowers x)⟩
  let C : Subgroup E :=
    (MulAction.stabilizer (Module.End (ZMod 2) (Additive U))ˣ v).comap ρ.asGroupHom
  have hC (g : E) : g ∈ C ↔ ρ g v = v := Iff.rfl
  have hfixed : v ∈ fixedSpace ρ (S' : Subgroup E) := by
    apply (NormalElementaryQuotient.mem_fixedSpace_image U f
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (S : Subgroup J) v).mpr
    intro a ha
    apply Subtype.ext
    change (a:G) * (x:G) = (x:G) * (a:G)
    rw [hx]
    have ha' : a ∈ A ⊓ B := hS.ge ha
    exact mem_centralizer_iff.mp (complement_centralizes_baumann d hH hB hZ hs hz)
      a (hinter ▸ ha')
  have hSC : (S' : Subgroup E) ≤ C := fun a ha => (hC a).mpr (hfixed ⟨a,ha⟩)
  have haC : ¬ A.map f ≤ C := by
    intro h
    have hv : v ∈ fixedSpace ρ (A.map f) := fun a => (hC a).mp (h a.property)
    have hcent := (NormalElementaryQuotient.mem_fixedSpace_image U f
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) A v).mp hv
    apply original_paired_point_not_centralizes_complement d hH hB hZ hs hz horiginal hPv
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg J.subtype (hcent ⟨a,mem_sup_left ha⟩ ha)
    change a * (x:G) = (x:G) * a at he
    rwa [hx] at he
  have hbC : ¬ B.map f ≤ C := by
    intro h
    have hv : v ∈ fixedSpace ρ (B.map f) := fun a => (hC a).mp (h a.property)
    have hcent := (NormalElementaryQuotient.mem_fixedSpace_image U f
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) B v).mp hv
    apply point_residual_not_centralizes_complement d
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg J.subtype (hcent ⟨a,mem_sup_right (mem_sup_left ha)⟩ (mem_sup_left ha))
    change a * (x:G) = (x:G) * a at he
    rwa [hx] at he
  have hCpre : C.comap f = centralizer ({x} : Set J) := by
    ext j
    change (ρ (f j) v = v) ↔ j ∈ centralizer ({x} : Set J)
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro he
      have hh := congrArg (fun w : Additive U => (w.toMul : J)) he
      rw [ChapterB.InternalThompsonAction.action_apply] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro he
      apply Subtype.ext
      change ((ρ (f j) v).toMul : J) = x
      rw [ChapterB.InternalThompsonAction.action_apply]
      exact mul_inv_eq_iff_eq_mul.mpr he
  have hCimage : C = (centralizer ({x} : Set J)).map f := by
    rw [←hCpre,map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hfaith : C ⊓ q.ker = ⊥ := by
    rw [hCimage]
    exact Theory.SpecificGroups.SmallRankTwoPointMotion.CubicSymmetric.centralizer_seed_image_inf_cubic_eq_bot
      x f (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) q.ker hk
  obtain ⟨_,_,_,eA,eB,_,_⟩ := point_span_action_comparison d hH hB hZ hs hz
    horiginal hPv hinter hg x hx U hr (le_conjugateSpanBy _ _ (mem_zpowers x))
  let ea : (A.map f ⧸ pCore 2 (A.map f)) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans
      hg.primeToThreeCore_quotient_left.some
  let eb : (B.map f ⧸ pCore 2 (B.map f)) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).trans
      hg.symm.primeToThreeCore_quotient_left.some
  have hsol (M : Subgroup J) (h : Group.IsSolvable M) : Group.IsSolvable (M.map f) := by
    let := h
    exact Group.isSolvable_of_surjective (f.subgroupMap_surjective M)
  have hCS : C = (S' : Subgroup E) :=
    Theory.SpecificGroups.SmallRankTwoPointMotion.CubicSymmetric.cubic_symmetric_point_stabilizer
      q hq hk hinv S' (A.map f) (B.map f) C
      (map_mono (hS ▸ inf_le_left)) (map_mono (hS ▸ inf_le_right))
      (by rw [←Subgroup.map_sup,hg.generated,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)])
      (hsol A hg.local_solvable) (hsol B hg.symm.local_solvable) ea eb hSC haC hbC hfaith
  obtain ⟨c,hcS,_,hcv⟩ := sections_cubic ρ N (generalizedFitting N)
    b.source.sectionData hsections S'
  exact hcS (show c ∈ (S' : Subgroup E) from hCS ▸ (hC c).mpr (hcv v hfixed))
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

/-- Transport the entire cubic sign-kernel quotient through a proved
isomorphism; both quotient maps remain specified. -/
theorem triple_symmetric_quotient_of_equiv
    {D E : Type*} [Group D] [Group E] (e : D ≃* E)
    (h : FSource.TripleSymmetric D 6) :
    ∃ q : E →* Equiv.Perm (Fin 6), Function.Surjective q ∧
      Nat.card q.ker = 3 ∧
      (∀ g : E, Equiv.Perm.sign (q g) = -1 →
        ∀ z ∈ q.ker, g*z*g⁻¹ = z⁻¹) := by
  let := h.normal
  let f := h.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' h.kernel)
  let q := f.comp e.symm.toMonoidHom
  have hf : Function.Surjective f :=
    h.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfk : f.ker = h.kernel := by
    rw [MonoidHom.ker_comp_of_injective _ _ h.quotientEquiv.injective,QuotientGroup.ker_mk']
  have hqk : q.ker = h.kernel.map e.toMonoidHom := by
    ext z
    change f (e.symm z) = 1 ↔ z ∈ h.kernel.map e.toMonoidHom
    rw [←MonoidHom.mem_ker,hfk]
    constructor
    · exact fun hz => ⟨e.symm z,hz,e.apply_symm_apply z⟩
    · rintro ⟨y,hy,rfl⟩
      change e.symm (e y) ∈ h.kernel
      rw [e.symm_apply_apply]
      exact hy
  refine ⟨q,hf.comp e.symm.surjective,?_,?_⟩
  · rw [hqk,card_map_of_injective e.injective,Nat.card_congr h.kernelEquiv.toEquiv]
    simp [FSource.C]
  · intro g hg z hz
    have hz' : e.symm z ∈ h.kernel := by
      rw [←hfk]
      exact hz
    have hh := h.inverse_action (e.symm g) hg ⟨e.symm z,hz'⟩
    apply e.symm.injective
    simpa only [map_mul,map_inv] using hh

/-- The faithful original comparison excludes its cubic S₆ source cover
once the literal point action has no cubic sign-kernel quotient. -/
theorem point_not_triple_symmetric_six_source
    {D E : Type*} [Group D] [Group E]
    (hfaith : ∀ _ : FSource.TripleSymmetric D 6, Nonempty (D ≃* E))
    (hne : ∀ q : E →* Equiv.Perm (Fin 6), Function.Surjective q →
      Nat.card q.ker = 3 →
      (∀ g : E, Equiv.Perm.sign (q g) = -1 →
        ∀ z ∈ q.ker, g*z*g⁻¹ = z⁻¹) → False) :
    ¬ Nonempty (FSource.TripleSymmetric D 6) := by
  rintro ⟨h⟩
  obtain ⟨e⟩ := hfaith h
  obtain ⟨q,hq,hk,hi⟩ := triple_symmetric_quotient_of_equiv e h
  exact hne q hq hk hi
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

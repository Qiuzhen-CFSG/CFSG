module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.Marking.CentralizerImage
public import Theory.Representation.G2BinaryPointMarking

/-!
# The actual point parabolic of the critical G₂ pair

The natural projection carries the critical line A₁ to a nonzero vector.
Its generator cannot centralize Q_H, since that centralizer has zero
natural image. The central commutator row corrects lifts of its quotient
stabilizer, identifying C_H(A₁)* with the actual point stabilizer. The
endpoint equality H=C_G(V₁) supplies relative normalization of Uγ; no
normality in the whole star group is required. Compatible conjugation
then gives the literal root marking used by the displacement estimates.

Source: Aschbacher–Smith 13.8.27, final paragraph, printed p.963.
The earlier plus-kernel equality and recognized component section remain
inputs of the final source owner qt-d-138-six-g2-source.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry Atlas.G2
variable {G : Type*} [Group G] [Finite G] {H K L T V V₃ V₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Construct the compatible point marking for the literal critical actor. -/
theorem source_point_marking_of_section
    (c : CriticalPair L T H V)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : Theory.GroupTheory.generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Model (ZMod 2)))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (Natural.OrthogonalCover.binaryNatural (ZMod 2)) eK)
    (hUg : c.Ugamma V₃ ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hcard : Nat.card V₁ = 2)
    (hcompare : Nat.log 2
      ((Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
        (Source.UH H V₃)) ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hB : IsElementaryAbelian 2 (Source.starImage H c.Vgamma))
    (hproper : Source.starImage H (c.Ugamma V₃) < Source.starImage H c.Vgamma)
    (hH : H = centralizer (V₁ : Set G))
    (hcomm : ⁅Source.QH H, Source.UH H V₃⁆ ≤ V₁)
    (hpluskernel : commutatorPreimage H (Source.UH H V₃)
      (Source.UH H V₃ ⊓ centralizer (Source.QH H : Set G)) = Source.QH H) :
    rank (Source.starImage H (c.Ugamma V₃)) < 3 ∧
    c.Aone V₁ ≤ Source.UH H V₃ ∧
    ∃ (f : Source.Hstar H →* Model (ZMod 2))
      (p : Additive (Source.Utilde H V₃ V₁) →ₗ[ZMod 2] Natural.Space (ZMod 2)),
      Function.Injective f ∧ Function.Surjective p ∧
      (∀ a v, p (ρ a v) = Natural.action (ZMod 2) (f a) (p v)) ∧
      (Source.starImage H (centralizer (c.Aone V₁ : Set G))).map f =
        BinaryCore.secondParabolic ⊓ f.range ∧
      (Source.starImage H (c.Ugamma V₃)).map f ≤ unipotent ∧
      BinaryParabolicPair.derivedSecondAmbient ≤
        normalizer ((Source.starImage H (c.Ugamma V₃)).map f : Set _) := by
  obtain ⟨hr,hAU,f,p,hf,hp,hfK,he,hk⟩ := projection_and_line_of_section
    c hKH hK hfit ρ hρ s hgen eK hs hUg hreverse hcard hcompare hA hB hproper
  have hnz := source_line_projection_ne_bot c s hUg hreverse hcard hcompare f hf p hp he hA hr
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnz
  obtain ⟨w,hw,rfl⟩ := hv
  obtain ⟨t,ht,rfl⟩ := (s.mem_image _ _).mp hw
  have ht1 : (t:G) ≠ 1 := by
    intro ht1
    have ht' : t = 1 := Subtype.ext ht1
    apply hv0
    rw [ht',map_one]
    exact map_zero p
  have hfull : Coinvariants.ker (ρ.comp (Source.starImage H K).subtype) = ⊤ := by
    rw [← subspaceCommutator_top_eq_coinvariants]
    exact (commutatorImage_eq_subspaceCommutator K hKH ρ hρ).symm.trans
      (commutatorImage_eq_top hgen)
  have hzero := source_core_centralizer_projection_eq_bot c s
    ((Components.componentStarEquiv H K hKH hK).symm.trans eK)
    f p hp he hfK hk.le hfull hpluskernel hA.1
  have htn : ¬ (t:G) ∈ centralizer (Source.QH H : Set G) := by
    intro htn
    apply hv0
    have hm : p (s.quotient t).toAdd ∈
        (s.image (Source.UH H V₃ ⊓ centralizer (Source.QH H : Set G))).map p :=
      ⟨_,(s.mem_image _ _).mpr ⟨t,⟨t.property,htn⟩,rfl⟩,rfl⟩
    simpa only [hzero,Submodule.mem_bot] using hm
  let C := Source.starImage H (centralizer (c.Aone V₁ : Set G))
  let A := Source.starImage H (c.Ugamma V₃)
  have hC (a) : a ∈ C ↔ Natural.action (ZMod 2) (f a) (p (s.quotient t).toAdd) =
      p (s.quotient t).toAdd :=
    (source_mem_line_centralizer_star_iff c s hcard hcomm t ht ht1 htn a).trans
      (source_point_fixed_iff hKH hK hfit ρ hρ hgen eK f p hp hfK he hk a _)
  have hAC : A ≤ C := by
    apply map_mono
    apply comap_mono
    exact (map_mono s.le).trans (s.centralizes_conjugate_line (c.gb:G))
  let e := MulAut.conj (c.gb:G)
  have hCG : centralizer (c.Aone V₁ : Set G) ≤ H.map e.toMonoidHom := by
    intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [hH]
    apply mem_centralizer_iff.mpr
    intro z hz
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    exact mem_centralizer_iff.mp hx (e z) (mem_map_of_mem e.toMonoidHom hz)
  have hn : centralizer (c.Aone V₁ : Set G) ≤ normalizer (c.Ugamma V₃ : Set G) := by
    have hm := map_mono (f := e.toMonoidHom) s.normalizes
    rw [map_equiv_normalizer_eq] at hm
    exact hCG.trans hm
  have hnA : C ≤ normalizer (A : Set _) :=
    (map_mono ((comap_mono hn).trans ((c.Ugamma V₃).le_normalizer_comap H.subtype))).trans
      (((c.Ugamma V₃).subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))
  have hrange : commutator (Model (ZMod 2)) ≤ f.range := by
    intro a ha
    let E := (Components.componentStarEquiv H K hKH hK).symm.trans eK
    refine ⟨E.symm ⟨a,ha⟩, ?_⟩
    rw [hfK]
    exact congrArg Subtype.val (E.apply_symm_apply ⟨a,ha⟩)
  let : IsElementaryAbelian 2 A := hA.2
  exact ⟨hr,hAU,Natural.BinaryPointFlag.exists_compatible_point_marking
    ρ f hf hrange p hp he C A hAC hnA (s.quotient t).toAdd hv0 hC⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic

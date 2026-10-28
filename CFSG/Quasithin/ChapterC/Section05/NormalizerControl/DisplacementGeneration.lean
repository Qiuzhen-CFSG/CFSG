module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.ReducedSpan
public import Theory.Representation.NormalClosureDisplacement

/-!
# Conjugate displacements generate the original A₃ source module

A T₁-actor moving U₁ has a nonzero displacement inside U₁. The
irreducibility of the actual A₃ four-group makes its K₁-span all of
U₁, and its X-span is the original V. Passing to the canonical
centralizer-quotient action identifies these group displacements
with the linear span required by G.6.1. This removes that generation
premise in the application of G.6.4 at C.5.12, printed p.163.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem alternating_three_span_of_nontrivial
    {T K : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (E : Subgroup G) (hEU : E ≤ U K) (hE : E ≠ ⊥) :
    conjugateSpanBy E K = U K := by
  let W := conjugateSpanBy E K
  have hUK : U K ≤ K := map_subtype_le _
  have hKU : K ≤ normalizer (U K : Set G) := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hWU : W ≤ U K := conjugateSpanBy_le hEU hKU
  have hWK : W ≤ K := hWU.trans hUK
  have hWneq : W ≠ ⊥ := fun he => hE (bot_unique (he ▸ le_conjugateSpanBy _ _))
  have hWn : (W.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWK).mpr (le_normalizer_conjugateSpanBy _ _)
  have hl : blockU K ⊓ center K = ⊥ := by
    apply bot_unique
    intro k hk
    have hh : (⟨k,hk.1⟩ : blockU K) ∈ blockFixed K := hk.2
    rw [alternatingThreeCoverInput K ha] at hh
    exact congrArg Subtype.val hh
  have hu : W.subgroupOf K ≤ blockU K := by
    intro k hk
    obtain ⟨u,hu,he⟩ := hWU hk
    have he' : u = k := Subtype.ext he
    exact he' ▸ hu
  obtain hw | hw := h.short.irreducible.2 (W.subgroupOf K) hWn (hl ▸ bot_le) hu
  · exact (hWneq (by rw [← map_subgroupOf_eq_of_le hWK,hw,hl,Subgroup.map_bot])).elim
  · change W = U K
    rw [← map_subgroupOf_eq_of_le hWK,hw]
    rfl

private theorem displacement_span_stable
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (a g : D) {v : W}
    (hv : v ∈ conjugateDisplacementSpan ρ a ⊤) :
    ρ g v ∈ conjugateDisplacementSpan ρ a ⊤ := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨d,_,w,rfl⟩ := hv
    exact Submodule.subset_span ⟨g*d,mem_top _,w,by rw [map_mul,Module.End.mul_apply]⟩
  | zero => simp
  | add v w _ _ hv hw => simpa using (conjugateDisplacementSpan ρ a ⊤).add_mem hv hw
  | smul c v _ hv => simpa using (conjugateDisplacementSpan ρ a ⊤).smul_mem c hv

omit [Finite G] in
/-- Every actor in T moving U generates the full X-span through its
conjugate displacements in the canonical quotient action. -/
theorem alternating_three_displacement_generates
    {T K : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G))
    (X V : Subgroup G) (hKX : K ≤ X) (hVX : V ≤ X)
    (hXV : X ≤ normalizer (V : Set G)) [IsElementaryAbelian 2 V]
    (hV : V = conjugateSpanBy (U K) X)
    (b : X) (hbT : (b : G) ∈ T) (hbC : (b : G) ∉ centralizer (U K : Set G)) :
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
    let : IsElementaryAbelian 2 (V.subgroupOf X) := IsElementaryAbelian.subgroupOf hVX
    conjugateDisplacementSpan (Representation.centralizerQuotient (V.subgroupOf X))
      (QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X)) b) ⊤ = ⊤ := by
  let Vi := V.subgroupOf X
  let : Vi.Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let : IsElementaryAbelian 2 Vi := IsElementaryAbelian.subgroupOf hVX
  let q := QuotientGroup.mk' (centralizer (Vi : Set X))
  let ρ := Representation.centralizerQuotient Vi
  let W := conjugateDisplacementSpan ρ (q b) ⊤
  let W₀ := W.toAddSubgroup.toSubgroup'
  let Wi := W₀.map Vi.subtype
  let A := Wi.map X.subtype
  have hmem (v : Additive Vi) : ((v.toMul : X) : G) ∈ A ↔ v ∈ W := by
    constructor
    · rintro ⟨x,⟨w,hw,he⟩,hex⟩
      have hew : w=v.toMul := Subtype.ext (Subtype.ext (hex ▸ congrArg X.subtype he))
      change Additive.ofMul w ∈ W at hw
      rw [hew] at hw
      exact hw
    · intro hv
      exact ⟨v.toMul.val,⟨v.toMul,hv,rfl⟩,rfl⟩
  have hnormal : Wi.Normal := by
    constructor
    rintro y ⟨v,hv,rfl⟩ g
    exact ⟨(ρ (q g) (Additive.ofMul v)).toMul,
      displacement_span_stable ρ (q b) (q g) hv,Representation.centralizerQuotient_apply Vi g _⟩
  let := hnormal
  have hXA : X ≤ normalizer (A : Set G) := by
    have hh := Wi.le_normalizer_map X.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  have hUV : U K ≤ V := hV ▸ le_conjugateSpanBy _ _
  have hbU : (b : G) ∈ normalizer (U K : Set G) :=
    (normalizer_le_normalizer_characteristic_image K (blockU K)) (hTK hbT)
  have hE : U K ⊓ A ≠ ⊥ := by
    intro hz
    apply hbC
    intro u hu
    let v : Additive Vi := Additive.ofMul ⟨⟨u,hVX (hUV hu)⟩,hUV hu⟩
    have hd : ⁅(b : G),u⁆ ∈ A := by
      have hh : ρ (q b) v-v ∈ W := Submodule.subset_span ⟨1,mem_top _,v,by simp⟩
      have hh' := (hmem (ρ (q b) v-v)).mpr hh
      change (((ρ (q b) v).toMul : X) : G) / u ∈ A at hh'
      have he := congrArg X.subtype (Representation.centralizerQuotient_apply Vi b v)
      change (((ρ (q b) v).toMul : X) : G) = (b : G)*u*(b : G)⁻¹ at he
      simpa only [he,div_eq_mul_inv,commutatorElement_def] using hh'
    have hdU : ⁅(b : G),u⁆ ∈ U K :=
      (mem_normalizer_iff.mp hbU u).mp hu |> fun hconj => (U K).mul_mem hconj ((U K).inv_mem hu)
    have he : ⁅(b : G),u⁆=1 := by
      simpa only [hz,mem_bot] using (show ⁅(b : G),u⁆ ∈ U K ⊓ A from ⟨hdU,hd⟩)
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  have hUA : U K ≤ A := by
    rw [← alternating_three_span_of_nontrivial h ha (U K ⊓ A) inf_le_left hE]
    exact conjugateSpanBy_le inf_le_right (hKX.trans hXA)
  have hVA : V ≤ A := hV ▸ conjugateSpanBy_le hUA hXA
  dsimp only
  apply top_unique
  intro v _
  exact (hmem v).mp (hVA v.toMul.property)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl

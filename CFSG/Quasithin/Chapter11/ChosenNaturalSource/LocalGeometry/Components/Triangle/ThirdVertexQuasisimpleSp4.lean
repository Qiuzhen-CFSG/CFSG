module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ThirdVertexSylowSp4
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ThirdVertexMathieu
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ThirdVertexJankoFour
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift

/-!
# Quasisimplicity and the remaining symplectic third-vertex models

The explicit nontrivial common normal Q puts IT inside its two-local
normalizer. The actual SQTK hypothesis and three-rank two therefore make
I/O₂(I) quasisimple. A quasisimple group with trivial two-core cannot have an
SL₂(5) quotient: its kernel would be central, while a central surjection maps
the two-core onto the nontrivial central involution of SL₂(5). This excludes
the nilpotent extension row without imposing a false rank bound on arbitrary
odd nilpotent extensions.

The literal consumer combines this with the two marked-local comparisons
for M₂₂, its triple cover and J₄. Only SL₃(4), Sp₄(4), G₂(4) and M₂₃ remain.
It preserves both original local sections, their quotient maps, full flag
and module data, and the explicit common Q. This is not source 11.1.2:
M₂₃, common-normal existence, the source SL₃(4) exclusion, maximal-faithful
placement and both orientations still belong to
qt-d-1222-natural-relative-components. Earlier flag and Cartan inputs retain
their existing producers and final discharge by
qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith, A.3.6, A.3.14 and 11.1.2,
printed pp.43--49,762--764, combined manuscript of 1 March 2004.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open FiveLocalFF.SolvableQuotients
public noncomputable section

open scoped MatrixGroups

/-- A quasisimple group with trivial two-core has no quotient onto SL₂(5). -/
theorem quasisimple_not_sl_two_five_quotient
    {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (hO : pCore 2 A = ⊥) (N : Subgroup A) [N.Normal] :
    ¬ Source.IsSL (A ⧸ N) 2 5 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hF,ZMod.card])
  let b := e.trans (GorensteinWalter.sl2RingEquiv a)
  let f := b.toMonoidHom.comp (QuotientGroup.mk' N)
  have hf : Function.Surjective f := b.surjective.comp (QuotientGroup.mk'_surjective N)
  have hz : orderOf (-1 : SL(2,ZMod 5)) = 2 :=
    Matrix.SpecialLinearGroup.orderOf_neg_one_eq_two (by decide)
  have hker : f.ker ≤ center A := by
    apply (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right
    intro ht
    obtain ⟨x,hx⟩ := hf (-1)
    have he : f x = 1 := by
      have hh : f = 1 := MonoidHom.ker_eq_top_iff.mp ht
      rw [hh]
      rfl
    rw [hx.symm.trans he,orderOf_one] at hz
    norm_num at hz
  have hm := f.map_pCore_of_central_kernel (p := 2) hf hker
  rw [hO,Subgroup.map_bot] at hm
  let Z := zpowers (-1 : SL(2,ZMod 5))
  have hZc : Z ≤ center SL(2,ZMod 5) := by
    apply zpowers_le.mpr
    exact mem_center_iff.mpr fun x => by simp
  have hZn : Z.Normal := ⟨fun x hx g => by
    have hc := mem_center_iff.mp (hZc hx) g
    rw [hc]
    simpa [mul_assoc] using hx⟩
  have hZp : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hz,pow_one])
  have hle : Z ≤ pCore 2 SL(2,ZMod 5) := le_sSup ⟨hZn,hZp⟩
  have he : (-1 : SL(2,ZMod 5)) = 1 := mem_bot.mp (hm ▸ hle (mem_zpowers _))
  rw [he,orderOf_one] at hz
  norm_num at hz

/-- The actual SQTK overgroup and relative C-component supply quasisimplicity
of the original two-core quotient at cubic rank two. -/
theorem relative_quotient_quasisimple_of_three_rank
    {G : Type*} [Group G] [Finite G] {H I : Subgroup G}
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hI : Source.ComponentIn H I) (hr : 2 ≤ primeRank 3 I) :
    IsQuasisimple (I ⧸ pCore 2 I) := by
  let e := subgroupOfEquivOfLe hI.1
  have hr' : 2 ≤ primeRank 3 (I.subgroupOf H) := by
    rwa [primeRank_congr 3 e]
  let := cComponent_twoCore_quasisimple_of_three_rank hH hI.2 hr'
  exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))

open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource Representation
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))

/-- The original common-Q construction, relative SQTK hypotheses and both
marked locals exclude M₂₂, its cover, J₄ and the nilpotent extension row.
M₂₃ and the subsequent source geometry still require their own comparisons. -/
theorem sp4_triangle_join_reduced_models_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    let A := I ⧸ pCore 2 I
    IsQuasisimple A ∧
      (Source.IsSL A 3 4 ∨ Source.IsSp A 2 4 ∨ ClassificationModels.IsG2At A 4 ∨
        Nonempty (A ≃* Sporadic.Mathieu.M23)) := by
  intro I A
  obtain ⟨hI,hIL,_,_,hr,_,hmark⟩ := sp4_triangle_marked_locals_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨hb,_,_,hmb,_,_⟩ := hmark K₀ (.inl rfl)
  obtain ⟨hc,_,_,hmc,_,_⟩ := hmark (f.Li 1) (.inr rfl)
  have hm22 := local_join_not_m22 T hK₀.1
    (flag_mem_local_of_model D S f 1 hm₂).1 hIL.1 hb.le hc.le hTK₀
    (f.sylow_normalizes_Li 1) rfl hmb hmc
  have hj4 := local_join_not_j4 T hK₀.1
    (flag_mem_local_of_model D S f 1 hm₂).1 hIL.1 hb.le hc.le hTK₀
    (f.sylow_normalizes_Li 1) rfl hmb hmc
  let H := I ⊔ (T : Subgroup G)
  have hHN : H ≤ normalizer (Q : Set G) := sup_le (sup_le hKQ hLQ) hTQ
  have hN := S.source.simpleQTKE.twoLocal_sqtk ⟨Q,hQ,T.isPGroup'.to_le hQT,rfl⟩
  have hH : IsSQTK KnownSimple.IsKnownSimple H := by
    let e := (subgroupOfEquivOfLe hHN).symm
    have hh := hN.subgroup (H.subgroupOf (normalizer (Q : Set G)))
    exact ⟨hh.stronglyQuasithin.of_injective e.toMonoidHom e.injective,
      hh.isKGroup.of_injective e.toMonoidHom e.injective⟩
  have hquasi := relative_quotient_quasisimple_of_three_rank hH hI.1 hr.ge
  let := hquasi
  refine ⟨hquasi,?_⟩
  obtain hm := sp4_triangle_join_sylow_sieve_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm
  · exact .inl hm
  · exact .inr (.inl hm)
  · exact .inr (.inr (.inl hm))
  · exact (hm22 (.inl hm)).elim
  · exact (hm22 (.inr hm)).elim
  · exact .inr (.inr (.inr hm))
  · exact (hj4 hm).elim
  · obtain ⟨N,hN,_,he⟩ := hm
    let := hN
    exact (quasisimple_not_sl_two_five_quotient (pCore_quotient_pCore_eq_bot 2) N he).elim

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle

module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ThirdVertexRecognitionSp4
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearCartanPlacement

/-!
# Recognition of the third vertex in the original linear branch

The two actual proper A₅ local sections, their common order-nine Cartan,
and the SQTK overgroup suffice for the third-vertex comparison independently
of the original natural-module model. The existing marked-local calculations
exclude triality, alternating and sporadic rows. Cubic rank excludes the
rank-one rows; relative quasisimplicity removes the odd extension. The
original Sylow intersection excludes PSL₃(4), leaving the three source models.

Apply this comparison to I = K₀ ∨ L₂ in the original SL₃(4) flag. The checked
Cartan placement and common-Q geometry discharge every marked-local premise;
the checked equality of the original cubic kernels excludes the remaining
SL₃(4) third vertex. Thus its quotient is Sp₄(4) or G₂(4), with original
relative normality, He membership and both three-ranks retained.

This does not exclude the original SL₃(4) vertex. The Weyl step is in
`LinearWeylEscape`. Common-normal existence, the module comparison, both final orientations and
full 11.1.1--3 remain with qt-d-1222-natural-relative-components. Earlier
source inputs retain their producers and final discharge by
qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith 11.1.2, printed pp.762--764, especially p.763,
and A.3.14. Imported model calculations retain their ATLAS attribution.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

private theorem no_prime_linear_of_three_rank_two
    {p : ℕ} (hp : p.Prime) (hr : 2 ≤ primeRank 3 G)
    (hm : ClassicalGroup.IsPSL G 2 p) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,hF,ZMod.card])
  have hb := Theory.PSL2.primeField_odd_rank (p := p) (r := 3) (by decide)
  rw [primeRank_congr 3 (e.trans (GorensteinWalter.psl2RingEquiv a))] at hr
  exact (by decide : ¬ (2 ≤ 1)) (hr.trans hb)

private theorem no_twenty_five_of_three_rank_two (hr : 2 ≤ primeRank 3 G)
    (hm : ClassicalGroup.IsPSL G 2 25) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hc : Nat.card G = 7800 := by
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
      ⟨5,2,by decide,by decide,by decide,by simpa using hF⟩,hF]
    norm_num
  have hb : primeRank 3 G ≤ 1 := primeRank_le_of_prime_pow_not_dvd (by rw [hc]; decide)
  omega

private theorem no_janko_one_of_three_rank_two (hr : 2 ≤ primeRank 3 G)
    (hm : Nonempty (G ≃* Janko1.Model)) : False := by
  have hc : Nat.card G = 175560 := (Nat.card_congr hm.some.toEquiv).trans Janko1.card_model
  have hb : primeRank 3 G ≤ 1 := primeRank_le_of_prime_pow_not_dvd (by rw [hc]; decide)
  omega

/-- The marked two-residual comparison is independent of the original
natural-module model. Its quotient is the literal quotient of their join. -/
theorem marked_triangle_join_three_models
    (T : Sylow 2 G) {B C I X : Subgroup G}
    (hH : IsSQTK KnownSimple.IsKnownSimple (I ⊔ (T : Subgroup G) : Subgroup G))
    (hI : Source.ComponentIn (I ⊔ (T : Subgroup G)) I)
    (hIL : I ∈ Chapter1.L G T)
    (hB : B ∈ Chapter1.L G T) (hC : C ∈ Chapter1.L G T)
    (hBI : B < I) (hCI : C < I)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hgen : B ⊔ C = I)
    (hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4)
    (hXI : X ≤ I) (hXB : X ≤ normalizer (B : Set G))
    (hXC : X ≤ normalizer (C : Set G))
    (hXP : X ≤ normalizer (((T : Subgroup G) ⊓ C : Subgroup G) : Set G))
    (hcard : Nat.card X = 9) (hnot : ¬ X ≤ C)
    (hr : 2 ≤ primeRank 3 I) :
    let A := I ⧸ pCore 2 I
    IsQuasisimple A ∧
      (Source.IsSL A 3 4 ∨ Source.IsSp A 2 4 ∨ ClassificationModels.IsG2At A 4) := by
  intro A
  have hquasi := relative_quotient_quasisimple_of_three_rank hH hI hr
  let := hquasi
  have hrq : 2 ≤ primeRank 3 A := by
    rwa [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
  have htop : (⊤ : Subgroup I).IsCComponent := by
    simpa only [subgroupOf_self] using hI.2.subgroupOf_of_le le_rfl hI.1
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) := by
    rw [←hgen]
    exact (le_inf hTB hTC).trans (normalizer_inf_normalizer_le_normalizer_sup B C)
  have hpsl : ¬ ClassicalGroup.IsPSL A 3 4 := fun hm => hnot
    (odd_intersection_le_local T htop hTI hC.1 hCI hC.1 hCI hXI
      (by rw [hcard]; decide) hXP hm)
  have htriality := local_join_not_triality_four T hB.1 hC.1 hIL.1 hBI hCI hgen hmB hmC
  have hseven := local_join_not_seven T hB.1 hC.1 hIL.1 hBI.le hCI.le hgen hmB hmC
  have hunitary := local_join_not_unitary_five T hB.1 hC.1 hIL.1 hBI.le hCI.le
    hTB hTC hgen hmB hmC
  have hspor := local_quotient_not_three_sporadics T hB.1 hIL.1 hBI hTB hXI hXB hcard hmB
  have hm22 := local_join_not_m22 T hB.1 hC.1 hIL.1 hBI.le hCI.le hTB hTC hgen hmB hmC
  have hm23 := local_join_not_m23_of_marked_cartan T hB.1 hC.1 hIL.1 hBI.le hCI.le
    hTB hTC hgen hmB hmC hXI hXB hXC hcard
  have hj4 := local_join_not_j4 T hB.1 hC.1 hIL.1 hBI.le hCI.le hTB hTC hgen hmB hmC
  have hTH : (T : Subgroup G) ≤ I ⊔ (T : Subgroup G) := le_sup_right
  have hP : Chapter1.IsSylowIn 2 (T : Subgroup G) (I ⊔ (T : Subgroup G)) :=
    ⟨T.subtype hTH,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  have hc := Embedding.relative_component_alternative hH hP hC hI hCI.le hTC
    (n := 2) (by decide) (by simpa using hmC)
  refine ⟨hquasi,?_⟩
  cases hc with
  | equal he => exact (hCI.ne he).elim
  | lie hm =>
    cases hm with
    | sl3 hm => exact .inl hm
    | psl3 hm => exact (hpsl hm).elim
    | sp4 hm => exact .inr (.inl hm)
    | g2 hm => exact .inr (.inr hm)
    | triality hm => exact (htriality hm).elim
    | ree n hn he _ => omega
    | trialityCube n hn he _ => omega
  | four _ hm =>
    cases hm with
    | alternating he => exact (hseven (.inl he)).elim
    | alternatingCover he => exact (hseven (.inr he)).elim
    | primeLinear p hp he => exact (no_prime_linear_of_three_rank_two hp.1 hrq he).elim
    | linearTwentyFive he => exact (no_twenty_five_of_three_rank_two hrq he).elim
    | j1 he => exact (no_janko_one_of_three_rank_two hrq he).elim
    | three u he =>
      cases u with
      | false => exact (rank_two_not_linear_three_five hrq he).elim
      | true => exact (hunitary he).elim
    | m22 he => exact (hm22 (.inl he)).elim
    | m22Cover he => exact (hm22 (.inr he)).elim
    | m23 he => exact (hm23 he).elim
    | j4 he => exact (hj4 he).elim
    | j2 he => exact (hspor (.inl he)).elim
    | hs he => exact (hspor (.inr (.inl he))).elim
    | ru he => exact (hspor (.inr (.inr he))).elim
    | nilpotentExtension he =>
      obtain ⟨N,hN,_,he⟩ := he
      let := hN
      exact (quasisimple_not_sl_two_five_quotient (pCore_quotient_pCore_eq_bot 2) N he).elim
    | elementaryExtension p hp he => exact (rank_two_not_elementary_extension hrq hp he).elim

open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource Representation
variable {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The actual third vertex in the original SL₃(4) branch has symplectic
or G₂ quotient. Common-normal existence is retained; no model catalogue
or Cartan-placement hypothesis is added. -/
theorem linear_triangle_join_two_models_of_common_normal
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hgen : f.Li 0 ⊔ K₀ = K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    let A := I ⧸ pCore 2 I
    Source.NormalComponentIn (I ⊔ (T : Subgroup G)) I ∧
      I ∈ Chapter1.L G T ∧ I ∈ Chapter1.He G ∧ X ≤ I ∧
      primeRank 3 I = 2 ∧ primeRank 3 A = 2 ∧ IsQuasisimple A ∧
      (Source.IsSp A 2 4 ∨ ClassificationModels.IsG2At A 4) := by
  intro I A
  obtain ⟨hI,hIL,hIH,hXI,hr,hrq,hnot,hmark⟩ :=
    linear_triangle_geometry_of_common_normal D S m f hd hfix hX hK hLK hK₀ hK₀K
      hTK₀ hgen hk hp hcard hmove hQ hQT hTQ hKQ hLQ
  obtain ⟨hb,_,hXB,hmb,_,_⟩ := hmark K₀ (.inl rfl)
  obtain ⟨hc,_,hXC,hmc,_,_⟩ := hmark (f.Li 1) (.inr rfl)
  have hm : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,
      ⟨SL3.flagLocalCoreEquiv S m f 1⟩⟩
  have hCL := flag_mem_local_of_model D S f 1 hm
  have hXP : X ≤ normalizer (((T : Subgroup G) ⊓ f.Li 1 : Subgroup G) : Set G) := by
    have he : (T : Subgroup G) ⊓ f.Li 1 = ((T : Subgroup G) ⊓ L) ⊓ f.Li 1 :=
      le_antisymm
        (le_inf (le_inf inf_le_left (inf_le_right.trans ((localResidual_le _).trans inf_le_left)))
          inf_le_right)
        (inf_le_inf inf_le_left le_rfl)
    rw [he]
    exact (le_inf (hX.1.trans cartanNormalizer_normalizes_intersection) hXC).trans
      inf_normalizer_le_normalizer_inf
  have hcardX : Nat.card X = 9 := by
    rw [(Coordinates.sl3 m).cartan_card hX,hd]
    norm_num
  have hnotC := (linear_triangle_proper_residuals D S m f hd hX hK hLK hK₀ hK₀K hk hp).2.2.2
  let H := I ⊔ (T : Subgroup G)
  have hHN : H ≤ normalizer (Q : Set G) := sup_le (sup_le hKQ hLQ) hTQ
  have hN := S.source.simpleQTKE.twoLocal_sqtk ⟨Q,hQ,T.isPGroup'.to_le hQT,rfl⟩
  have hH : IsSQTK KnownSimple.IsKnownSimple H := by
    let e := (subgroupOfEquivOfLe hHN).symm
    have hh := hN.subgroup (H.subgroupOf (normalizer (Q : Set G)))
    exact ⟨hh.stronglyQuasithin.of_injective e.toMonoidHom e.injective,
      hh.isKGroup.of_injective e.toMonoidHom e.injective⟩
  obtain ⟨hq,hmodels⟩ := marked_triangle_join_three_models T hH hI.1 hIL hK₀ hCL hb hc
    hTK₀ (f.sylow_normalizes_Li 1) rfl hmb hmc hXI hXB hXC hXP hcardX hnotC hr.ge
  exact ⟨hI,hIL,hIH,hXI,hr,hrq,hq,hmodels.resolve_left hnot⟩

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle

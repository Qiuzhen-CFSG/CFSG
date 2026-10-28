module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ThirdVertexRecognitionSp4

/-!
# The three quotient models of the original G₂ third vertex

The same Cartan and the two local PSL₂(4) sections constructed from the
original common normal Q feed the full 11.1.1 embedding catalogue. Cubic
rank and the marked local comparisons remove the exceptional rows. Every
comparison uses I = K₀ ∨ L₂ and its entire intrinsic two-core.
Source: Aschbacher--Smith, 11.1.2, printed pp.762--764.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
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

omit [Finite G] in
private theorem sylow_intersection_normalized
    {T : Sylow 2 G} {L B X : Subgroup G}
    (hX : IsCartan T L X) (hBL : B ≤ L)
    (hXB : X ≤ normalizer (B : Set G)) :
    X ≤ normalizer (((T : Subgroup G) ⊓ B : Subgroup G) : Set G) := by
  have he : (T : Subgroup G) ⊓ B = ((T : Subgroup G) ⊓ L) ⊓ B := by
    exact le_antisymm (le_inf (le_inf inf_le_left (inf_le_right.trans hBL)) inf_le_right)
      (inf_le_inf inf_le_left le_rfl)
  rw [he]
  exact (le_inf (hX.1.trans cartanNormalizer_normalizes_intersection) hXB).trans
    inf_normalizer_le_normalizer_inf

variable {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (.g2 m))

/-- The projective quotient is excluded by the original Sylow intersection. -/
theorem g2_triangle_not_psl3
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hI : Source.ComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1)) :
    ¬ ClassicalGroup.IsPSL ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 3 4 := by
  obtain ⟨_,hlt,_,hn⟩ := g2_triangle_proper_residuals D S m f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hXN : X ≤ normalizer (f.Li 1 : Set G) := by
    have hx : X ≤ L ⊓ normalizer (f.Vi 1 : Set G) :=
      le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX 1)
    exact (hx.trans (L ⊓ normalizer (f.Vi 1 : Set G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have htop : (⊤ : Subgroup (K₀ ⊔ f.Li 1 : Subgroup G)).IsCComponent := by
    simpa only [subgroupOf_self] using hI.2.subgroupOf_of_le le_rfl hI.1
  have hTI : (T : Subgroup G) ≤ normalizer ((K₀ ⊔ f.Li 1 : Subgroup G) : Set G) :=
    (le_inf hTK₀ (f.sylow_normalizes_Li 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup K₀ (f.Li 1))
  intro hi
  exact hn (odd_intersection_le_local T htop hTI
    (flag_mem_local_of_model D S f 1 hm₂).1 hlt
    (flag_mem_local_of_model D S f 1 hm₂).1 hlt
    (g2_triangle_cartan_le_join D S m f hu hm₁ hfour hX hK hLK hK₀ hK₀K hk hp)
    hX.odd (sylow_intersection_normalized hX ((localResidual_le _).trans inf_le_left) hXN) hi)

/-- The common-Q join has the full three-model conclusion, with no quotient catalogue premise. -/
theorem g2_triangle_join_three_models_of_common_normal
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
      (Source.IsSL A 3 4 ∨ Source.IsSp A 2 4 ∨ ClassificationModels.IsG2At A 4) := by
  intro I A
  obtain ⟨hI,hIL,_,hXI,hr,hrq,hmark⟩ := g2_triangle_marked_locals_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨hb,hbX,hXb,hmb,_,_⟩ := hmark K₀ (.inl rfl)
  obtain ⟨hc,_,hXc,hmc,_,_⟩ := hmark (f.Li 1) (.inr rfl)
  have hB := (flag_mem_local_of_model D S f 1 hm₂).1
  have hcx : Nat.card X = 9 := by
    rw [(Coordinates.g2 m).cartan_card hX,hfour]
    norm_num
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
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hP : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  have hcases := Embedding.relative_component_alternative hH hP
    (flag_mem_local_of_model D S f 1 hm₂) hI.1 le_sup_right
    (f.sylow_normalizes_Li 1) S.nonbinary hm₂
  rw [hfour] at hcases
  cases hcases with
  | equal he => exact (hc.ne he).elim
  | lie hm =>
    cases hm with
    | sl3 hm => exact .inl hm
    | sp4 hm => exact .inr (.inl hm)
    | g2 hm => exact .inr (.inr hm)
    | psl3 hm => exact (g2_triangle_not_psl3 D S m f hu hm₁ hm₂ hfour
        hX hK hLK hK₀ hK₀K hTK₀ hk hp hI.1 hm).elim
    | triality hm => exact (local_join_not_triality_four T hK₀.1 hB hIL.1
        hb hc rfl hmb hmc hm).elim
    | ree n hn he _ => omega
    | trialityCube n hn he _ => omega
  | four _ hm =>
    have hseven := local_join_not_seven T hK₀.1 hB hIL.1 hb.le hc.le rfl hmb hmc
    have hunitary := local_join_not_unitary_five T hK₀.1 hB hIL.1 hb.le hc.le hTK₀
      (f.sylow_normalizes_Li 1) rfl hmb hmc
    have hspor := local_quotient_not_three_sporadics T hK₀.1 hIL.1 hb hTK₀
      hXI hXb hcx hmb
    have hm22 := local_join_not_m22 T hK₀.1 hB hIL.1 hb.le hc.le hTK₀
      (f.sylow_normalizes_Li 1) rfl hmb hmc
    have hj4 := local_join_not_j4 T hK₀.1 hB hIL.1 hb.le hc.le hTK₀
      (f.sylow_normalizes_Li 1) rfl hmb hmc
    cases hm with
    | alternating he => exact (hseven (.inl he)).elim
    | alternatingCover he => exact (hseven (.inr he)).elim
    | primeLinear p hp he => exact (no_prime_linear_of_three_rank_two hp.1 hrq.ge he).elim
    | linearTwentyFive he => exact (no_twenty_five_of_three_rank_two hrq.ge he).elim
    | j1 he => exact (no_janko_one_of_three_rank_two hrq.ge he).elim
    | three u he =>
      cases u with
      | false => exact (rank_two_not_linear_three_five hrq.ge he).elim
      | true => exact (hunitary he).elim
    | m22 he => exact (hm22 (.inl he)).elim
    | m22Cover he => exact (hm22 (.inr he)).elim
    | m23 he => exact (local_join_not_m23_of_marked_cartan T hK₀.1 hB hIL.1
        hb.le hc.le hTK₀ (f.sylow_normalizes_Li 1) rfl hmb hmc hXI hXb hXc hcx he).elim
    | j4 he => exact (hj4 he).elim
    | j2 he => exact (hspor (.inl he)).elim
    | hs he => exact (hspor (.inr (.inl he))).elim
    | ru he => exact (hspor (.inr (.inr he))).elim
    | nilpotentExtension he =>
      obtain ⟨N,hN,_,he⟩ := he
      let := hN
      exact (quasisimple_not_sl_two_five_quotient (pCore_quotient_pCore_eq_bot 2) N he).elim
    | elementaryExtension p hp he => exact (rank_two_not_elementary_extension hrq.ge hp he).elim

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation

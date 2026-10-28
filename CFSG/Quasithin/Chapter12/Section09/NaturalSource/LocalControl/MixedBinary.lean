module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.MatchingBinary
public import Theory.SpecificGroups.BinaryLinear.FivePointSection

/-!
# The literal mixed point-parabolic section

If n=4 and the point component has PSL₅(2) quotient, failure of plane
movement makes the core of K₁T centralize V. The full original point
parabolic action therefore descends to the image J of L₁T in
K₁T/O₂(K₁T). Its kernel is exactly the image of Q=O₂(LT), and its
restriction to the original elements is still conjugation on V.

The full-Sylow order calculation gives |J|=21504 and kernel order16,
and identifies J with one of the three flags with a three-dimensional
Levi block. The original L₁ maps to O²(J). Uniqueness of the maximal
two-local over LT gives N_G(Q)≤N_G(L); pulling the quotient normalizer
back consequently proves that the kernel normalizer normalizes this
literal O²(J) image.

The final theorem applies the complete matching and A₇ movement proofs
to LocalControl, retaining only this mixed configuration as an alternative.
It does not exclude that configuration or establish LocalControlInput.
The model normalizer comparison, source centralizer/model bounds and
component/abelianity arguments remain with qt-d-1291-natural-source.

Source: Aschbacher--Smith,12.9.5(3) and12.9.6, printed pp.860--862
of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag Section08.NormalGeometry
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}

variable {n : ℕ}

/-- The exact mixed quotient obstruction, constructed from a failure of movement.
It retains the original action, core image and residual, rather than merely their orders. -/
@[expose] def MixedPointSection [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) : Prop :=
  ∃ e : ((C.K1 ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (C.K1 ⊔ (T : Subgroup G) : Subgroup G)) ≃* LinearGroup 5,
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (C.K1 ⊔ (T : Subgroup G) : Subgroup G)))
      let B := F.Li L 1 ⊔ (T : Subgroup G)
      let r := q.comp (inclusion (sup_le_sup_right C.contains (T : Subgroup G)))
      let J := r.range
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∃ a : J →* BinaryLinear.parabolic (space (V := V) (F.Vi 1)),
        Function.Surjective a ∧
        (∀ (b : B) (v : Additive V),
          (((a (r.rangeRestrict b)).val v).toMul : G) =
            (b : G) * (v.toMul : G) * (b : G)⁻¹) ∧
        a.ker = (Q.subgroupOf B).map r.rangeRestrict ∧
        IsPGroup 2 a.ker ∧
        ((F.Li L 1).subgroupOf B).map r = (pResidual 2 J).map J.subtype ∧
        normalizer (a.ker.map J.subtype : Set (LinearGroup 5)) ≤
          normalizer (((F.Li L 1).subgroupOf B).map r : Set (LinearGroup 5)) ∧
        Nat.card J = 21504 ∧ Nat.card a.ker = 16 ∧
        (∃ b : FiveBasis, J = flagStabilizer b {0,1} ∨
          J = flagStabilizer b {0,3} ∨ J = flagStabilizer b {2,3})

/-- Failure of movement in the mixed row constructs the literal binary section. -/
theorem mixed_plane_fixed_section
    (h : HigherRankHypothesis K T L V 4) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V 4) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2)
    (hfix : ⁅F.Vi 2,C.K1.pCoreIn 2⁆ = ⊥) :
    letI := h.chosen.elementary
    MixedPointSection F C := by
  let := h.chosen.elementary
  have hc := (core_centralizes_point_span_of_plane_fixed h F C hfix).trans
    (centralizer_le (le_conjugateSpanBy V F.H))
  have hR := join_core_centralizes_of_component_core_centralizes h (by decide) earlier F C hc
  let X := C.K1 ⊔ (T : Subgroup G)
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hBX : B ≤ X := sup_le_sup_right C.contains _
  have hBL : B ≤ L ⊔ (T : Subgroup G) :=
    sup_le_sup_right ((F.Li_le L 1).trans inf_le_left) _
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hh
  obtain ⟨k,_,_,hcard,⟨e₀⟩⟩ := hm
  let ek := Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo k hcard
  let eK := (e₀.trans (Atlas.fieldEquivPSL 5 ek)).trans (projectiveEquivLinear (by decide : 0<5))
  have hz : center (C.K1 ⧸ pCore 2 C.K1) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    let eS := eK.trans (slEquivLinear 5).symm
    have he : eS x ∈ center (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
      (centerCongr eS ⟨x,hx⟩).property
    rw [binary_center_eq_bot (by decide),mem_bot] at he
    exact mem_bot.mpr (eS.map_eq_one_iff.mp he)
  let hTN := (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)
  have hi := binary_sylow_acts_inner h (Or.inl rfl) earlier F C (Or.inr rfl)
    (show ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2 from ⟨k,inferInstance,inferInstance,hcard,⟨e₀⟩⟩)
  let e := (pCoreJoinQuotientEquivOfInner C.K1 (T : Subgroup G) hTN T.isPGroup' hz hi).trans eK
  refine ⟨e,?_⟩
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let : Finite (LinearGroup 5) := Finite.of_surjective q hq
  have hqk : q.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let S := (T.subtype hTX).mapSurjective (f := q) hq
  let r := q.comp (inclusion hBX)
  let J := r.range
  obtain ⟨a₀,hak,has,hact⟩ := point_join_conjugation_action h (by decide) earlier F
  have hsurj : Function.Surjective a₀ := by
    intro x
    obtain ⟨l,hl⟩ := has x
    exact ⟨inclusion le_sup_left l,hl⟩
  have haQ : a₀.ker = Q.subgroupOf B := by
    rw [hak]
    ext b
    change (b : G) ∈ centralizer (V : Set G) ↔ (b : G) ∈ Q
    constructor
    · intro hb
      change (b : G) ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2
      rw [← h.centralizer_LT earlier.structural]
      exact ⟨hBL b.property,hb⟩
    · intro hb
      exact h.chosen.core_centralizes hb
  have hk : r.ker ≤ a₀.ker := by
    intro b hb
    have hx : inclusion hBX b ∈ q.ker := hb
    rw [hqk] at hx
    rw [hak]
    exact hR (mem_map.mpr ⟨_,hx,rfl⟩)
  let er := QuotientGroup.quotientKerEquivRange r
  let a := (QuotientGroup.lift r.ker a₀ hk).comp er.symm.toMonoidHom
  have ha : Function.Surjective a :=
    (QuotientGroup.lift_surjective_of_surjective r.ker a₀ hsurj hk).comp er.symm.surjective
  have hae (b : B) : a (r.rangeRestrict b) = a₀ b := by
    change QuotientGroup.lift r.ker a₀ hk (er.symm (er (QuotientGroup.mk' r.ker b))) = a₀ b
    rw [er.symm_apply_apply]
    rfl
  have hak' : a.ker = (Q.subgroupOf B).map r.rangeRestrict := by
    ext j
    obtain ⟨b,rfl⟩ := r.rangeRestrict_surjective j
    constructor
    · intro hj
      have hb : b ∈ a₀.ker := (hae b).symm.trans hj
      exact mem_map.mpr ⟨b,haQ ▸ hb,rfl⟩
    · rintro ⟨c,hc,he⟩
      change a (r.rangeRestrict b) = 1
      rw [← he,hae]
      exact (haQ.symm ▸ hc : c ∈ a₀.ker)
  have hp : IsPGroup 2 a.ker := hak'.symm ▸
    (((isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).comap_subtype).map r.rangeRestrict)
  have hSJ : (S : Subgroup (LinearGroup 5)) ≤ J := by
    rintro _ ⟨t,ht,rfl⟩
    exact ⟨⟨t,mem_sup_right ht⟩,rfl⟩
  have hBres : pResidual 2 B = (F.Li L 1).subgroupOf B := by
    let A := (F.Li L 1).subgroupOf B
    let : A.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le (F.Li L 1).le_normalizer (sylow_normalizes_point_residual h earlier F))
    let eA := subgroupOfEquivOfLe (show F.Li L 1 ≤ B from le_sup_left)
    have hpA : IsPPerfect 2 A := (Components.Li_twoPerfect F 1).of_surjective
      eA.symm.toMonoidHom eA.symm.surjective
    apply pResidual_eq_of_isPPerfect_sup A ((T : Subgroup G).subgroupOf B) hpA
      T.isPGroup'.comap_subtype
    rw [← subgroupOf_sup (show F.Li L 1 ≤ B from le_sup_left)
      (show (T : Subgroup G) ≤ B from le_sup_right),subgroupOf_self]
  have hres : ((F.Li L 1).subgroupOf B).map r = (pResidual 2 J).map J.subtype := by
    rw [← map_pResidual_of_surjective 2 r.rangeRestrict r.rangeRestrict_surjective,
      hBres,map_map]
    rfl
  have hQX : Q ≤ X := hQT.trans hTX
  have hQimage : a.ker.map J.subtype = (Q.subgroupOf X).map q := by
    rw [hak',map_map]
    ext z
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨inclusion hBX b,hb,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,mem_sup_right (hQT hx)⟩,hx,rfl⟩
  have hRQ : q.ker ≤ Q.subgroupOf X := by
    rw [hqk]
    intro x hx
    have hxR : (x : G) ∈ X.pCoreIn 2 := mem_map.mpr ⟨x,hx,rfl⟩
    have hRT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
      have hh := pCoreIn_le_sylow X (T.subtype hTX)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX] using hh
    change (x : G) ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [← h.centralizer_LT earlier.structural]
    exact ⟨mem_sup_right (hRT hxR),hR hxR⟩
  have hNQ : normalizer (Q : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hJN
      exact Set.mem_singleton_iff.mp ((h.maximal_unique earlier.structural earlier.uniqueness).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} from ⟨hN,hJN⟩)
    · exact isPGroup_pCoreIn 2 _
    · intro hz
      exact h.chosen.ne_bot (le_bot_iff.mp (hz ▸ h.chosen.le_core))
    · exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hLN : F.H ⊓ normalizer (L : Set G) ≤ normalizer (F.Li L 1 : Set G) := by
    have hh : F.H ⊓ normalizer (L : Set G) ≤ normalizer (L ⊓ F.H : Subgroup G) :=
      (le_inf inf_le_right (inf_le_left.trans F.H.le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    dsimp only [Li]
    rw [if_neg (by decide)]
    let : (pResidual 2 (L ⊓ F.H : Subgroup G)).Characteristic := by
      apply characteristic_iff_map_eq.mpr
      intro a
      exact map_pResidual_of_surjective 2 a.toMonoidHom a.surjective
    exact hh.trans (normalizer_le_normalizer_characteristic_image
      (L ⊓ F.H) (pResidual 2 (L ⊓ F.H : Subgroup G)))
  have hJimage : ((F.Li L 1).subgroupOf B).map r =
      ((F.Li L 1).subgroupOf X).map q := by
    ext z
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨inclusion hBX b,hb,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,mem_sup_left hx⟩,hx,rfl⟩
  have hnimage : normalizer (a.ker.map J.subtype : Set (LinearGroup 5)) ≤
      normalizer (((F.Li L 1).subgroupOf B).map r : Set (LinearGroup 5)) := by
    rw [hQimage,hJimage]
    intro z hz
    obtain ⟨x,rfl⟩ := hq z
    have hx : x ∈ normalizer (Q.subgroupOf X : Set X) := by
      have hx' : x ∈ (normalizer ((Q.subgroupOf X).map q : Set (LinearGroup 5))).comap q := hz
      rwa [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hRQ] at hx'
    have hxN : (x : G) ∈ normalizer (Q : Set G) := by
      rwa [← subgroupOf_normalizer_eq hQX] at hx
    have hxL : (x : G) ∈ normalizer (F.Li L 1 : Set G) :=
      hLN ⟨(sup_le C.point_le (F.invariant 1)) x.property,hNQ hxN⟩
    have hx' : x ∈ normalizer ((F.Li L 1).subgroupOf X : Set X) := by
      rw [← subgroupOf_normalizer_eq (C.contains.trans le_sup_left)]
      exact hxL
    exact ((F.Li L 1).subgroupOf X).le_normalizer_map q (mem_map_of_mem q hx')
  have hP : Nat.card (BinaryLinear.parabolic (space (V := V) (F.Vi 1))) = 1344 := by
    rw [BinaryLinear.PointStabilizerPerfect.parabolic_card _
      (Components.flag_space_finrank F 1 (by decide))]
    have hv : Module.finrank (ZMod 2) (Additive V) = 4 :=
      h.naturalMarking.coordinates.finrank_eq.trans (by simp)
    rw [hv]
    have h3 : Nat.card (LinearGroup 3) = 168 := by
      rw [← Nat.card_congr (matrixEquivLinear 3).toEquiv,Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]
    norm_num [h3]
  obtain ⟨hJ,hka,hflag⟩ := BinaryLinear.FivePointSection.section_geometry S J hSJ a ha hp hP
  exact ⟨a,ha,fun b v => by rw [hae]; exact hact b v,hak',hp,hres,hnimage,hJ,hka,hflag⟩

/-- The LocalControl consumer is complete unless the remaining mixed source
configuration occurs. All source maps and normalizer restrictions are retained
in that alternative; no model comparison is assumed. -/
theorem localControl_or_mixed_point_section
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G))
    (hmodels : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    LocalControl C ∨ (n = 4 ∧ letI := h.chosen.elementary; MixedPointSection F C) := by
  by_cases hm : ⁅F.Vi 2,C.K1.pCoreIn 2⁆ = ⊥
  · obtain ⟨rfl,h5⟩ := point_movement_failure_is_mixed h hn earlier F C hcentral hmodels hm
    exact Or.inr ⟨rfl,mixed_plane_fixed_section h earlier F C h5 hm⟩
  · exact Or.inl (localControl_of_plane_centralizer_and_models h earlier F C hcentral hmodels hm hplane)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource

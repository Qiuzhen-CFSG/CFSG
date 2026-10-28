module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointOrder
public import Theory.SpecificGroups.BinaryLinear.PointParabolicSection
public import Theory.GroupTheory.PCoreQuotientInnerJoin

/-!
# Plane movement in the matching binary dimensions

Suppose the point component has PSLₙ(2) two-core quotient, with n=4 or5.
If its core fixes the original plane, it centralizes the point span and V.
The core of K₁T also centralizes V: its action commutes with the full point
parabolic, whose ambient centralizer is trivial.

The original L₁-action on V is the full point parabolic. Its image in the
literal K₁T/O₂(K₁T) quotient is normalized by the image of T. The binary
section theorem equates the two action kernels and places that Sylow image
inside the L₁-image. Consequently O₂(LT)=O₂(K₁T). Uniqueness then puts
K₁T inside M, contrary to its escape supplied by the source quotient-centralizer
bound. Thus the core moves the plane, and the existing plane-closure proof
supplies all three clauses of 12.9.6.

The actual LocalControl applications remove the movement premise in the
matching rows and, using the existing model comparison, in degree five.
Under the surviving source model list, every remaining failure is the mixed
n=4, PSL₅(2) case. That case, the centralizer bounds, model control and
component geometry remain with qt-d-1291-natural-source. No source bound
is supplied by a certificate or an additional movement hypothesis.

Source: Aschbacher--Smith, 12.9.6, printed pp.861--862 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag Section08.NormalGeometry
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

private def seedLinearAction [IsElementaryAbelian 2 V]
    (B : Subgroup G) (hBV : B ≤ normalizer (V : Set G)) :
    B →* BinaryLinear.GL (Additive V) :=
  let a : MulAut V →* BinaryLinear.GL (Additive V) :=
    { toFun := fun f => { f.toAdditive with map_smul' := ZMod.map_smul f.toAdditive }
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl }
  a.comp (setupSeedAction B V hBV)

omit [Finite G] in
private theorem seedLinearAction_ker [IsElementaryAbelian 2 V]
    (B : Subgroup G) (hBV : B ≤ normalizer (V : Set G)) :
    (seedLinearAction B hBV).ker = (centralizer (V : Set G)).subgroupOf B := by
  ext b
  change seedLinearAction B hBV b = 1 ↔ (b : G) ∈ centralizer (V : Set G)
  constructor
  · intro hb v hv
    have he := congrArg (fun a : BinaryLinear.GL (Additive V) => (a (Additive.ofMul ⟨v,hv⟩)).toMul.val) hb
    change (b : G) * v * (b : G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hb
    ext v
    change (b : G) * (v.toMul : G) * (b : G)⁻¹ = (v.toMul : G)
    rw [← hb v.toMul v.toMul.property,mul_inv_cancel_right]

/-- The full action of the original point residual extends to its Sylow join,
with the literal seed centralizer as kernel. -/
theorem point_join_conjugation_action
    (h : HigherRankHypothesis K T L V n) (hn : 4 ≤ n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) :
    letI := h.chosen.elementary
    ∃ a : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) →*
        BinaryLinear.parabolic (space (V := V) (F.Vi 1)),
      a.ker = (centralizer (V : Set G)).subgroupOf (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      Function.Surjective (a.comp (inclusion le_sup_left)) ∧
      ∀ (b : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)) (v : Additive V),
        (((a b).val v).toMul : G) = (b : G) * (v.toMul : G) * (b : G)⁻¹ := by
  let := h.chosen.elementary
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let W := space (V := V) (F.Vi 1)
  have hBV : B ≤ normalizer (V : Set G) := sup_le
    (((F.Li_le L 1).trans inf_le_left).trans h.chosen.normalizes)
    (h.sylow_normalizes_seed earlier.structural)
  have hBH : B ≤ F.H := sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  let a₀ := seedLinearAction B hBV
  have haW (b : B) : a₀ b ∈ BinaryLinear.parabolic W := by
    intro v
    change (b : G) * (v.toMul : G) * (b : G)⁻¹ ∈ F.Vi 1 ↔ (v.toMul : G) ∈ F.Vi 1
    exact (mem_normalizer_iff.mp (hBH b.property) v.toMul).symm
  let a := a₀.codRestrict (BinaryLinear.parabolic W) haW
  have hker : a.ker = (centralizer (V : Set G)).subgroupOf B := by
    rw [MonoidHom.ker_codRestrict,seedLinearAction_ker]
  let b := a.comp (inclusion (show F.Li L 1 ≤ B from le_sup_left))
  obtain ⟨f,hf,hfk⟩ := point_residual_full_action h hn F
  have hbker : b.ker = f.ker := by
    rw [← MonoidHom.comap_ker,hker,hfk]
    rfl
  have hcard : Nat.card b.range = Nat.card (BinaryLinear.parabolic W) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange b).toEquiv,hbker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  exact ⟨a,hker,MonoidHom.range_eq_top.mp (b.range.eq_top_of_card_eq hcard),fun _ _ => rfl⟩

/-- The full point action with its literal kernel and residual surjectivity. -/
theorem point_join_action
    (h : HigherRankHypothesis K T L V n) (hn : 4 ≤ n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) :
    letI := h.chosen.elementary
    ∃ a : (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) →*
        BinaryLinear.parabolic (space (V := V) (F.Vi 1)),
      a.ker = (centralizer (V : Set G)).subgroupOf (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      Function.Surjective (a.comp (inclusion le_sup_left)) := by
  obtain ⟨a,hk,hs,_⟩ := point_join_conjugation_action h hn earlier F
  exact ⟨a,hk,hs⟩

/-- Centralization by the component core forces centralization by the core
of its Sylow join, since the full point parabolic has trivial centralizer. -/
theorem join_core_centralizes_of_component_core_centralizes
    (h : HigherRankHypothesis K T L V n) (hn : 4 ≤ n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hc : C.K1.pCoreIn 2 ≤ centralizer (V : Set G)) :
    (C.K1 ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (V : Set G) := by
  let := h.chosen.elementary
  let X := C.K1 ⊔ (T : Subgroup G)
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hBX : B ≤ X := sup_le_sup_right C.contains _
  have hRT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow X (T.subtype hTX)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX] using hh
  obtain ⟨a,hak,has⟩ := point_join_action h hn earlier F
  let hTN := (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)
  let q := QuotientGroup.mk' (pCore 2 C.K1)
  have hcomm (r : B) (hr : (r : G) ∈ X.pCoreIn 2) (l : F.Li L 1) :
      a r * a (inclusion le_sup_left l) = a (inclusion le_sup_left l) * a r := by
    let rx : X := inclusion hBX r
    have hrx : rx ∈ pCore 2 X := by
      obtain ⟨x,hx,he⟩ := hr
      exact (Subtype.ext he : x = rx) ▸ hx
    have hact := pCore_le_pCoreJoinAction_kernel 2 hTN hrx
    have he := congrArg (fun α : MulAut (C.K1 ⧸ pCore 2 C.K1) => α (q (inclusion C.contains l))) hact
    rw [pCoreJoinAction_mk] at he
    change q (C.K1.normalizerMonoidHom (inclusion (sup_le C.K1.le_normalizer hTN) rx) (inclusion C.contains l)) = q (inclusion C.contains l) at he
    have hk : C.K1.normalizerMonoidHom (inclusion (sup_le C.K1.le_normalizer hTN) rx) (inclusion C.contains l) * (inclusion C.contains l)⁻¹ ∈ pCore 2 C.K1 := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (_ * _) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hg : (r : G) * (l : G) * (r : G)⁻¹ * (l : G)⁻¹ ∈ C.K1.pCoreIn 2 :=
      mem_map.mpr ⟨_,hk,rfl⟩
    have hk' : r * inclusion le_sup_left l * r⁻¹ * (inclusion le_sup_left l)⁻¹ ∈ a.ker := by
      rw [hak]
      exact hc hg
    change a (r * inclusion le_sup_left l * r⁻¹ * (inclusion le_sup_left l)⁻¹) = 1 at hk'
    rw [map_mul,map_mul,map_mul,map_inv,map_inv,mul_inv_eq_one] at hk'
    exact mul_inv_eq_iff_eq_mul.mp hk'
  intro r hr
  let rb : B := ⟨r,(show (T : Subgroup G) ≤ B from le_sup_right) (hRT hr)⟩
  have ha : (a rb).val ∈ centralizer (BinaryLinear.parabolic (space (V := V) (F.Vi 1)) : Set (BinaryLinear.GL (Additive V))) := by
    intro g hg
    obtain ⟨l,hl⟩ := has ⟨g,hg⟩
    have he := congrArg Subtype.val (hcomm rb hr l)
    change (a rb).val * (a (inclusion le_sup_left l)).val = (a (inclusion le_sup_left l)).val * (a rb).val at he
    have he' : (a (inclusion le_sup_left l)).val = g := congrArg Subtype.val hl
    rw [he'] at he
    exact he.symm
  have hv : Module.finrank (ZMod 2) (Additive V) = n := h.naturalMarking.coordinates.finrank_eq.trans (by simp)
  rw [BinaryLinear.PointParabolicSection.point_centralizer_eq_bot (by omega)
    _ (Components.flag_space_finrank F 1 (by omega)),mem_bot] at ha
  have hk : rb ∈ a.ker := Subtype.ext ha
  rw [hak] at hk
  exact hk

/-- The original component core moves the plane when the binary dimensions match.
The quotient-centralizer bound is the earlier source 12.9.5(1) premise. -/
theorem point_core_moves_plane_of_matching_binary
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) n 2)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G)) :
    ⁅F.Vi 2, C.K1.pCoreIn 2⁆ ≠ ⊥ := by
  intro hfix
  let := h.chosen.elementary
  have hc := (core_centralizes_point_span_of_plane_fixed h F C hfix).trans
    (centralizer_le (le_conjugateSpanBy V F.H))
  have hR := join_core_centralizes_of_component_core_centralizes h (by omega) earlier F C hc
  let X := C.K1 ⊔ (T : Subgroup G)
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hBX : B ≤ X := sup_le_sup_right C.contains _
  have hLX : F.Li L 1 ≤ X := C.contains.trans le_sup_left
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hh
  have hRT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow X (T.subtype hTX)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX] using hh
  have hRQ : X.pCoreIn 2 ≤ Q := by
    dsimp only [Q]
    rw [← h.centralizer_LT earlier.structural]
    exact le_inf (hRT.trans le_sup_right) hR
  obtain ⟨k,_,_,hcard,⟨e₀⟩⟩ := hm
  let ek := Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo k hcard
  let e := (e₀.trans (Atlas.fieldEquivPSL n ek)).trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0<n))
  have hz : center (C.K1 ⧸ pCore 2 C.K1) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    let eS := e.trans (slEquivLinear n).symm
    have he : eS x ∈ center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
      (centerCongr eS ⟨x,hx⟩).property
    rw [binary_center_eq_bot (by omega),mem_bot] at he
    exact mem_bot.mpr (eS.map_eq_one_iff.mp he)
  let hTN := (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)
  have hi := binary_sylow_acts_inner h hn earlier F C hn
    (show ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) n 2 from ⟨k,inferInstance,inferInstance,hcard,⟨e₀⟩⟩)
  let eX := (pCoreJoinQuotientEquivOfInner C.K1 (T : Subgroup G) hTN T.isPGroup' hz hi).trans e
  let q := eX.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := eX.surjective.comp (QuotientGroup.mk'_surjective _)
  let : Finite (LinearGroup n) := Finite.of_surjective q hq
  have hqk : q.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ eX.injective,QuotientGroup.ker_mk']
  let S := (T.subtype hTX).mapSurjective (f := q) hq
  let g := q.comp (inclusion hLX)
  have hgr : g.range = ((F.Li L 1).subgroupOf X).map q := by
    rw [MonoidHom.range_comp,inclusion_range]
  have hnorm : (T : Subgroup G).subgroupOf X ≤ normalizer ((F.Li L 1).subgroupOf X : Set X) := by
    rw [← subgroupOf_normalizer_eq hLX]
    exact comap_mono (sylow_normalizes_point_residual h earlier F)
  have hSn : (S : Subgroup (LinearGroup n)) ≤ normalizer (g.range : Set (LinearGroup n)) := by
    rw [hgr]
    exact (map_mono (f := q) hnorm).trans (((F.Li L 1).subgroupOf X).le_normalizer_map q)
  obtain ⟨a,hak,has⟩ := point_join_action h (by omega) earlier F
  let f := a.comp (inclusion (show F.Li L 1 ≤ B from le_sup_left))
  have hk : g.ker ≤ f.ker := by
    intro l hl
    have hlq : inclusion hLX l ∈ q.ker := hl
    rw [hqk] at hlq
    have hlR : (l : G) ∈ X.pCoreIn 2 := mem_map.mpr ⟨_,hlq,rfl⟩
    change inclusion le_sup_left l ∈ a.ker
    rw [hak]
    exact hR hlR
  have hv : Module.finrank (ZMod 2) (Additive V) = n := h.naturalMarking.coordinates.finrank_eq.trans (by simp)
  have hp : Nat.card (BinaryLinear.parabolic (space (V := V) (F.Vi 1))) =
      2^(n-1) * Nat.card (LinearGroup (n-1)) := by
    rw [BinaryLinear.PointStabilizerPerfect.parabolic_card _
      (Components.flag_space_finrank F 1 (by omega)),hv]
  obtain ⟨hker,hS⟩ := BinaryLinear.PointParabolicSection.section_kernel_eq hn S g hSn f has hk hp
  have hQR : Q ≤ X.pCoreIn 2 := by
    intro t ht
    let tx : X := ⟨t,hTX (hQT ht)⟩
    have hqt : q tx ∈ (S : Subgroup (LinearGroup n)) := mem_map_of_mem q (hQT ht)
    obtain ⟨l,hl⟩ := hS hqt
    let lb : B := inclusion le_sup_left l
    let tb : B := ⟨t,(show (T : Subgroup G) ≤ B from le_sup_right) (hQT ht)⟩
    have hdiff : inclusion hBX (lb * tb⁻¹) ∈ q.ker := by
      change q (inclusion hLX l * tx⁻¹) = 1
      rw [map_mul,map_inv,show q (inclusion hLX l) = q tx from hl,mul_inv_cancel]
    rw [hqk] at hdiff
    have hc : (l : G) * t⁻¹ ∈ centralizer (V : Set G) :=
      hR (mem_map.mpr ⟨_,hdiff,rfl⟩)
    have hct : t ∈ centralizer (V : Set G) := h.chosen.core_centralizes ht
    have hcl : (l : G) ∈ centralizer (V : Set G) := by
      simpa only [inv_mul_cancel_right] using (centralizer (V : Set G)).mul_mem hc hct
    have hfl : l ∈ f.ker := by
      change lb ∈ a.ker
      rw [hak]
      exact hcl
    have hgl : g l = 1 := by
      change l ∈ g.ker
      rwa [← hker]
    have hz : q tx = 1 := hl.symm.trans hgl
    have htR : tx ∈ pCore 2 X := hqk ▸ hz
    exact mem_map.mpr ⟨tx,htR,rfl⟩
  have he : X.pCoreIn 2 = Q := le_antisymm hRQ hQR
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
  have hXM : X ≤ normalizer (L : Set G) := by
    apply le_trans (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
    change normalizer (X.pCoreIn 2 : Set G) ≤ normalizer (L : Set G)
    rw [he]
    exact hNQ
  have hmodels : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨ ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2 := by
    have hm' : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) n 2 := ⟨k,inferInstance,inferInstance,hcard,⟨e₀⟩⟩
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl hm')
    · exact Or.inr (Or.inr hm')
  exact (point_join_mem_Hz_of_quotient_centralizer h earlier F C
    (point_outer_two_of_local_models F C hmodels) hcentral).2.2 hXM

/-- All three source 12.9.6 clauses in the matching binary rows, with the
literal plane closure, quotient and minimal-parabolic predicate. -/
theorem matching_binary_plane_local_control
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) n 2)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G)) :
    ⁅F.Vi 2, C.K1.pCoreIn 2⁆ ≠ ⊥ ∧
      ((planeCoreClosure F).subgroupOf (F.Gi 2)).Normal ∧
      planeCoreClosure F ⊔ (T : Subgroup G) = F.P L ∧
      ChapterB.IsMinimalParabolicOver T (planeCoreClosure F ⊔ (T : Subgroup G)) ∧
      (T : Subgroup G).relIndex (planeCoreClosure F ⊔ (T : Subgroup G)) = 3 ∧
      (planeCoreClosure F).pCoreIn 2 = planeCoreClosure F ⊓ centralizer (F.Vi 2 : Set G) ∧
      Nonempty (((planeCoreClosure F) ⧸ pCore 2 (planeCoreClosure F)) ≃* Equiv.Perm (Fin 3)) ∧
      primeRank 3 (centralizer (F.Vi 2 : Set G)) ≤ 1 := by
  have hmove := point_core_moves_plane_of_matching_binary h hn earlier F C hm hcentral
  exact ⟨hmove,plane_local_control_with_minimal_parabolic h earlier F C hmove⟩

/-- Apply matching binary movement to the actual LocalControl consumer.
Both source centralizer bounds remain obligations of this source owner. -/
theorem localControl_of_matching_binary_and_centralizers
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hm : ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) n 2)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G))
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) : LocalControl C := by
  have hmove := point_core_moves_plane_of_matching_binary h hn earlier F C hm hcentral
  have hmodels : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨ ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2 := by
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hm)
  exact localControl_of_plane_centralizer_and_models h earlier F C hcentral hmodels hmove hplane

/-- Degree-five LocalControl needs no separate movement premise once the
source centralizer bounds and surviving models have been established. -/
theorem five_localControl_of_centralizers_and_models
    (h : HigherRankHypothesis K T L V 5) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V 5) (C : ComponentGeometry F L)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G))
    (hmodels : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨ ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) : LocalControl C :=
  localControl_of_matching_binary_and_centralizers h (Or.inr rfl) earlier F C
    (five_point_model_of_controlled_quotient h earlier F C hcentral hmodels) hcentral hplane

/-- Under source 12.9.5(1–2), a remaining failure of plane movement must have
n=4 and PSL₅(2) point quotient. The mixed transvection argument remains
with this source owner. -/
theorem point_movement_failure_is_mixed
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G))
    (hmodels : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2)
    (hfix : ⁅F.Vi 2, C.K1.pCoreIn 2⁆ = ⊥) :
    n = 4 ∧ ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2 := by
  rcases hn with rfl | rfl
  · rcases hmodels with ha | h4 | h5
    · exact (point_core_moves_plane_of_alternating_seven h (Or.inl rfl) F C ha hfix).elim
    · exact (point_core_moves_plane_of_matching_binary h (Or.inl rfl) earlier F C h4 hcentral hfix).elim
    · exact ⟨rfl,h5⟩
  · exact (point_core_moves_plane_of_matching_binary h (Or.inr rfl) earlier F C
      (five_point_model_of_controlled_quotient h earlier F C hcentral hmodels) hcentral hfix).elim

end CFSG.Quasithin.Chapter12.Section09.NaturalSource

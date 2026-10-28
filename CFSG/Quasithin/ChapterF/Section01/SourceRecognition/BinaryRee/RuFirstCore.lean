module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveNormalizer.Source
public import Theory.GroupTheory.AlmostSpecialIntersection
public import Theory.Frattini.BinarySquares

/-!
# The intrinsic first two-core in the original Ru amalgam

The actual first core R = Q₀Q₅ has derived and Frattini subgroup U,
center Z, exponent dividing four, and nilpotency class three. Its
centralizer of U is exactly Q₀. All equalities retain the original
ambient subgroup maps.

Coprime splitting Q = Q₅ C_Q(B₅), with C_Q(B₅) centralizing U, first
transfers [Q,U] = Z to [R,U] = Z. The quaternion central product HC has
derived subgroup contained in Z. Choose an element of Q₀ outside U;
J.2.4 says that its commutator with Q is all of U. The quaternion
supplement contributes only Z, already contained in R′, so U = R′.
The marked elementary quotient Q/U then gives Φ(R) = U and fourth
powers equal to one. The last theorem applies these facts to the literal
embedded O₂(F₁) of the original source construction.

These are structural inputs to the first endpoint identification, not a
recognition theorem: the complete ten-root presentation and its complement
action still require proof. Source: Aschbacher–Smith J.2.4, J.4.1(3–4),
J.4.4–5, printed pp.434 and 440–442; the intended comparison is the first
parabolic in F.1.12(I)(5) at q = 2, printed p.263.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)
  (B5 : Sylow 5 d.toTypeRuSetup.H)

theorem firstCore_commutator_U :
    ⁅fiveHyperplane d B5,d.toTypeRuSetup.U⁆=d.toTypeRuSetup.Z := by
  have h5 : ⁅d.toTypeRuSetup.U,Q₅ d B5⁆=d.toTypeRuSetup.Z := by
    have h := commutator_eq_of_centralizing_sup
      (show CQ B5⊔Q₅ d B5=d.toTypeRuSetup.Q by
        rw [sup_comm]; exact (Q_eq_Q₅_sup_CQ d B5).symm)
      ((five_centralizer_le_HC B5).trans inf_le_right)
      (((Q₅_le_Q d B5).trans (pCoreIn_le 2 _)).trans d.ru2.natural.normalized)
    rw [commutator_comm d.toTypeRuSetup.U d.toTypeRuSetup.Q,d.commutator_Q_U] at h
    exact h
  apply le_antisymm
  · exact (commutator_mono (fiveHyperplane_le_Q d B5) le_rfl).trans
      d.toTypeRuSetup.commutator_Q_U_le_Z
  · rw [←h5,commutator_comm]
    exact commutator_mono le_sup_right le_rfl

private theorem HC_self_commutator_le_Z :
    ⁅d.toTypeRuSetup.HC,d.toTypeRuSetup.HC⁆≤d.toTypeRuSetup.Z := by
  obtain ⟨c⟩ := SourceCompletion.exists_choices d
  have hPhi := (SourceCompletion.fusion c).2.2.1.2.2.2.2.1
  exact derived_le_of_frattini_image_le
    ((isPGroup_pCoreIn 2 d.toTypeRuSetup.H).of_injective
      (inclusion d.toTypeRuSetup.HC_le_Q) (inclusion_injective _)) hPhi.le

theorem firstCore_derived :
    ⁅fiveHyperplane d B5,fiveHyperplane d B5⁆=d.toTypeRuSetup.U := by
  let R := fiveHyperplane d B5
  let D := ⁅R,R⁆
  have hRQ : R≤d.toTypeRuSetup.Q := fiveHyperplane_le_Q d B5
  have hUR : d.toTypeRuSetup.U≤R := U_le_fiveHyperplane d B5
  have hZD : d.toTypeRuSetup.Z≤D := by
    rw [←firstCore_commutator_U d B5]
    exact commutator_mono le_rfl hUR
  have hND : d.toTypeRuSetup.Q≤normalizer (D:Set G) := by
    intro q hq
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [D]
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (Q_normalizes_fiveHyperplane d B5 hq)]
  have hAC : ⁅CQ B5,Q₀ d⁆≤D :=
    ((commutator_mono (five_centralizer_le_HC B5) (Q₀_le_HC d)).trans
      (HC_self_commutator_le_Z d)).trans hZD
  have hQR : d.toTypeRuSetup.Q≤commutatorPreimage d.toTypeRuSetup.Q (Q₀ d) D := by
    conv_lhs => rw [Q_eq_Q₅_sup_CQ d B5]
    refine sup_le (le_commutatorPreimage (Q₅_le_Q d B5) ?_)
      (le_commutatorPreimage inf_le_left hAC)
    exact commutator_mono le_sup_right le_sup_left
  have hAQ : ⁅Q₀ d,d.toTypeRuSetup.Q⁆≤D := by
    rw [commutator_comm]
    exact (commutator_mono hQR le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hND)
  have hnu : ¬Q₀ d≤d.toTypeRuSetup.U := by
    intro h
    have hc := card_le_of_le h
    rw [card_Q₀,d.ru2.card_U d.card_Z] at hc
    omega
  obtain ⟨a,ha,haU⟩ := Set.not_subset.mp hnu
  obtain ⟨c⟩ := SourceCompletion.exists_choices d
  have haQ := (SourceCompletion.fusion c).1 a (Q₀_le_HC d ha) haU
  apply le_antisymm
  · apply commutator_le.mpr
    intro a ha b hb
    let x : d.toTypeRuSetup.Q := ⟨a,hRQ ha⟩
    let y : d.toTypeRuSetup.Q := ⟨b,hRQ hb⟩
    exact (d.ru2.six.coordinates_eq_one_iff ⁅x,y⁆).mp (by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _)
  · rw [←haQ.2.1]
    exact (commutator_mono (zpowers_le.mpr ha) le_rfl).trans hAQ

theorem firstCore_square_mem_U (x : fiveHyperplane d B5) :
    (x:G)^2∈d.toTypeRuSetup.U := by
  let q : d.toTypeRuSetup.Q := ⟨x,fiveHyperplane_le_Q d B5 x.property⟩
  change ((q^2:d.toTypeRuSetup.Q):G)∈d.toTypeRuSetup.U
  apply (d.ru2.six.coordinates_eq_one_iff (q^2)).mp
  rw [map_pow]
  change (2:ℕ) • (d.ru2.six.coordinates q).toAdd=0
  ext j
  exact CharTwo.two_nsmul _

theorem firstCore_frattini :
    (frattini (fiveHyperplane d B5)).map (fiveHyperplane d B5).subtype=d.toTypeRuSetup.U := by
  have hP := (isPGroup_pCoreIn 2 d.toTypeRuSetup.H).of_injective
    (inclusion (fiveHyperplane_le_Q d B5)) (inclusion_injective _)
  apply le_antisymm
  · rw [hP.frattini_eq_closure_squares,map_le_iff_le_comap]
    apply (closure_le _).mpr
    rintro _ ⟨x,rfl⟩
    exact firstCore_square_mem_U d B5 x
  · rw [←firstCore_derived d B5,←map_subtype_commutator]
    let : Fact (IsPGroup 2 (fiveHyperplane d B5)) := ⟨hP⟩
    exact map_mono (commutator_le_frattini_of_isPGroup (p:=2))

theorem firstCore_center :
    (center (fiveHyperplane d B5)).map (fiveHyperplane d B5).subtype=d.toTypeRuSetup.Z := by
  apply le_antisymm
  · rintro x ⟨x,hx,rfl⟩
    apply (centralizer_Q₀_sup_Q₅ d B5).le
    intro r hr
    exact congrArg (fun a:fiveHyperplane d B5=>(a:G))
      (mem_center_iff.mp hx ⟨r,hr⟩)
  · intro z hz
    let zR : fiveHyperplane d B5 := ⟨z,
      U_le_fiveHyperplane d B5 (d.ru2.natural.kernel_le hz)⟩
    refine ⟨zR,?_,rfl⟩
    apply mem_center_iff.mpr
    intro r
    apply Subtype.ext
    exact (centralizer_Q₀_sup_Q₅ d B5).ge hz r r.property

theorem firstCore_fourth_power (x : fiveHyperplane d B5) : x^4=1 := by
  let u : d.toTypeRuSetup.U := ⟨(x:G)^2,firstCore_square_mem_U d B5 x⟩
  let := d.elementary_U
  have hu : u^2=1 := (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p (p:=2) (G:=d.toTypeRuSetup.U))) u
  apply Subtype.ext
  have he := congrArg (fun a:d.toTypeRuSetup.U=>(a:G)) hu
  simpa only [u,coe_pow,coe_mk,coe_one,←pow_mul] using he

theorem firstCore_inf_HC :
    fiveHyperplane d B5⊓d.toTypeRuSetup.HC=Q₀ d := by
  have hs : fiveHyperplane d B5⊔d.toTypeRuSetup.HC=d.toTypeRuSetup.Q := by
    apply le_antisymm (sup_le (fiveHyperplane_le_Q d B5) d.toTypeRuSetup.HC_le_Q)
    rw [←Q₅_sup_HC d B5]
    exact sup_le_sup_right le_sup_right _
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (fiveHyperplane d B5) d.toTypeRuSetup.HC
    (d.toTypeRuSetup.HC_le_Q.trans (Q_normalizes_fiveHyperplane d B5))
  rw [hs,fiveHyperplane_card,d.card_HC,d.ru2.card_Q d.card_Z] at hc
  apply (eq_of_le_of_card_ge (le_inf le_sup_left (Q₀_le_HC d)) ?_).symm
  change Nat.card (fiveHyperplane d B5⊓d.toTypeRuSetup.HC:Subgroup G)≤Nat.card (Q₀ d)
  rw [card_Q₀]
  omega

theorem firstCore_centralizer_U :
    fiveHyperplane d B5⊓centralizer (d.toTypeRuSetup.U:Set G)=Q₀ d := by
  rw [centralizer_U,firstCore_inf_HC]

theorem firstCore_third_commutator :
    ⁅_root_.commutator (fiveHyperplane d B5),(⊤:Subgroup (fiveHyperplane d B5))⁆=
      center (fiveHyperplane d B5) := by
  apply map_injective (fiveHyperplane d B5).subtype_injective
  rw [map_commutator,map_subtype_commutator,firstCore_derived,
    ←MonoidHom.range_eq_map,range_subtype,commutator_comm,firstCore_commutator_U,
    firstCore_center]

theorem firstCore_center_card : Nat.card (center (fiveHyperplane d B5))=2 := by
  rw [←card_map_of_injective (fiveHyperplane d B5).subtype_injective,firstCore_center]
  exact d.card_Z

theorem firstCore_derived_card : Nat.card (_root_.commutator (fiveHyperplane d B5))=32 := by
  rw [←card_map_of_injective (fiveHyperplane d B5).subtype_injective,
    map_subtype_commutator,firstCore_derived]
  exact d.ru2.card_U d.card_Z

theorem firstCore_nilpotencyClass : Group.nilpotencyClass (fiveHyperplane d B5)=3 := by
  let R := fiveHyperplane d B5
  let : Group.IsNilpotent R := ((isPGroup_pCoreIn 2 d.toTypeRuSetup.H).of_injective
    (inclusion (fiveHyperplane_le_Q d B5)) (inclusion_injective _)).isNilpotent
  have h2 : (⊤:Subgroup R).lowerCentralSeries 2=center R := firstCore_third_commutator d B5
  have h3 : (⊤:Subgroup R).lowerCentralSeries 3=⊥ := by
    change ⁅(⊤:Subgroup R).lowerCentralSeries 2,(⊤:Subgroup R)⁆=⊥
    rw [h2]
    exact commutator_top_right_eq_bot_iff_le_center.mpr le_rfl
  have hle := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp h3
  have hn : ¬ Group.nilpotencyClass R≤2 := by
    intro hn
    have hh := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hn
    rw [h2] at hh
    have hc := firstCore_center_card d B5
    change Nat.card (center R)=2 at hc
    rw [hh,card_bot] at hc
    contradiction
  change Group.nilpotencyClass R=3
  omega

theorem firstCore_structure :
    Nat.card (fiveHyperplane d B5)=1024 ∧
    ⁅fiveHyperplane d B5,fiveHyperplane d B5⁆=d.toTypeRuSetup.U ∧
    (frattini (fiveHyperplane d B5)).map (fiveHyperplane d B5).subtype=d.toTypeRuSetup.U ∧
    (center (fiveHyperplane d B5)).map (fiveHyperplane d B5).subtype=d.toTypeRuSetup.Z ∧
    Group.nilpotencyClass (fiveHyperplane d B5)=3 ∧
    (∀x:fiveHyperplane d B5,x^4=1) ∧
    fiveHyperplane d B5⊓centralizer (d.toTypeRuSetup.U:Set G)=Q₀ d :=
  ⟨fiveHyperplane_card d B5,firstCore_derived d B5,firstCore_frattini d B5,
    firstCore_center d B5,firstCore_nilpotencyClass d B5,firstCore_fourth_power d B5,
    firstCore_centralizer_U d B5⟩

variable {d} (p:Plane d)
theorem SourceChoice.F₁_core_structure_source (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nat.card ((p.F₁ B5).pCoreIn 2)=1024 ∧
    ⁅(p.F₁ B5).pCoreIn 2,(p.F₁ B5).pCoreIn 2⁆=d.toTypeRuSetup.U ∧
    (frattini ((p.F₁ B5).pCoreIn 2)).map ((p.F₁ B5).pCoreIn 2).subtype=d.toTypeRuSetup.U ∧
    (center ((p.F₁ B5).pCoreIn 2)).map ((p.F₁ B5).pCoreIn 2).subtype=d.toTypeRuSetup.Z ∧
    Group.nilpotencyClass ((p.F₁ B5).pCoreIn 2)=3 ∧
    (∀x:(p.F₁ B5).pCoreIn 2,x^4=1) ∧
    (p.F₁ B5).pCoreIn 2⊓centralizer (d.toTypeRuSetup.U:Set G)=Q₀ d := by
  rw [s.F₁_core_eq_fiveHyperplane p B5 hi]
  exact firstCore_structure d B5

/-- The source core invariants from the original type-Ru hypothesis alone.
The plane, conjugate choice, and inverted Sylow-five subgroup are constructed
by the earlier J.4 producers; they are not additional hypotheses. -/
theorem first_core_structure_of_typeRu (h : IsTypeRu G) :
    ∃ (d : LocalSetup G) (p : Plane d) (B5 : Sylow 5 d.toTypeRuSetup.H),
      Nat.card ((p.F₁ B5).pCoreIn 2) = 1024 ∧
      ⁅(p.F₁ B5).pCoreIn 2, (p.F₁ B5).pCoreIn 2⁆ = d.toTypeRuSetup.U ∧
      (frattini ((p.F₁ B5).pCoreIn 2)).map ((p.F₁ B5).pCoreIn 2).subtype = d.toTypeRuSetup.U ∧
      (center ((p.F₁ B5).pCoreIn 2)).map ((p.F₁ B5).pCoreIn 2).subtype = d.toTypeRuSetup.Z ∧
      Group.nilpotencyClass ((p.F₁ B5).pCoreIn 2) = 3 ∧
      (∀ x : (p.F₁ B5).pCoreIn 2, x ^ 4 = 1) ∧
      (p.F₁ B5).pCoreIn 2 ⊓ centralizer (d.toTypeRuSetup.U : Set G) = Q₀ d := by
  obtain ⟨d⟩ := h.nonempty_localSetup
  obtain ⟨p⟩ := exists_plane d
  obtain ⟨s⟩ := p.exists_sourceChoice
  obtain ⟨B5, hi⟩ := s.inverts_sylow_five
  exact ⟨d, p, B5, s.F₁_core_structure_source p B5 hi⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup

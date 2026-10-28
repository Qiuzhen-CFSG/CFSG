module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.ModelData
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.NormalizerModels.Marking
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.Centerless.Order

/-!
# Centerless local graph-field normalizers

When O₂(L) is trivial, the marked cover is an actual isomorphism L ≃ PSL₃(4).
The outside-product condition and the trivial center give L ∩ E = 1 for
E = ⟨r,z⟩. Commutators then show that N_LE(E) = C_L(r)E centralizes E.

A faithful embedding transports a concrete quaternion supplement of the
projective graph-field fixed group to P ≤ C_L(r). Setting Q = PE constructs
the two-group normalizer, its actual relative quotient Q/E, and its quaternion
complement. The Hermitian identity s·graphField(s⁻¹) = u² transports to an
L-conjugating element for r and r·v; the square v belongs to Φ(P).

`CenterlessLocalData` retains every local witness and leaves the full ambient
residual-fixer bound to its independent owner. The public `centerlessLocalData`
constructor instantiates the explicit quaternion matrices, their faithful action
on E₉, the proved fixed-group decomposition and the Hermitian fusion identity.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(5) and the centerless branch of 16.4.9(2), printed pp.1171, 1191–1192.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField.NormalizerModels
open Matrix.PSL3Four Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- A marked central cover with trivial center is an actual group isomorphism. -/
noncomputable def MarkedCover.centerlessEquiv (d : MarkedCover L r)
    (hcenter : center L = ⊥) : L ≃* PSL :=
  MulEquiv.ofBijective d.cover.toMonoidHom
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (d.kernel_center.trans hcenter), d.cover.surjective⟩

/-- The source center/two-core identity gives trivial center in this branch. -/
theorem centerless_center_eq_bot {𝒦 : GroupClass} (hG : Hypothesis1611 𝒦 G)
    (h : IntersectionSetup T z L g R) (hcore : pCore 2 L = ⊥) : center L = ⊥ :=
  (hG.evenType.component_center_eq_twoCore h.involution h.component).trans hcore

private theorem mem_four_cases (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    (hr2 : orderOf r = 2) {x : G} (hx : x ∈ fourGroup r z) :
    x = 1 ∨ x = r ∨ x = z ∨ x = r * z := by
  classical
  have hn : zpowers z ≤ normalizer (zpowers r : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    rw [zpowers_eq_closure r, centralizer_closure]
    apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (h.sylow_centralizes (h.le_sylow hr))).symm
  have hx' : x ∈ (zpowers r : Set G) * (zpowers z : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  change a ∈ zpowers r at ha
  change b ∈ zpowers z at hb
  rw [mem_zpowers_iff_mem_range_orderOf, hr2] at ha
  rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hb
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
  have hi2 := Finset.mem_range.mp hi
  have hj2 := Finset.mem_range.mp hj
  interval_cases i <;> interval_cases j <;> simp

/-- The marked four-group meets the centerless component trivially. -/
theorem centerless_four_disjoint_component (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) (hcenter : center L = ⊥) :
    Disjoint (fourGroup r z) L := by
  have hzL : z ∉ L := by
    intro hz
    have hzZ : (⟨z,hz⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro x
      exact Subtype.ext (central_involution_mem_centralizer h x x.property)
    rw [hcenter, mem_bot] at hzZ
    have hz1 : z = 1 := congrArg Subtype.val hzZ
    simpa [hz1] using h.involution
  apply disjoint_def.mpr
  intro x hx hxl
  rcases mem_four_cases h hr hr2 hx with he | rfl | rfl | rfl
  · exact he
  · exact (hout (mem_sup_right hxl)).elim
  · exact (hzL hxl).elim
  · have hrmem : r ∈ centralizer (L : Set G) ⊔ L := by
      have ht := (centralizer (L : Set G) ⊔ L).mul_mem
        (mem_sup_right hxl)
        (mem_sup_left ((centralizer (L : Set G)).inv_mem
          (central_involution_mem_centralizer h)))
      simpa only [mul_inv_cancel_right] using ht
    exact (hout hrmem).elim

/-- The specified actor and central involution normalize the component. -/
theorem four_le_component_normalizer (h : IntersectionSetup T z L g R)
    (hn : r ∈ normalizer (L : Set G)) :
    fourGroup r z ≤ normalizer (L : Set G) :=
  sup_le (zpowers_le.mpr hn) (zpowers_le.mpr
    (centralizer_le_normalizer _ (central_involution_mem_centralizer h)))

/-- Commutators of the component normalizer of E lie in the trivial intersection L ∩ E. -/
theorem centerless_component_normalizer_four_le_centralizer
    (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) (hcenter : center L = ⊥)
    (hn : r ∈ normalizer (L : Set G)) :
    L ⊓ normalizer (fourGroup r z : Set G) ≤ centralizer (fourGroup r z : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  have he := centerless_four_disjoint_component h hr hr2 hout hcenter
  have h1 : ⁅L ⊓ normalizer (fourGroup r z : Set G), fourGroup r z⁆ ≤ L :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (four_le_component_normalizer h hn))
  have h2 : ⁅L ⊓ normalizer (fourGroup r z : Set G), fourGroup r z⁆ ≤ fourGroup r z :=
    le_normalizer_iff_commutator_le_right.mp inf_le_right
  exact (le_inf h2 h1).trans he.le_bot

/-- Inside L, fixing r is equivalent to fixing E, since z already centralizes L. -/
theorem component_four_centralizer (h : IntersectionSetup T z L g R) :
    L ⊓ centralizer (fourGroup r z : Set G) = L ⊓ centralizer ({r} : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr
      (mem_sup_left (mem_zpowers r))))
  · apply le_inf inf_le_left
    apply le_centralizer_iff.mpr
    apply sup_le
    · apply zpowers_le.mpr
      intro x hx
      exact mem_centralizer_singleton_iff.mp hx.2
    · apply zpowers_le.mpr
      intro x hx
      exact mem_centralizer_singleton_iff.mp (h.component.1 hx.1)

/-- Trivial intersection makes the local normalizer precisely C_L(r)E. -/
theorem centerless_local_normalizer_eq (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) (hcenter : center L = ⊥)
    (hn : r ∈ normalizer (L : Set G)) :
    (L ⊔ fourGroup r z) ⊓ normalizer (fourGroup r z : Set G) =
      (L ⊓ centralizer ({r} : Set G)) ⊔ fourGroup r z := by
  rw [← component_four_centralizer h]
  apply le_antisymm
  · intro x hx
    have hxp : x ∈ (L : Set G) * (fourGroup r z : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (four_le_component_normalizer h hn)]
      exact hx.1
    obtain ⟨l, hl, e, he, rfl⟩ := hxp
    have hln : l ∈ normalizer (fourGroup r z : Set G) := by
      have hh := (normalizer (fourGroup r z : Set G)).mul_mem hx.2
        ((fourGroup r z).le_normalizer ((fourGroup r z).inv_mem he))
      simpa only [mul_inv_cancel_right] using hh
    exact mul_mem_sup ⟨hl,
      centerless_component_normalizer_four_le_centralizer h hr hr2 hout hcenter hn ⟨hl,hln⟩⟩ he
  · apply sup_le
    · exact le_inf (inf_le_left.trans le_sup_left)
        (inf_le_right.trans (centralizer_le_normalizer _))
    · exact le_inf le_sup_right (fourGroup r z).le_normalizer

/-- The whole local normalizer centralizes E in the centerless branch. -/
theorem centerless_local_normalizer_centralizes_four (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) (hcenter : center L = ⊥)
    (hn : r ∈ normalizer (L : Set G)) :
    (L ⊔ fourGroup r z) ⊓ normalizer (fourGroup r z : Set G) ≤
      centralizer (fourGroup r z : Set G) := by
  rw [centerless_local_normalizer_eq h hr hr2 hout hcenter hn,
    ← component_four_centralizer h]
  apply sup_le inf_le_right
  let : IsElementaryAbelian 2 (fourGroup r z) := (fourGroup_elementary_card h hr hr2 hout).1
  intro x hx y hy
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨y,hy⟩ : fourGroup r z) ⟨x,hx⟩)


/-- The marked isomorphism, read as an actual inclusion in the source ambient group. -/
noncomputable def MarkedCover.centerlessEmbedding (d : MarkedCover L r)
    (hcenter : center L = ⊥) : PSL →* G :=
  L.subtype.comp (d.centerlessEquiv hcenter).symm.toMonoidHom

omit [Finite G] in
/-- Faithfulness retains the actual projective model when transported to G. -/
theorem MarkedCover.centerlessEmbedding_injective (d : MarkedCover L r)
    (hcenter : center L = ⊥) : Function.Injective (d.centerlessEmbedding hcenter) :=
  L.subtype_injective.comp (d.centerlessEquiv hcenter).symm.injective

omit [Finite G] in
/-- The faithful model inclusion has image exactly L. -/
theorem MarkedCover.centerlessEmbedding_range (d : MarkedCover L r)
    (hcenter : center L = ⊥) : (d.centerlessEmbedding hcenter).range = L := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ((d.centerlessEquiv hcenter).symm y).property
  · intro hx
    refine ⟨d.centerlessEquiv hcenter ⟨x,hx⟩, ?_⟩
    change ((d.centerlessEquiv hcenter).symm (d.centerlessEquiv hcenter ⟨x,hx⟩) : G) = x
    rw [MulEquiv.symm_apply_apply]

omit [Finite G] in
/-- The faithful inclusion intertwines graph-field action with conjugation by r. -/
theorem MarkedCover.centerlessEmbedding_action (d : MarkedCover L r)
    (hcenter : center L = ⊥) (x : PSL) :
    d.centerlessEmbedding hcenter (graphField x) =
      MulAut.conj r (d.centerlessEmbedding hcenter x) := by
  let e := d.centerlessEquiv hcenter
  have he : e (L.normalizerMonoidHom ⟨r,d.actor_mem⟩ (e.symm x)) = graphField x := by
    change d.cover.toMonoidHom (L.normalizerMonoidHom ⟨r,d.actor_mem⟩ (e.symm x)) = _
    rw [d.compatible]
    exact congrArg graphField (e.apply_symm_apply x)
  have he' := congrArg e.symm he
  simp only [MulEquiv.symm_apply_apply] at he'
  exact congrArg Subtype.val he'.symm

omit [Finite G] in
/-- The concrete E₉ maps onto the actual embedded two-residual. -/
theorem MarkedCover.centerlessEmbedding_model (d : MarkedCover L r)
    (hcenter : center L = ⊥) : model.map (d.centerlessEmbedding hcenter) = residual L r := by
  rw [centerlessEmbedding, ← map_map, ← d.residual_image]
  have he : (((residual L r).subgroupOf L).map d.cover.toMonoidHom).map
      (d.centerlessEquiv hcenter).symm.toMonoidHom = (residual L r).subgroupOf L := by
    change (((residual L r).subgroupOf L).map (d.centerlessEquiv hcenter).toMonoidHom).map
      (d.centerlessEquiv hcenter).symm.toMonoidHom = _
    rw [map_map]
    have hid : (d.centerlessEquiv hcenter).symm.toMonoidHom.comp
        (d.centerlessEquiv hcenter).toMonoidHom = MonoidHom.id L := by
      apply MonoidHom.ext
      intro x
      exact (d.centerlessEquiv hcenter).symm_apply_apply x
    rw [hid, map_id]
  rw [he, map_subgroupOf_eq_of_le ((residual_le_centralizer L r).trans inf_le_left)]

omit [Finite G] in
/-- The full projective fixed subgroup maps onto C_L(r). -/
theorem MarkedCover.centerlessEmbedding_fixed (d : MarkedCover L r)
    (hcenter : center L = ⊥) : graphField.fixedSubgroup.map (d.centerlessEmbedding hcenter) =
      L ⊓ centralizer ({r} : Set G) := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    refine ⟨(d.centerlessEquiv hcenter).symm y |>.property, ?_⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := (d.centerlessEmbedding_action hcenter y).symm
    rw [(MulAut.mem_fixedSubgroup _ _).mp hy] at hh
    change r * _ * r⁻¹ = _ at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro x hx
    obtain ⟨y,hy⟩ := (d.centerlessEmbedding_range hcenter).symm ▸ hx.1
    refine ⟨y, ?_, hy⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply d.centerlessEmbedding_injective hcenter
    rw [d.centerlessEmbedding_action, hy]
    change r * x * r⁻¹ = x
    rw [← mem_centralizer_singleton_iff.mp hx.2, mul_inv_cancel_right]


omit [Finite G] in
/-- The whole fixed centralizer normalizes its embedded two-residual. -/
theorem component_fixed_normalizes_residual (L : Subgroup G) (r : G) :
    L ⊓ centralizer ({r} : Set G) ≤ normalizer (residual L r : Set G) := by
  let C := L ⊓ centralizer ({r} : Set G)
  change C ≤ normalizer ((pResidual 2 C).map C.subtype : Set G)
  have hh := (pResidual 2 C).le_normalizer_map C.subtype
  simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh

/-- The centerless local witnesses. The global residual-fixer bound is deliberately
absent, since its proof belongs to the independent automorphism calculation. -/
structure CenterlessLocalData (L : Subgroup G) (r z : G) where
  Q : Subgroup G
  two_group : IsPGroup 2 Q
  four_le : fourGroup r z ≤ Q
  le_product : Q ≤ L ⊔ fourGroup r z
  normalizes_four : Q ≤ normalizer (fourGroup r z : Set G)
  normalizes_residual : Q ≤ normalizer (residual L r : Set G)
  normalizer_eq : (L ⊔ fourGroup r z) ⊓ normalizer (fourGroup r z : Set G) =
    residual L r ⊔ Q
  centralizer_eq : Q ⊓ centralizer (residual L r : Set G) = fourGroup r z
  quotient_quaternion :
    letI : ((fourGroup r z).subgroupOf Q).Normal :=
      normal_subgroupOf_of_le_normalizer normalizes_four
    Nonempty ((Q ⧸ (fourGroup r z).subgroupOf Q) ≃* QuaternionGroup 2)
  centralizes_four : Q ≤ centralizer (fourGroup r z : Set G)
  P : Subgroup G
  le_Q : P ≤ Q
  disjoint_four : Disjoint P (fourGroup r z)
  sup_four : P ⊔ fourGroup r z = Q
  quaternion : Nonempty (P ≃* QuaternionGroup 2)
  frattini_product : ∃ v ∈ (frattini P).map P.subtype,
    orderOf v = 2 ∧ v ∈ L ⊓ centralizer ({r} : Set G) ∧
    ∃ l ∈ L, MulAut.conj l r = r * v

/-- Attach the independently proved full residual-fixer bound to the local witnesses. -/
def CenterlessLocalData.normalizerData (d : CenterlessLocalData L r z)
    (hfix : normalizer (L : Set G) ⊓ centralizer (residual L r : Set G) ≤
      (centralizer (L : Set G) ⊔ residual L r) ⊔ zpowers r) : NormalizerData L r z where
  Q := d.Q
  two_group := d.two_group
  four_le := d.four_le
  le_product := d.le_product
  normalizes_four := d.normalizes_four
  normalizes_residual := d.normalizes_residual
  normalizer_eq := d.normalizer_eq
  centralizer_eq := d.centralizer_eq
  residual_fixer := hfix
  quaternion := d.quotient_quaternion

/-- The same actual complement works for the assembled normalizer data. -/
def CenterlessLocalData.complementData (d : CenterlessLocalData L r z)
    (hfix : normalizer (L : Set G) ⊓ centralizer (residual L r : Set G) ≤
      (centralizer (L : Set G) ⊔ residual L r) ⊔ zpowers r) :
    CenterlessComplementData (d.normalizerData hfix) where
  centralizes_four := d.centralizes_four
  P := d.P
  le_Q := d.le_Q
  disjoint_four := d.disjoint_four
  sup_four := d.sup_four
  quaternion := d.quaternion
  frattini_product := d.frattini_product

/-- A projective quaternion supplement and one explicit Hermitian fusion identity
construct all centerless local witnesses in the source ambient group. The concrete
matrix supplement and action calculations are explicit premises of this transfer,
not conclusions supplied by 16.1.4(5). -/
noncomputable def centerlessLocalData_of_projective
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) (hcenter : center L = ⊥)
    (d : MarkedCover L r) (B : Subgroup PSL) (hB : B ≤ graphField.fixedSubgroup)
    (eB : B ≃* QuaternionGroup 2)
    (hsupp : graphField.fixedSubgroup = model ⊔ B)
    (hfaithful : B ⊓ centralizer (model : Set PSL) = ⊥)
    (u : B) (hu : orderOf (u : PSL) = 4)
    (s : PSL) (hs : s * graphField s⁻¹ = (u : PSL) ^ 2) :
    CenterlessLocalData L r z := by
  let f := d.centerlessEmbedding hcenter
  have hf : Function.Injective f := d.centerlessEmbedding_injective hcenter
  let P := B.map f
  let E := fourGroup r z
  let Q := P ⊔ E
  have hPD : P ≤ L ⊓ centralizer ({r} : Set G) := by
    rw [← d.centerlessEmbedding_fixed hcenter]
    exact map_mono hB
  have hPL : P ≤ L := hPD.trans inf_le_left
  have hPE : P ≤ centralizer (E : Set G) :=
    hPD.trans ((component_four_centralizer h).ge.trans inf_le_right)
  have hdis : Disjoint P E :=
    (centerless_four_disjoint_component h hr hr2 hout hcenter).symm.mono_left hPL
  let : IsElementaryAbelian 2 E := (fourGroup_elementary_card h hr hr2 hout).1
  have hEE : E ≤ centralizer (E : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hQE : Q ≤ centralizer (E : Set G) := sup_le hPE hEE
  have hQN : Q ≤ normalizer (E : Set G) := hQE.trans (centralizer_le_normalizer _)
  let eP : P ≃* QuaternionGroup 2 := (B.equivMapOfInjective f hf).symm.trans eB
  have hPcard : Nat.card P = 2 ^ 3 := by
    rw [Nat.card_congr eP.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rfl
  have hPtwo : IsPGroup 2 P := IsPGroup.of_card hPcard
  have hQtwo : IsPGroup 2 Q := hPtwo.to_sup_of_normal_right'
    (IsElementaryAbelian.isPGroup 2 E) (hPE.trans (centralizer_le_normalizer _))
  have hPN : P ≤ normalizer (residual L r : Set G) :=
    hPD.trans (component_fixed_normalizes_residual L r)
  have hED : E ≤ centralizer (residual L r : Set G) :=
    le_centralizer_iff.mp (residual_le_fourGroup_centralizer h)
  have hQND : Q ≤ normalizer (residual L r : Set G) :=
    sup_le hPN (hED.trans (centralizer_le_normalizer _))
  have hPCD : P ⊓ centralizer (residual L r : Set G) = ⊥ := by
    apply bot_unique
    rintro x ⟨⟨b,hb,rfl⟩,hx⟩
    have hbc : b ∈ centralizer (model : Set PSL) := by
      intro m hm
      apply hf
      simp only [map_mul]
      exact hx (f m) ((d.centerlessEmbedding_model hcenter).le (mem_map_of_mem f hm))
    have hb1 : b = 1 := mem_bot.mp (hfaithful.le ⟨hb,hbc⟩)
    simp only [hb1, map_one, mem_bot]
  have hQCD : Q ⊓ centralizer (residual L r : Set G) = E := by
    apply le_antisymm
    · intro x hx
      have hxp : x ∈ (P : Set G) * (E : Set G) := by
        rw [← coe_mul_of_left_le_normalizer_right _ _
          (hPE.trans (centralizer_le_normalizer _))]
        exact hx.1
      obtain ⟨p,hp,e,he,rfl⟩ := hxp
      have hpc : p ∈ centralizer (residual L r : Set G) := by
        have hh := (centralizer (residual L r : Set G)).mul_mem hx.2
          (hED (E.inv_mem he))
        simpa only [mul_inv_cancel_right] using hh
      have hp1 : p = 1 := mem_bot.mp (hPCD.le ⟨hp,hpc⟩)
      change p * e ∈ E
      rw [hp1, one_mul]
      exact he
    · exact le_inf le_sup_right hED
  have hnormalizer : (L ⊔ E) ⊓ normalizer (E : Set G) = residual L r ⊔ Q := by
    rw [centerless_local_normalizer_eq h hr hr2 hout hcenter d.actor_mem,
      ← d.centerlessEmbedding_fixed hcenter, hsupp, Subgroup.map_sup,
      d.centerlessEmbedding_model hcenter, sup_assoc]
  let : (E.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer hQN
  let q : P →* Q ⧸ E.subgroupOf Q :=
    (QuotientGroup.mk' (E.subgroupOf Q)).comp (inclusion (show P ≤ Q from le_sup_left))
  have hqi : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro p hp
    have hpE : (p : G) ∈ E :=
      (QuotientGroup.eq_one_iff (⟨p,mem_sup_left p.property⟩ : Q)).mp hp
    apply mem_bot.mpr
    exact Subtype.ext (disjoint_def.mp hdis p.property hpE)
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (E.subgroupOf Q) y
    have hxp : (x : G) ∈ (P : Set G) * (E : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _
        (hPE.trans (centralizer_le_normalizer _))]
      exact x.property
    obtain ⟨p,hp,e,he,hpe⟩ := hxp
    let pQ : Q := ⟨p,mem_sup_left hp⟩
    let eQ : Q := ⟨e,mem_sup_right he⟩
    have hx : x = pQ * eQ := Subtype.ext hpe.symm
    have he1 : QuotientGroup.mk' (E.subgroupOf Q) eQ = 1 :=
      (QuotientGroup.eq_one_iff eQ).mpr he
    refine ⟨⟨p,hp⟩, ?_⟩
    rw [hx, map_mul, he1, mul_one]
    rfl
  have hquot : Nonempty ((Q ⧸ E.subgroupOf Q) ≃* QuaternionGroup 2) :=
    ⟨(MulEquiv.ofBijective q ⟨hqi,hqs⟩).symm.trans eP⟩
  refine {
    Q := Q, two_group := hQtwo, four_le := le_sup_right,
    le_product := sup_le_sup_right hPL E, normalizes_four := hQN,
    normalizes_residual := hQND, normalizer_eq := hnormalizer, centralizer_eq := hQCD,
    quotient_quaternion := hquot, centralizes_four := hQE,
    P := P, le_Q := le_sup_left, disjoint_four := hdis, sup_four := rfl,
    quaternion := ⟨eP⟩, frattini_product := ?_ }
  let uP : P := ⟨f u,mem_map_of_mem f u.property⟩
  have huPhi : uP ^ 2 ∈ frattini P := by
    rw [hPtwo.frattini_eq_closure_squares]
    exact subset_closure ⟨uP,rfl⟩
  have hu2 : orderOf (f (u : PSL) ^ 2) = 2 := by
    rw [← map_pow, orderOf_injective f hf, orderOf_pow, hu]
    rfl
  have huv : f (u : PSL) ^ 2 ∈ L ⊓ centralizer ({r} : Set G) :=
    hPD (P.pow_mem (mem_map_of_mem f u.property) 2)
  refine ⟨f (u : PSL) ^ 2, ⟨uP ^ 2,huPhi,rfl⟩, hu2, huv,
    f s, ((d.centerlessEquiv hcenter).symm s).property, ?_⟩
  have he := congrArg f hs
  simp only [map_mul, map_pow] at he
  rw [d.centerlessEmbedding_action, map_inv] at he
  change f s * (r * (f s)⁻¹ * r⁻¹) = f (u : PSL) ^ 2 at he
  have he' : f s * r * (f s)⁻¹ = f (u : PSL) ^ 2 * r := by
    apply (mul_inv_eq_iff_eq_mul).mp
    simpa only [mul_assoc] using he
  exact he'.trans (mem_centralizer_singleton_iff.mp huv.2)

open Matrix.PSL3Four.InnerFamilyNormalizer.Centerless in
/-- Construct the actual centerless normalizer, quaternion complement and fusion
witness from the source hypotheses and its permitted 16.1.4(5) residual inputs. -/
noncomputable def centerlessLocalData {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G) (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hmodel : IsL3FourGraphField L r) (hcore : pCore 2 L = ⊥)
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9) :
    CenterlessLocalData L r z := by
  apply Classical.choice
  obtain ⟨eB⟩ := quaternion_equiv
  obtain ⟨s,hs⟩ := exists_fusion
  exact ⟨centerlessLocalData_of_projective h hr hr2 hout
    (centerless_center_eq_bot hG h hcore) (markedCover hG h hmodel hD h9)
    quaternion quaternion_le_fixed eB fixed_eq_model_sup_quaternion
    quaternion_inf_centralizer_model ⟨i,i_mem_quaternion⟩ i_order s
    (hs.trans i_sq_projective.symm)⟩


end CFSG.Quasithin.Chapter16.Intersections.GraphField.NormalizerModels

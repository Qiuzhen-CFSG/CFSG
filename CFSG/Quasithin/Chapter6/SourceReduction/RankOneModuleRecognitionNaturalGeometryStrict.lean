module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryMultiplicity
public import Theory.SpecificGroups.SL2.SylowPointFixer
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple

/-!
# Strictness of the escaping natural section

If E = R, then R = C_U(V_L) is elementary. A nonidentity root element has
exactly the root group's fixed vectors on the original natural layer.
Together with the moving-pair product, this puts every involution of U in
R or its I-conjugate C_U(V_L^g). These two subgroups have equal order, so
I permutes them. The Sylow intersection fixes R; its odd index forces I
to fix R too. Since LT normalizes the nontrivial two-subgroup R, uniqueness
of the maximal two-local overgroup of LT now puts I in M, a contradiction.

Thus E < R on the literal G.2.3 section. In field four, the previously
constructed common multiplicity is consequently positive. The Chapter 12
consumer discharges the E.6.1, rank and central-line normalizer premises.
The initial natural action and escaping nonabelianness remain earlier
source obligations of qt-d-1222-rankone-recognition-natural, as do the
parameter reduction and marked PSL₂ prime component. No conclusion of
6.1.25 or 6.1.27 is assumed or asserted here.

Source: Aschbacher–Smith, 6.1.20–22 and the paragraph before 6.1.24,
printed pp.675–676, using the actual natural action in G.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterG.Section02.RankOneHigherFields
variable {G : Type*} [Group G] [Finite G]

private theorem seed_fixed_by_root {D : ChapterG.Section02.Setup G}
    {F : Type*} [Field F] [Finite F] {n : ℕ} {l : G}
    (d : Hypothesis D F n l) (hut : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    {a v : G} (ha : a ∈ D.U) (haout : a ∉ centralizer (D.V : Set G))
    (hv : v ∈ D.V) (hav : Commute a v) : v ∈ centralizer (D.U : Set G) := by
  let := d.field_char_two
  have hs := d.star_I_eq_star_L hut hf
  let q := d.quotientActionProjection hut hs
  have he (x : D.I l) (w : D.V) :
      q x • (d.coordinates w).toAdd = (d.coordinates w).toAdd ↔ Commute (x : G) (w : G) := by
    have heq := d.IStarProjection_equivariant hut hs x w
    change (d.coordinates _).toAdd = q x • (d.coordinates w).toAdd at heq
    rw [← heq, Multiplicative.toAdd.injective.eq_iff, d.coordinates.injective.eq_iff, Subtype.ext_iff]
    exact mul_inv_eq_iff_eq_mul
  let ai : D.I l := ⟨a,mem_sup_left ha⟩
  obtain ⟨P,hP⟩ := d.quotientRoot_sylow hut hs (d.exists_star_U_sylow hut hf)
  have hap : q ai ∈ P := by
    change q ai ∈ (P : Subgroup SL(2,F))
    rw [hP]
    exact mem_map_of_mem q ha
  have hane : q ai ≠ 1 := by
    intro hzero
    apply haout
    intro w hw
    exact ((he ai ⟨w,hw⟩).mp (by rw [hzero]; exact one_smul _ _)).eq.symm
  have hfix := Matrix.SpecialLinearGroup.sylow_fixed_of_nonidentity_fixed P (q ai) hap hane
    (d.coordinates ⟨v,hv⟩).toAdd ((he ai ⟨v,hv⟩).mpr hav)
  intro u hu
  have hup : q ⟨u,mem_sup_left hu⟩ ∈ (P : Subgroup SL(2,F)) := by
    rw [hP]
    exact mem_map_of_mem q hu
  exact ((he ⟨u,mem_sup_left hu⟩ ⟨v,hv⟩).mp (hfix _ hup)).eq


omit [Finite G] in
private theorem pair_involutions
    (B A U : Subgroup G) [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 A]
    [IsElementaryAbelian 2 (U ⊓ centralizer (B : Set G) : Subgroup G)]
    (hBU : B ≤ U) (hAU : A ≤ U)
    (hNB : U ≤ normalizer (B : Set G)) (hNA : U ≤ normalizer (A : Set G))
    (hprod : U = (B ⊔ A) ⊔ (U ⊓ centralizer ((B ⊔ A : Subgroup G) : Set G)))
    (hfix : ∀ a ∈ A, a ∉ centralizer (B : Set G) →
      ∀ b ∈ B, Commute a b → b ∈ centralizer (A : Set G)) :
    ∀ x ∈ U, x ^ 2 = 1 →
      x ∈ U ⊓ centralizer (B : Set G) ∨ x ∈ U ⊓ centralizer (A : Set G) := by
  let R := U ⊓ centralizer (B : Set G)
  let C := U ⊓ centralizer (A : Set G)
  have hBR : B ≤ R := le_inf hBU (le_centralizer _)
  have hAC : A ≤ C := le_inf hAU (le_centralizer _)
  have hAR : A ⊔ R = U := by
    apply le_antisymm (sup_le hAU inf_le_left)
    apply hprod.le.trans
    exact sup_le (sup_le (hBR.trans le_sup_right) le_sup_left)
      ((inf_le_inf_left U (centralizer_le (show B ≤ B ⊔ A from le_sup_left))).trans le_sup_right)
  have hBC : B ⊔ C = U := by
    apply le_antisymm (sup_le hBU inf_le_left)
    apply hprod.le.trans
    exact sup_le (sup_le le_sup_left (hAC.trans le_sup_right))
      ((inf_le_inf_left U (centralizer_le (show A ≤ B ⊔ A from le_sup_right))).trans le_sup_right)
  have hpow (K : Subgroup G) [IsElementaryAbelian 2 K] (x : G) (hx : x ∈ K) : x ^ 2 = 1 :=
    congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p (p := 2) (G := K)) ⟨x,hx⟩)
  intro x hx hx2
  have hxprod : x ∈ (A : Set G) * (R : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A R (inf_le_left.trans hNA),hAR]
    exact hx
  obtain ⟨a,ha,r,hr,rfl⟩ := hxprod
  by_cases haC : a ∈ centralizer (B : Set G)
  · exact Or.inl ((U ⊓ centralizer (B : Set G)).mul_mem ⟨hAU ha,haC⟩ hr)
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hpow R r hr)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hpow A a ha)
  have har : Commute a r := by
    have hi := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx2)
    rw [_root_.mul_inv_rev,hri,hai] at hi
    exact hi.symm
  have hrprod : r ∈ (B : Set G) * (C : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left B C (inf_le_left.trans hNB),hBC]
    exact hr.1
  obtain ⟨b,hb,c,hc,hbc⟩ := hrprod
  have hac : Commute a c := hc.2 a ha
  have hab : Commute a b := by
    have hh := har.mul_right hac.inv_right
    rw [← hbc,mul_inv_cancel_right] at hh
    exact hh
  have hbC : b ∈ C := ⟨hBU hb,hfix a ha haC b hb hab⟩
  exact Or.inr (C.mul_mem (hAC ha) (hbc ▸ C.mul_mem hbC hc))

private theorem normalizes_of_involution_pair
    (U R C I S : Subgroup G)
    [IsElementaryAbelian 2 R]
    (hRU : R ≤ U) (hcard : Nat.card C = Nat.card R)
    (hne : R ≠ C) (hIU : I ≤ normalizer (U : Set G))
    (hSR : S ≤ normalizer (R : Set G))
    (hodd : ¬ 2 ∣ S.relIndex I)
    (hcover : ∀ x ∈ U, x ^ 2 = 1 → x ∈ R ∨ x ∈ C) :
    I ≤ normalizer (R : Set G) := by
  have hperm (x : G) (hx : x ∈ I) :
      R.map (MulAut.conj x).toMonoidHom = R ∨ R.map (MulAut.conj x).toMonoidHom = C := by
    let f := (MulAut.conj x).toMonoidHom
    have hle : R.map f ≤ U := (map_mono hRU).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hIU hx))
    have he : IsElementaryAbelian 2 (R.map f) := IsElementaryAbelian.map f
    have hc : Nat.card (R.map f) = Nat.card R := card_map_of_injective (MulAut.conj x).injective
    have hh : (R.map f : Set G) ⊆ (R : Set G) ∪ C := by
      intro y hy
      exact hcover y (hle hy) (congrArg Subtype.val
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he.exponent_dvd_p ⟨y,hy⟩))
    rcases SubgroupClass.subset_union.mp hh with hR | hC
    · exact Or.inl (eq_of_le_of_card_ge hR hc.ge)
    · exact Or.inr (eq_of_le_of_card_ge hC (hc.trans hcard.symm).ge)
  by_contra hnot
  obtain ⟨a,ha,haout⟩ := SetLike.not_le_iff_exists.mp hnot
  have hswap := (hperm a ha).resolve_left (fun hh => haout (mem_normalizer_iff_map_conj_eq.mpr hh))
  have hi : (normalizer (R : Set G)).relIndex I = 2 := by
    apply relIndex_eq_two_iff_exists_notMem_and.mpr
    refine ⟨a,ha,haout,?_⟩
    intro b hb
    rcases hperm b hb with hfix | hmove
    · exact Or.inr (mem_normalizer_iff_map_conj_eq.mpr hfix)
    · left
      apply mem_normalizer_iff_map_conj_eq.mpr
      change R.conjBy (b*a) = R
      have hCb : C.conjBy b = R := by
        rcases hperm b⁻¹ (I.inv_mem hb) with hf | hm
        · have hh := congrArg (fun K : Subgroup G => K.conjBy b) hf
          change (R.conjBy b⁻¹).conjBy b = R.conjBy b at hh
          rw [conjBy_inv'] at hh
          exact False.elim (hne (hh.trans hmove))
        · have hh := congrArg (fun K : Subgroup G => K.conjBy b) hm
          change (R.conjBy b⁻¹).conjBy b = C.conjBy b at hh
          rw [conjBy_inv'] at hh
          exact hh.symm
      change R.conjBy a = C at hswap
      rw [conjBy_mul,hswap,hCb]
  apply hodd
  rw [← hi]
  exact relIndex_dvd_of_le_left I hSR

variable {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- Source 6.1.22, retaining the earlier natural action and nonabelianness
while proving strictness from the actual escaping centralizer. -/
theorem natural_escape_intersection_lt_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    (hI : ¬ Escape.I (T : Subgroup G) L V ≤ M)
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V) :
    Escape.E (T : Subgroup G) L V l < Escape.R (T : Subgroup G) L V l := by
  let D := naturalEscapeSetup (T : Subgroup G) L V
  let U := Escape.U (T : Subgroup G) L V
  let B := layer L V
  let R := Escape.R (T : Subgroup G) L V l
  let E := Escape.E (T : Subgroup G) L V l
  let I := Escape.I (T : Subgroup G) L V
  obtain ⟨F,_,_,⟨d⟩⟩ := natural_escape_G2_marking h hnatural hE hNS hnon hl hlout
  obtain ⟨hU,hJ,hR,hE'⟩ := natural_escape_G2_constructions h hE hNS l
  have hut : D.U ≤ D.T := by rw [hU]; exact natural_escape_U_le_sylow h hnatural
  have hf := (natural_escape_G2_hypothesis h hnatural).frattini_U_le_point
  have hER : E ≤ R := by
    have hh := (d.series hut hf).2.1
    rw [hR,hE'] at hh
    exact hh
  refine lt_of_le_of_ne hER ?_
  intro hEq
  have hReq : R = E := hEq.symm
  obtain ⟨_,hcore,helem,_,hnorm⟩ := natural_escape_core_geometry h hnatural hE hNS hnon hl hlout
  have hRU : R ≤ U := by rw [hReq]; exact inf_le_left
  have hRC : R = U ⊓ centralizer (B : Set G) := by
    apply le_antisymm (le_inf hRU ?_) (le_sup_left.trans_eq hcore.symm)
    change Escape.R (T : Subgroup G) L V l ≤ _
    rw [hcore]
    exact sup_le inf_le_right inf_le_right
  let : IsElementaryAbelian 2 B := h.layer_elementary
  let : IsElementaryAbelian 2 R := by rw [hReq]; exact helem
  let : IsElementaryAbelian 2 (U ⊓ centralizer (B : Set G) : Subgroup G) := hRC ▸ inferInstance
  obtain ⟨g,hg,hmove⟩ := natural_escape_exists_pair hnon
  let A := B.map (MulAut.conj g).toMonoidHom
  let C := U ⊓ centralizer (A : Set G)
  have hBU : B ≤ U := Escape.layer_le_U _ _ _
  obtain ⟨hAU,hNA⟩ := natural_escape_pair_normalizes h hnatural hg
  have hNB : U ≤ normalizer (B : Set G) :=
    (natural_escape_U_le_sylow h hnatural).trans h.sylow_normalizes_layer
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hRg : R.map (MulAut.conj g).toMonoidHom = C := by
    have hug : U.map (MulAut.conj g).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp (NaturalEscape.I_normalizes_U (T : Subgroup G) L V hg)
    rw [hRC,map_inf _ _ _ (MulAut.conj g).injective,
      Theory.Quasithin.map_centralizer,hug]
  let : IsElementaryAbelian 2 C := hRg ▸ IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hcard : Nat.card C = Nat.card R := by rw [←hRg]; exact card_map_of_injective (MulAut.conj g).injective
  have hne : R ≠ C := by
    intro he
    apply hmove
    have hCB : C ≤ centralizer (B : Set G) := by rw [←he,hRC]; exact inf_le_right
    exact (le_inf hAU (le_centralizer A) : A ≤ C).trans hCB
  have hcover : ∀ x ∈ U, x ^ 2 = 1 → x ∈ R ∨ x ∈ C := by
    rw [hRC]
    apply pair_involutions B A U hBU hAU hNB hNA
      (natural_escape_pair_product h hnatural hE hs hg hmove).1
    intro a ha haout b hb hab
    have ha' : a ∈ D.U := hU.symm ▸ hAU ha
    have hfixed := seed_fixed_by_root d hut hf ha' haout hb hab
    rw [hU] at hfixed
    exact centralizer_le hAU hfixed
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) :=
    h.sylow_normalizes_ZS.trans (normalizer_le_normalizer_centralizer _)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
  have hodd : ¬ 2 ∣ ((T : Subgroup G) ⊓ I).relIndex I := by
    have hp : ((T : Subgroup G) ⊓ I).subgroupOf I = (P : Subgroup I) := by
      rw [inf_subgroupOf_right]
      exact hP.symm
    change ¬ 2 ∣ (((T : Subgroup G) ⊓ I).subgroupOf I).index
    rw [hp]
    exact P.not_dvd_index
  have hIR : I ≤ normalizer (R : Set G) :=
    normalizes_of_involution_pair U R C I ((T : Subgroup G) ⊓ I)
      hRU hcard hne (NaturalEscape.I_normalizes_U _ _ _)
      (inf_le_left.trans (le_sup_right.trans hnorm)) hodd hcover
  have hRne : R ≠ ⊥ := by
    intro he
    have hBR : B ≤ R := by rw [hRC]; exact le_inf hBU (le_centralizer B)
    exact h.nontrivial_action (bot_unique (hBR.trans_eq he))
  have hRT : R ≤ (T : Subgroup G) := hRU.trans (natural_escape_U_le_sylow h hnatural)
  obtain ⟨N,hRN,hN⟩ := Finite.exists_le_maximal
    (show IsTwoLocal (normalizer (R : Set G)) from ⟨R,hRne,T.isPGroup'.to_le hRT,rfl⟩)
  have hstar : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.prop,?_⟩
    intro K hK hLK
    exact le_antisymm (h.local_mem.1.2 hK hLK) hLK
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.simpleQTKE T hstar
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl h.sylow_normalizes_L)
      (le_componentOrbit L T)
  have h1 := hu.normalizer_unique N hN
  have h2 := hu.normalizer_unique M h.maximal
  rw [horbit] at h1 h2
  have hNM : N = M := (h1 (hnorm.trans hRN)).trans (h2 (sup_le h.L_le h.sylow_le)).symm
  exact hI ((hIR.trans hRN).trans_eq hNM)

/-- Strictness excludes multiplicity zero in the actual field-four section. -/
theorem natural_escape_four_positive_multiplicity
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V 2)
    (hnatural : IsNaturalModule L (layer L V) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = 2)
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    (hI : ¬ Escape.I (T : Subgroup G) L V ≤ M)
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V) :
    ∃ s : ℕ, 0 < s ∧
      (Escape.E (T : Subgroup G) L V l).relIndex
        (Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G)) = 2 ^ (2 * s) ∧
      (Escape.E (T : Subgroup G) L V l).relIndex (Escape.R (T : Subgroup G) L V l) =
        2 ^ (4 * s) ∧
      Nat.card (Escape.U (T : Subgroup G) L V) =
        2 ^ (2 * (s + 3)) * (layer L V).relIndex (Escape.E (T : Subgroup G) L V l) := by
  obtain ⟨s,hi,hr,hc⟩ := natural_escape_four_multiplicity h hnatural hE hNS hnon hl hlout
  refine ⟨s,?_,hi,hr,hc⟩
  have hlt := natural_escape_intersection_lt_core h hnatural hE hs hNS hnon hI hl hlout
  by_contra hz
  have he : s = 0 := by omega
  rw [he,mul_zero,pow_zero] at hr
  exact hlt.not_ge (relIndex_eq_one.mp hr)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

module
public import Stellmacher.SectionNine.NineNinePreterminalCoatom
public import Theory.GroupAction.InvolutionCentralizingCoatom
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The extracted preterminal transvection in (9.9)

The actual preterminal neighbor extraction supplies an index-two coatom in the
preceding module. Its center centralizes that coatom. The neighbor center has
an element outside the preceding core: otherwise the full center commutator
would lie in the preceding order-two center and in the preterminal module,
contradicting the proved opposite center exclusion.

The selected involution fixes the coatom, so involution rank-nullity bounds its
commutator by two. The exact quotient-action kernel excludes containment in
the preceding center, hence both the ambient commutator and its displacement
modulo that center have order two. The commutator lies in the preterminal
module, which centralizes the selected terminal support; maximal-intersection
transport therefore puts it in the original first-step module.

This is the transvection packet immediately before the application of (9.5)
in Stellmacher (9.9), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`. The actual ambient (9.8) bound and the
transported (9.7) index bound remain explicit inputs.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_preterminal_transvection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (bound : ∀ shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B,
      ZAt shifted.Γ shifted.criticalPath.a' ≤
        VAt shifted.Γ shifted.criticalPath.firstStep → shifted.criticalPath.length ≤ 3)
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card (VAt ctx.Γ previous ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤ Nat.card (VAt ctx.Γ previous)) :
    let preterminal := ctx.criticalPath.path ⟨ctx.criticalPath.length - 2,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    ∃ (neighbor : ctx.Γ.Vertex) (actor : G),
      neighbor ∈ Neighborhood ctx.Γ preterminal ∧
      actor ∈ ZAt ctx.Γ neighbor ∧ actor ∉ QAt ctx.Γ previous ∧
      Nat.card (⁅VAt ctx.Γ previous, Subgroup.zpowers actor⁆ : Subgroup G) = 2 ∧
      QuotientCardEq (⁅VAt ctx.Γ previous, Subgroup.zpowers actor⁆ ⊔ ZAt ctx.Γ previous)
        (ZAt ctx.Γ previous) 2 ∧
      ⁅VAt ctx.Γ previous, Subgroup.zpowers actor⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let preterminal := cp.path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let B := VAt Γ previous
  let Z := ZAt Γ previous
  let V := VAt Γ preterminal
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hlong : 4 < cp.length := by
    have hh := nine_ten_length_ge_five ctx.toLocalContext hb
    change 5 ≤ cp.length at hh
    omega
  obtain ⟨neighbor,hneighbor,hindex,_,hnoncomm⟩ :=
    nine_nine_preterminal_extracted_neighbor ctx hb hcore previous hprevious hne hlarge
  have hnot := nine_nine_preterminal_center_not_le_previous_module bound ctx hb hcore
    previous hprevious hne hlarge
  obtain ⟨hcenterP,hcoatom⟩ := nine_nine_preterminal_neighbor_centralizes_coatom
    ctx hb previous hprevious neighbor hneighbor hnot
  obtain ⟨mover,hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hprevious
  have horbit : IsConjugateVertex Γ cp.firstStep previous := ⟨mover,hmover⟩
  let _ : IsElementaryAbelian 2 B := by
    change IsElementaryAbelian 2 (v Γ previous)
    rw [← hmover,v_act]
    let _ : IsElementaryAbelian 2 (v Γ cp.firstStep) :=
      ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
    exact IsElementaryAbelian.map (MulAut.conj (mover:G)⁻¹).toMonoidHom
  obtain ⟨hZcard,hBQ,hkernel⟩ := nine_next_center_commutator_and_kernel ctx hshort previous horbit
  have hBpre : B ≤ GAt Γ preterminal :=
    (nine_eight_v_le_generated_neighborhood Γ hprevious).trans
      (nine_eight_neighborhood_le_preterminal ctx.toLocalContext hlong cp.a
        ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)))
  have hcenterV : ZAt Γ neighbor ≤ V := by
    change z Γ neighbor ≤ v Γ preterminal
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨neighbor,hneighbor,rfl⟩
  have hcommV : ⁅B,ZAt Γ neighbor⁆ ≤ V := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hcenterV le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hBpre.trans (stabilizer_le_normalizer_v Γ preterminal)))
  have hcenterNot : ¬ ZAt Γ neighbor ≤ QAt Γ previous := by
    intro hle
    have hbound : ⁅B,ZAt Γ neighbor⁆ ≤ Z :=
      (Subgroup.commutator_mono le_rfl hle).trans_eq hBQ
    have hnonzero : ⁅B,ZAt Γ neighbor⁆ ≠ ⊥ := by
      simpa only [Subgroup.commutator_comm] using hnoncomm
    have hpositive := (Subgroup.one_lt_card_iff_ne_bot _).mpr hnonzero
    have heq : ⁅B,ZAt Γ neighbor⁆ = Z := Subgroup.eq_of_le_of_card_ge hbound (by
      change Nat.card Z = 2 at hZcard
      omega)
    apply nine_nine_previous_center_not_le_preterminal_module ctx hb hcore previous hprevious hne
    change Z ≤ V
    exact heq ▸ hcommV
  obtain ⟨actor,hactor,hactorNot⟩ := SetLike.not_le_iff_exists.mp hcenterNot
  have hactorP := hcenterP hactor
  have hcyclic : Subgroup.zpowers actor ≤ ZAt Γ neighbor := Subgroup.zpowers_le.mpr hactor
  have hnormal : Subgroup.zpowers actor ≤ Subgroup.normalizer (B : Set G) :=
    (hcyclic.trans hcenterP).trans (stabilizer_le_normalizer_v Γ previous)
  let _ : IsElementaryAbelian 2 (ZAt Γ neighbor) :=
    z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ
      ((mem_neighborhood_iff_adjacent Γ).mpr
        (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor)))
  have hinvolution : actor ≠ 1 ∧ actor ^ 2 = 1 :=
    ⟨fun hone => hactorNot (hone ▸ (QAt Γ previous).one_mem),
      elemPow_eq_one_of_isElementaryAbelian actor hactor⟩
  let K := B ⊓ GAt Γ neighbor
  let R := ⁅B,Subgroup.zpowers actor⁆
  have hKcentral : K ≤ Subgroup.centralizer (Subgroup.zpowers actor : Set G) :=
    (Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcoatom)).trans
        (Subgroup.centralizer_le hcyclic)
  have hbound : Nat.card R ≤ 2 := Subgroup.commutator_card_le_two_of_centralizing_index_two
    B K actor hinvolution hnormal inf_le_left hindex hKcentral
  have hRnot : ¬ R ≤ Z := fun hle => hactorNot ((hkernel actor hactorP).mp hle)
  have hRne : R ≠ ⊥ := fun heq => hRnot (heq ▸ bot_le)
  have hRcard : Nat.card R = 2 := by
    have hpositive := (Subgroup.one_lt_card_iff_ne_bot R).mpr hRne
    omega
  have hRZ : R ⊓ Z = ⊥ := by
    by_contra hne
    have hpositive := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    have heq : R ⊓ Z = R := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact hRnot (heq ▸ inf_le_right)
  have hRB : R ≤ B := Subgroup.le_normalizer_iff_commutator_le_left.mp hnormal
  have hQP : QAt Γ previous ≤ GAt Γ previous := by
    rw [QAt,q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZB : Z ≤ B := by
    change ZAt ctx.Γ previous ≤ VAt ctx.Γ previous
    rw [← hBQ]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQP.trans (stabilizer_le_normalizer_v Γ previous))
  have hab : B ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hnormalize : R ≤ Subgroup.normalizer (Z : Set G) :=
    hRB.trans (hab.trans ((Subgroup.centralizer_le hZB).trans
      (Subgroup.centralizer_le_normalizer _)))
  have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes Z R hnormalize
  rw [inf_comm,hRZ,Subgroup.card_bot,hRcard,one_mul,sup_comm] at hcard
  have hquot : QuotientCardEq (R ⊔ Z) Z 2 := by
    change Nat.card (R ⊔ Z : Subgroup G) = 2 * Nat.card Z
    rw [← hcard,Nat.mul_comm]
  obtain ⟨support,hsupport,hsupportComm,_⟩ := nine_nine_support_of_terminal_core ctx hshort hcore
  have hRV : R ≤ V := (Subgroup.commutator_mono le_rfl hcyclic).trans hcommV
  have hzero : ⁅R,support⁆ = ⊥ := le_bot_iff.mp
    ((Subgroup.commutator_mono hRV hsupport).trans_eq
      (nine_nine_terminal_modules_commute ctx.toLocalContext hb))
  have hRmax := (le_nineNineCommutatorBound_iff B support (ZAt Γ cp.firstStep) R
    (nine_nine_previous_normalizes_first_center ctx.toLocalContext hb previous hprevious)).mpr
      ⟨hRB,hzero.le.trans bot_le⟩
  rw [nine_nine_maximal_eq_intersection ctx hb support (hsupport.trans hcore)
    hsupportComm previous hprevious hne] at hRmax
  exact ⟨neighbor,actor,hneighbor,hactor,hactorNot,hRcard,hquot,hRmax.trans inf_le_right⟩

end Stellmacher.SectionNine

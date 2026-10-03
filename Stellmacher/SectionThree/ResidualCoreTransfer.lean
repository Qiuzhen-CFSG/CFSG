module
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Theory.ThreeSubgroups

/-!
# Residual-core transfer from Stellmacher (3.4)

For a solvable `P ∈ ℘(S)`, let `T ◁ S` lie outside `O₂(P)`, and assume
`N = T ∩ O₂(P)` is normal in `P`. Then `O₂(O²(P)) ≤ N`. The primary
transfer theorem uses solvability and the defining properties of `℘(S)`.
The original `residual_core_transfer` interface retains its characteristic-two
premise as a wrapper; that premise is not used in the underlying proof.

The proof of Stellmacher (7.6), Journal of Algebra 190 (1997), pp. 35–36,
compresses this transfer into an application of (3.4). Here (3.4) first gives
`[O²(P),T] = O²(P)`. Since `[O₂(P),T] ≤ N`, the relative three-subgroups
lemma implies `[O²(P),O₂(P)] ≤ N`. The quotient of `O²(P)` by its
intersection with `N` therefore has central kernel over the odd-prime
residual image in `P/O₂(P)` supplied by (3.3), so is nilpotent. Residual
idempotence makes that quotient 2-residual-perfect, and its normal
2-complement forces its order to be odd. The image of its 2-core is trivial,
giving the required containment. No assertion that characteristic two
descends through arbitrary normal 2-subgroup quotients is used.
-/

open Stellmacher BenderSuzuki.External
open scoped commutatorElement

private theorem core_le_of_residual_perfect_central_kernel
    {R H : Type*} [Group R] [Group H] [Finite R]
    [Group.IsNilpotent H]
    (f : R →* H) (N : Subgroup R) [N.Normal]
    (hN : N ≤ f.ker) (hcomm : ⁅f.ker, ⊤⁆ ≤ N)
    (hres : hktPResidual 2 R = ⊤) : pCore 2 R ≤ N := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : R →* R ⧸ N := QuotientGroup.mk' N
  let fbar : R ⧸ N →* H := QuotientGroup.lift N f hN
  have hker : fbar.ker ≤ Subgroup.center (R ⧸ N) := by
    intro x hx
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hr : r ∈ f.ker := hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hc : ⁅r, s⁆ ∈ N := hcomm
      (Subgroup.commutator_mem_commutator hr (show s ∈ (⊤ : Subgroup R) from trivial))
    have hcq : ⁅q r, q s⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 hc
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcq).symm
  have hnil : Group.IsNilpotent (R ⧸ N) :=
    Subgroup.isNilpotent_of_ker_le_center fbar hker
  have hodd : ¬ 2 ∣ Nat.card (R ⧸ N) := by
    intro hdvd
    exact (hktPResidual_ne_top_of_hasNormalPComplement_of_dvd_card
      (hkt_hasNormalPComplement_of_nilpotent hnil) hdvd)
        (hktPResidual_quotient_eq_top_of_eq_top N hres)
  have hmap2 := (pCore_isPGroup (p := 2) (G := R)).map q
  have hmapbot : (pCore 2 R).map q = ⊥ := by
    rcases hmap2.card_eq_or_dvd with hcard | hdvd
    · exact Subgroup.card_eq_one.mp hcard
    · exact False.elim (hodd (hdvd.trans (Subgroup.card_subgroup_dvd_card _)))
  have hle := (Subgroup.map_eq_bot_iff _).1 hmapbot
  simpa [q, QuotientGroup.ker_mk'] using hle

namespace Stellmacher.SectionThree

/-- The residual 2-core lies in a normal intersection with a Sylow-normal subgroup. -/
public theorem residual_core_transfer_of_solvable
    {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (T : Subgroup G) (hT : T ≤ S ∧ (T.subgroupOf S).Normal)
    (hsolv : Group.IsSolvable P)
    (hNnormal : ((T ⊓ twoCoreAmbient P).subgroupOf P).Normal)
    (hTnot : ¬ T ≤ twoCoreAmbient P) :
    twoCoreAmbient (twoResidualAmbient P) ≤ T ⊓ twoCoreAmbient P := by
  classical
  let Q := twoCoreAmbient P
  let R := twoResidualAmbient P
  let N := T ⊓ Q
  have hQP : Q ≤ P := Subgroup.map_subtype_le _
  have hRP : R ≤ P := Subgroup.map_subtype_le _
  obtain ⟨SP, hSP⟩ := hP.1.2.1
  have hSPle : S ≤ P := by
    rw [← hSP]
    exact Subgroup.map_subtype_le _
  have hTP : T ≤ P := hT.1.trans hSPle
  have hQS : Q ≤ S := by
    rw [← hSP]
    exact Subgroup.map_mono
      (IsPGroup.le_sylow_of_normal (pCore_isPGroup (p := 2)) SP)
  have hPnormQ : P ≤ Subgroup.normalizer Q := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mp
    have heq : Q.subgroupOf P = pCore 2 P := by
      dsimp [Q, twoCoreAmbient]
      exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
    rw [heq]
    infer_instance
  have hPnormN : P ≤ Subgroup.normalizer N :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_right.trans hQP)).mp hNnormal
  have hSnormT : S ≤ Subgroup.normalizer T :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT.1).mp hT.2
  have hQT : ⁅Q, T⁆ ≤ N := by
    exact le_inf
      (Subgroup.le_normalizer_iff_commutator_le_right.mp (hQS.trans hSnormT))
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hTP.trans hPnormQ))
  have hQR : ⁅Q, R⁆ ≤ Q :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hRP.trans hPnormQ)
  have hcomm : ⁅R, T⁆ = R := (lemma_three_four S h P hP T hT hsolv).resolve_left hTnot
  have hRQ : ⁅R, Q⁆ ≤ N := by
    rw [← hcomm]
    apply Subgroup.commutator_commutator_le_of_rotate_of_le_normalizer
      (hRP.trans hPnormN) (hTP.trans hPnormN) (hQP.trans hPnormN)
    · have hTQ : ⁅T, Q⁆ ≤ N := by simpa [Subgroup.commutator_comm] using hQT
      exact (Subgroup.commutator_mono hTQ le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hRP.trans hPnormN))
    · exact (Subgroup.commutator_mono hQR le_rfl).trans hQT
  obtain ⟨B, hB, hSB, hBuniq⟩ := hP.2
  have hSB' : S.subgroupOf P ≤ B := by
    intro s hs
    obtain ⟨b, hb, hbs⟩ := hSB hs
    have heq : b = s := P.subtype_injective hbs
    simpa [heq] using hb
  have hBuniq' : ∀ B' : Subgroup P, IsCoatom B' → S.subgroupOf P ≤ B' → B' = B := by
    intro B' hB' hSB'
    apply hBuniq B' hB'
    rw [← Subgroup.map_subgroupOf_eq_of_le hSPle]
    exact Subgroup.map_mono hSB'
  have h33 := lemma_three_three S h P hP B B.normalCore
    ⟨hB, hSB', hBuniq'⟩
    ⟨B.normalCore_le, inferInstance, fun N hN hNB =>
      @Subgroup.normal_le_normalCore P _ B N hN |>.mpr hNB⟩ hsolv
  obtain ⟨p, hp, _, hpgroup⟩ := h33.part_a
  let Rbar : Subgroup (P ⧸ pCore 2 P) :=
    twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P))
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Group.IsNilpotent Rbar := hpgroup.isNilpotent
  let qO : P →* P ⧸ pCore 2 P := QuotientGroup.mk' (pCore 2 P)
  have hRtop : (twoResidualAmbient (⊤ : Subgroup P)).map P.subtype = R := by
    apply map_twoResidualAmbient_of_subgroup_image
    exact (MonoidHom.range_eq_map P.subtype).symm.trans (Subgroup.range_subtype P)
  have hRO : (R.subgroupOf P).map qO = Rbar := by
    have hReq : R.subgroupOf P = twoResidualAmbient (⊤ : Subgroup P) := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hRP, hRtop]
    rw [hReq]
    apply map_twoResidualAmbient_of_subgroup_image
    exact Subgroup.map_top_of_surjective qO (QuotientGroup.mk'_surjective _)
  let f₀ : R →* P ⧸ pCore 2 P := qO.comp (Subgroup.inclusion hRP)
  let f : R →* Rbar := f₀.codRestrict Rbar (fun r => by
    rw [← hRO]
    exact Subgroup.mem_map_of_mem qO r.property)
  have hker (r : R) : r ∈ f.ker ↔ (r : G) ∈ Q := by
    change f r = 1 ↔ (r : G) ∈ Q
    rw [Subtype.ext_iff]
    change qO (Subgroup.inclusion hRP r) = 1 ↔ (r : G) ∈ Q
    dsimp [qO]
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hr
      exact Subgroup.mem_map_of_mem P.subtype hr
    · rintro ⟨x, hx, hxr⟩
      have heq : x = Subgroup.inclusion hRP r := P.subtype_injective hxr
      simpa [heq] using hx
  let NR := N.subgroupOf R
  let _ : NR.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hRP.trans hPnormN)
  have hNRker : NR ≤ f.ker := fun r hr => (hker r).2 hr.2
  have hkerMap : f.ker.map R.subtype ≤ Q := by
    rintro x ⟨r, hr, rfl⟩
    exact (hker r).1 hr
  have hkerComm : ⁅f.ker, ⊤⁆ ≤ NR := by
    intro r hr
    have hm := Subgroup.mem_map_of_mem R.subtype hr
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hm
    exact (show ⁅Q, R⁆ ≤ N by simpa [Subgroup.commutator_comm] using hRQ)
      (Subgroup.commutator_mono hkerMap le_rfl hm)
  have hcore : pCore 2 R ≤ NR := core_le_of_residual_perfect_central_kernel
    f NR hNRker hkerComm (twoResidualAmbient_has_top_twoResidual P)
  rintro x ⟨r, hr, rfl⟩
  exact hcore hr

/-- The original characteristic-two interface, retained as a compatibility wrapper. -/
public theorem residual_core_transfer
    {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (T : Subgroup G) (hT : T ≤ S ∧ (T.subgroupOf S).Normal)
    (hsolv : Group.IsSolvable P)
    (_hchar : Stellmacher.IsCharacteristicTwoType P)
    (hNnormal : ((T ⊓ twoCoreAmbient P).subgroupOf P).Normal)
    (hTnot : ¬ T ≤ twoCoreAmbient P) :
    twoCoreAmbient (twoResidualAmbient P) ≤ T ⊓ twoCoreAmbient P :=
  residual_core_transfer_of_solvable S h P hP T hT hsolv hNnormal hTnot

end Stellmacher.SectionThree


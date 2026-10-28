module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Source.Center
public import BenderSuzuki.SE.Borel

/-!
# Recognition of the nonsolvable distinguished circle

Apply minimality to the proper local overgroup. Nonsolvability excludes
the rank-one alternative. In the structural alternative, the extra cyclic
factor becomes central modulo the odd core. Strong embedding in that
quotient forces this factor to be trivial. The circle is consequently
perfect and its quotient is the actual simple Bender model supplied by
induction; the same isomorphism transports the Borel subgroup.

Source: GLS, Volume 4, Chapter 2, Corollary 7.13(b).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Proper-subgroup induction recognizes the whole local odd-core quotient,
not merely an unconnected simple factor. -/
public theorem localCircle_perfect_and_bender_oddCore
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (F : Subgroup G) (hF : F ≠ ⊤) (hFM : ¬ F ≤ M)
    (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M)
    (hns : ¬ Group.IsSolvable (localCircle Z F)) :
    commutator (localCircle Z F) = ⊤ ∧
      IsSimpleBenderGroup (localCircle Z F ⧸ pPrimeCore 2 (localCircle Z F)) ∧
      IsBorelSubgroup ((M.comap (localCircleHom Z F)).map
        (QuotientGroup.mk' (pPrimeCore 2 (localCircle Z F)))) := by
  let C := Subgroup.closure (F.subtype ⁻¹' Z)
  let Y : Subgroup C := (M.comap F.subtype).comap C.subtype
  let N := pPrimeCore 2 C
  let q := QuotientGroup.mk' N
  let Q := C ⧸ N
  let X := commutator Q
  have hs : IsStronglyEmbedded Y := r.local_embedding F hF hFM hne
  have hgenC := localCircle_involutionCore_eq_top h.disconnected F
  have hrY := hs.twoRankAtLeastTwo_of_not_solvable_of_involutionCore_eq_top hgenC hns
  have hrC : TwoRankAtLeastTwo C := hrY.map_of_injective Y.subtype Y.subtype_injective
  have hstr : StructureConclusion (F.subtype ⁻¹' Z) (M.comap F.subtype) :=
    (h.conclusion_subgroup F hF hFM hne).resolve_left (not_not.mpr hrC)
  obtain ⟨u, huY, hu2, hgen, hgenQ, _, hcomm, hmodel, hN, hBorel, _⟩ := hstr
  change u ∈ Y at huY
  change commutator C ⊔ Subgroup.zpowers u = ⊤ at hgen
  change X ⊔ Subgroup.zpowers (q u) = ⊤ at hgenQ
  change ∀ x ∈ X, ∀ v ∈ Subgroup.zpowers (q u), Commute x v at hcomm
  change IsSimpleBenderGroup X at hmodel
  change N ≤ Y ⊓ commutator C at hN
  change IsBorelSubgroup (((Y ⊓ commutator C).map q).subgroupOf X) at hBorel
  have hodd : Odd (Nat.card N) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hsQ := hs.map_quotient_of_odd_kernel (hN.trans inf_le_left) hodd
  have hc : q u ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro a
    have hle : X ⊔ Subgroup.zpowers (q u) ≤ Subgroup.centralizer ({q u} : Set Q) := by
      refine sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
        (hcomm x hx (q u) (Subgroup.mem_zpowers _)).eq) ?_
      exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    rw [hgenQ] at hle
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top a))
  have hqu : q u = 1 := by
    by_contra hqu
    have hqi : IsInvolution (q u) := ⟨hqu, by rw [← map_pow, hu2, map_one]⟩
    apply hsQ.ne_top
    apply top_unique
    intro a _
    exact hsQ.centralizer_le (Subgroup.mem_map_of_mem q huY) hqi
      (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hc a))
  have hu : u = 1 := by
    by_contra hu
    exact (IsInvolution.quotient_mk_of_odd_kernel N hodd ⟨hu, hu2⟩).ne_one hqu
  have hperfect : commutator C = ⊤ := by simpa only [hu, Subgroup.zpowers_one_eq_bot, sup_bot_eq] using hgen
  have hX : X = ⊤ := by simpa only [hqu, Subgroup.zpowers_one_eq_bot, sup_bot_eq] using hgenQ
  let e : X ≃* Q :=
    { toFun := fun x => x
      invFun := fun x => ⟨x, hX ▸ Subgroup.mem_top x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hB : (((Y ⊓ commutator C).map q).subgroupOf X).map e.toMonoidHom = Y.map q := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, heq⟩ := hx
      exact ⟨y, hy.1, heq⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨q y, hX ▸ Subgroup.mem_top _⟩, ?_, rfl⟩
      exact ⟨y, ⟨hy, hperfect ▸ Subgroup.mem_top y⟩, rfl⟩
  exact ⟨hperfect, hmodel.map_mulEquiv e, hB ▸ hBorel.map_mulEquiv e⟩

/-- The central quotient, with its Borel witness and perfect cover, is the
nonsolvable structural alternative of Corollary 7.13. -/
public theorem localCircle_nonsolvable_structure
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (F : Subgroup G) (hF : F ≠ ⊤) (hFM : ¬ F ≤ M)
    (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M)
    (hns : ¬ Group.IsSolvable (localCircle Z F)) :
    pPrimeCore 2 (localCircle Z F) = Subgroup.center (localCircle Z F) ∧
      commutator (localCircle Z F) = ⊤ ∧
      IsSimpleBenderGroup (localCircle Z F ⧸ Subgroup.center (localCircle Z F)) ∧
      IsBorelSubgroup ((M.comap (localCircleHom Z F)).map
        (QuotientGroup.mk' (Subgroup.center (localCircle Z F)))) := by
  have hc := localCircle_oddCore_eq_center h.disconnected r ha F hF hFM hne hns
  have hp := localCircle_perfect_and_bender_oddCore h r F hF hFM hne hns
  let e := QuotientGroup.quotientMulEquivOfEq hc
  have he : e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 (localCircle Z F))) =
      QuotientGroup.mk' (Subgroup.center (localCircle Z F)) := by
    ext x
    exact QuotientGroup.quotientMulEquivOfEq_mk hc x
  have hb := hp.2.2.map_mulEquiv e
  rw [Subgroup.map_map, he] at hb
  exact ⟨hc, hp.1, hp.2.1.map_mulEquiv e, hb⟩

/-- The nonsolvable circle acts doubly transitively on the full orbit
`α^F`, correcting the punctured-orbit wording of the printed statement. -/
public theorem localCircle_twoTransitiveOn
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (F : Subgroup G) (hF : F ≠ ⊤) (hFM : ¬ F ≤ M)
    (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M)
    (hns : ¬ Group.IsSolvable (localCircle Z F)) :
    IsTwoTransitiveOn (localCircleIn Z F)
      {beta : G ⧸ M | InOrbit F (QuotientGroup.mk 1) beta} := by
  let C := localCircle Z F
  let A := localCircleIn Z F
  let Y : Subgroup C := (M.comap F.subtype).comap C.subtype
  let YA := M.comap A.subtype
  let N := pPrimeCore 2 C
  have hp := localCircle_perfect_and_bender_oddCore h r F hF hFM hne hns
  have htwo : MulAction.IsMultiplyPretransitive C (C ⧸ Y) 2 := by
    apply coset_isTwoPretransitive_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) Y
    · rw [QuotientGroup.ker_mk']
      exact localCircle_oddCore_le h.disconnected r F hF hFM hne hns
    · exact simpleBender_borel_coset_twoTransitive hp.2.2 hp.2.1
  let e : C ≃* A := Subgroup.equivMapOfInjective C F.subtype F.subtype_injective
  have hi : ∀ x : A, localCircleHom Z F (e.symm x) = (x : G) := by
    intro x
    exact congrArg A.subtype (e.apply_symm_apply x)
  have hmap : YA.map e.symm.toMonoidHom = Y := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      change localCircleHom Z F (e.symm x) ∈ M
      rw [hi]
      exact hx
    · intro hc
      exact ⟨e c, hc, e.symm_apply_apply c⟩
  have htwoA : MulAction.IsMultiplyPretransitive A (A ⧸ YA) 2 := by
    apply coset_isTwoPretransitive_of_mulEquiv e.symm YA
    rwa [hmap]
  have hpoint : pointStabilizerIn A (QuotientGroup.mk 1 : G ⧸ M) = YA := by
    ext x
    simp [pointStabilizerIn, YA]
  have htwoOrbit := isTwoTransitiveOn_orbit_of_coset A (QuotientGroup.mk 1 : G ⧸ M)
    (by rw [hpoint]; exact htwoA)
  exact twoTransitiveOn_orbit_of_orbit_iff F A (QuotientGroup.mk 1)
    (localCircle_orbit_iff h.disconnected r F hF hFM hne) htwoOrbit

open scoped Pointwise in
/-- The final factorization in Corollary 7.13(b), for every nonbase point
in the full orbit. Both stabilizers refer to the ambient coset action. -/
public theorem localCircle_twoPoint_factorization
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (F : Subgroup G) (hF : F ≠ ⊤) (hFM : ¬ F ≤ M)
    (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M)
    (hns : ¬ Group.IsSolvable (localCircle Z F))
    {beta : G ⧸ M} (hbeta : InOrbit F (QuotientGroup.mk 1) beta)
    (hnebase : beta ≠ QuotientGroup.mk 1) :
    (F : Set G) = (localCircleIn Z F : Set G) *
      (F ⊓ M ⊓ MulAction.stabilizer G beta : Subgroup G) := by
  simpa only [baseCoset_stabilizer] using
    set_eq_mul_twoPointStabilizer_of_twoTransitiveOn F (localCircleIn Z F)
      (QuotientGroup.mk 1) beta (localCircleIn_le Z F)
      (localCircle_twoTransitiveOn h r F hF hFM hne hns) hbeta hnebase

end BenderSuzuki.ZD

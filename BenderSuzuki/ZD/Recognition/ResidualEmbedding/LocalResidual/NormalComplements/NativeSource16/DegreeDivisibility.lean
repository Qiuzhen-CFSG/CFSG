module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.DegreeDivisibility.Geometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.DegreeDivisibility.Orbit
public import BenderSuzuki.Converse.Lift

/-!
# The source degree divisor of Lemma 16.4(c)

For the selected Sylow T₁ of C_G(u), put Q=T₁° and P=T₁∩C_G(u)°.
Assume the source hypotheses that u is two-central in D and u is conjugate
to uz, where z is the selected distinguished central involution of T₁.
Burnside fusion and concrete root transitivity give an orbit Qu of size |Q|
under N_G(Q⟨u⟩)≤M. The marked Borel normalizes P and Q, and P∩D=1.
A Sylow two-subgroup of D centralizing u consequently contributes its full
order together with P to the centralizer in this normalizer. Canceling its
odd index in D gives |Q||P| dividing |G:M|−1.

The formula uses the literal Q and P rather than an uninstantiated field
parameter. The earlier circle models give |Q|=q, making this exactly GLS IV,
Chapter 2, Lemma 16.4(c), refs/KGroup/GLS4/Chapter2.tex, final paragraph.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory RankOneModelGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem residual_pair_index_eq_degree_sub_one
    (ha : ResidualAction Z M) {t : G} (htM : t ∉ M) :
    (residualPairStabilizer M t).relIndex M = Nat.card (G ⧸ M) - 1 := by
  let a : G ⧸ M := QuotientGroup.mk 1
  have hM : MulAction.stabilizer G a = M := MulAction.stabilizer_quotient M
  have hne : t⁻¹ • a ≠ a := by
    intro he
    apply htM
    rw [← hM]
    exact (inv_smul_eq_iff.mp he).symm
  have hc := Converse.card_stabilizer_eq_twoPoint_mul ha.two_transitive hne
  rw [← PFchapter1section1.rightConjugate_stabilizer, hM] at hc
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) (residualPairStabilizer M t) M
    bot_le inf_le_left
  simp only [relIndex_bot_left] at hi
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hi.trans hc)

/-- Lemma 16.4(c), with the actual circle, original Sylow intersection, and
source meaning of two-centrality. All normalizer, model, orbit, and order
premises are proved inside the theorem. -/
public theorem source16_degree_divisibility
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {t u z : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (htu : Commute t u) (hz : z ∈ Z)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hSM : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ M)
    (huS : u ∈ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hzS : z ∈ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hSz : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ centralizer ({z} : Set G))
    (hcentral : ∃ SD : Sylow 2 (residualPairStabilizer M t),
      (SD : Subgroup (residualPairStabilizer M t)).map
        (residualPairStabilizer M t).subtype ≤ centralizer ({u} : Set G))
    (hconj : IsConj u (u * z)) :
    let B := centralizer ({u} : Set G)
    let T := (S : Subgroup B).map B.subtype
    Nat.card (localCircleIn Z T) * Nat.card (T ⊓ localCircleIn Z B : Subgroup G) ∣
      Nat.card (G ⧸ M) - 1 := by
  let B := centralizer ({u} : Set G)
  let C := localCircle Z B
  let f := localCircleHom Z B
  let T := (S : Subgroup B).map B.subtype
  let Q := localCircleIn Z T
  let D := residualPairStabilizer M t
  let N := normalizer ((Q ⊔ zpowers u : Subgroup G) : Set G)
  have hTB : T ≤ B := map_subtype_le _
  have hB : B ≠ ⊤ := r.involution_centralizer_ne_top h.disconnected hu
  have hBM : ¬ B ≤ M := fun hle => htM (hle (mem_centralizer_singleton_iff.mpr htu.eq))
  have hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M := ⟨z,hz,hTB hzS,hSM hzS⟩
  have hns := source16_centralizer_nonsolvable h r ha ht htM hu huD
  obtain ⟨P,hP,_⟩ := source16_sylow_circle_intersection h.disconnected B hBM hne S
  let H := (P : Subgroup C).map f
  have hHM : H ≤ M := hP.le.trans (inf_le_left.trans hSM)
  have hHB : H ≤ B := by
    rintro _ ⟨x,_,rfl⟩
    exact (x : B).property
  have hmark := source16_circle_sylow_borel h r ha B hB hBM hne hns P hHM
  have hPD : Disjoint H D := source16_circle_sylow_disjoint_pair h.disconnected r B hB hBM hne htM P
  have hQeq : (omegaOneAmbient (P : Subgroup C)).map f = Q :=
    source16_sylow_omega_map_eq_localCircle h.disconnected r B hB hBM hne T hTB P hP
  have hQH : Q ≤ H := hQeq.symm ▸ map_mono (omegaOneAmbient_le _)
  have huQ : u ∉ Q := fun hh => hu.ne_one (disjoint_def.mp hPD (hQH hh) huD)
  have hzQ : z ∈ Q := by
    change z ∈ localCircleIn Z T
    rw [localCircleIn_eq_closure]
    exact subset_closure ⟨hz,hzS⟩
  have huQcent : u ∈ centralizer (Q : Set G) := by
    intro q hq
    exact mem_centralizer_singleton_iff.mp (hTB (localCircleIn_le Z T hq))
  obtain ⟨hc,hperfect,hmodels,_⟩ := localCircle_nonsolvable_structure h r ha B hB hBM hne hns
  have hodd : Odd (Nat.card (center C)) := by
    rw [← hc]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  obtain ⟨n,hn,hmodel⟩ := hmodels.exists_exponent
  have htrans : ∀ x ∈ Q, x ≠ 1 →
      ∃ a ∈ normalizer (Q : Set G) ⊓ centralizer ({u} : Set G), MulAut.conj a z = x := by
    rw [← hQeq] at hzQ ⊢
    exact source16_circle_root_transitivity P hn hperfect hodd hmodel z hzQ
      (h.disconnected.involutions z hz).ne_one
  obtain ⟨g,hg,_,he⟩ := source16_exists_root_join_normalizer_mover h.disconnected
    S hSM huS hz hzS hSz hconj
  have horbit := (Source16DegreeDivisibility.source_normalizer_orbit_card h.disconnected
    T huS huQ hu.sq_eq_one huQcent hzQ (h.disconnected.involutions z hz).ne_one
    ⟨g,hg,he⟩ htrans).2
  have hBN : B ⊓ M ≤ N := by
    change B ⊓ M ≤ normalizer ((Q ⊔ zpowers u : Subgroup G) : Set G)
    rw [← hQeq]
    exact source16_borel_normalizes_root_join h.disconnected P hmark
  have hBC : B ⊓ M ≤ N ⊓ centralizer ({u} : Set G) := le_inf hBN inf_le_left
  have hNM : N ≤ M := normalizer_le h.disconnected
    (sup_le ((localCircleIn_le Z T).trans hSM) (zpowers_le.mpr huD.1))
    ⟨z,hz,(show Q ≤ Q ⊔ zpowers u from le_sup_left) hzQ⟩
  obtain ⟨SD,hSD⟩ := hcentral
  have hSBM : (SD : Subgroup D).map D.subtype ≤ B ⊓ M :=
    le_inf hSD ((map_subtype_le _).trans inf_le_left)
  have hdiv := source16_root_product_dvd_pair_index M D N H Q u inf_le_left hNM SD
    (P.isPGroup'.map f) ((P.isPGroup'.map f).to_le hQH)
    ((le_inf hHB hHM).trans hBC) (hSBM.trans hBC)
    (hSBM.trans (source16_circle_marked_sylow_normalized h.disconnected B P hmark))
    hPD horbit
  rw [residual_pair_index_eq_degree_sub_one ha htM] at hdiv
  change Nat.card Q * Nat.card (T ⊓ localCircleIn Z B : Subgroup G) ∣ _
  have hHeq : H = T ⊓ localCircleIn Z B := hP
  rw [hHeq] at hdiv
  exact hdiv

end BenderSuzuki.ZD

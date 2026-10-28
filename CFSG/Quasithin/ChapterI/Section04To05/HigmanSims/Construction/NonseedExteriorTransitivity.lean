module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedExtensionTransfer
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreCentralFour
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreCommutator
public import Theory.GroupTheory.PCoreFrattiniDisplacement
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Exterior transitivity for every original nonseed-eight extension

Every elementary sixteen through an original nonseed eight is normalized
by its original point core and is self-centralizing. An actual central
cyclic-four generator consequently fails to commute with every exterior
involution. The line-displacement and Frattini-kernel argument identifies
its point-core stabilizer with the specified eight, so its orbit exhausts
the eight exterior points. No involution-class premise is required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G]

private def lineDisplacement (Q U : Subgroup G) (b : G)
    (hQU : Q ≤ centralizer (U : Set G)) : Subgroup G where
  carrier := {q | q ∈ Q ∧ ⁅q, b⁆ ∈ U}
  one_mem' := ⟨Q.one_mem, by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hxb⟩ ⟨hy, hyb⟩
    refine ⟨Q.mul_mem hx hy, ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul,
      ← hQU hx _ hyb, mul_inv_cancel_right]
    exact U.mul_mem hyb hxb
  inv_mem' := by
    rintro x ⟨hx, hxb⟩
    refine ⟨Q.inv_mem hx, ?_⟩
    rw [commutatorElement_inv_left, ← commutatorElement_inv]
    have hc := hQU (Q.inv_mem hx) _ (U.inv_mem hxb)
    rw [← hc, inv_mul_cancel_right]
    exact U.inv_mem hxb

private theorem line_cases (u x : G) (hu : orderOf u = 2)
    (hx : x ∈ zpowers u) : x = 1 ∨ x = u := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hu] at hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

private theorem line_le_frattini {z : G} {V : Subgroup G} (_h : TypeAt z V)
    (c : G) (hc : c ∈ (involutionCentralizer z).pCoreIn 2) (hc2 : c ^ 2 = z) :
    zpowers z ≤ (frattini ((involutionCentralizer z).pCoreIn 2)).map
      ((involutionCentralizer z).pCoreIn 2).subtype := by
  let Q := (involutionCentralizer z).pCoreIn 2
  let : Fact (IsPGroup 2 Q) := ⟨isPGroup_pCoreIn 2 _⟩
  apply zpowers_le.mpr
  exact ⟨(⟨c, hc⟩ : Q) ^ 2,
    pth_power_mem_frattini_of_isPGroup (p := 2) (⟨c, hc⟩ : Q), hc2⟩

private theorem center_line_of_square_one {z : G} {V : Subgroup G} (h : TypeAt z V)
    (x : G) (hx : x ∈ (involutionCentralizer z).pCoreIn 2)
    (hxZ : ∀ q ∈ (involutionCentralizer z).pCoreIn 2, Commute q x)
    (hx2 : x ^ 2 = 1) : x ∈ zpowers z := by
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  have hs : CoreShape Q := (h.centralizer_core.of_equiv
    (MulEquiv.subgroupCongr h.centralizer_fitting)).of_equiv
      ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective)
  obtain ⟨e⟩ := hs.center_model
  let : IsCyclic (center Q) := e.isCyclic.mpr inferInstance
  have hzQ : z ∈ Q := by
    have hVQ : V ≤ Q := by
      change V ≤ (pCore 2 H).map H.subtype
      rw [← h.centralizer_fitting]
      exact h.seed_le_core
    exact hVQ h.involution_mem_seed
  have hzZ : (⟨z, hzQ⟩ : Q) ∈ center Q := mem_center_iff.mpr fun q =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (pCoreIn_le 2 H q.property))
  have hxZ' : (⟨x, hx⟩ : Q) ∈ center Q := mem_center_iff.mpr fun q =>
    Subtype.ext (hxZ q q.property).eq
  by_cases hx1 : x = 1
  · exact hx1 ▸ (zpowers z).one_mem
  have he : (⟨⟨x, hx⟩, hxZ'⟩ : center Q) = ⟨⟨z, hzQ⟩, hzZ⟩ := by
    apply IsCyclic.eq_of_orderOf_eq_two
    · rw [← orderOf_coe, ← orderOf_coe]
      exact orderOf_eq_prime hx2 hx1
    · rw [← orderOf_coe, ← orderOf_coe]
      exact h.involution
  have hxz : x = z := congrArg (fun q : center Q => (q.val : G)) he
  exact hxz ▸ mem_zpowers z

private theorem displacement_ne_core {z : G} {V : Subgroup G} (h : TypeAt z V)
    (c : G) (hc : c ∈ (involutionCentralizer z).pCoreIn 2) (hc2 : c ^ 2 = z)
    (b : G) (hbH : b ∈ involutionCentralizer z)
    (hbQ : b ∉ (involutionCentralizer z).pCoreIn 2)
    (hQU : (involutionCentralizer z).pCoreIn 2 ≤ centralizer (zpowers z : Set G)) :
    lineDisplacement ((involutionCentralizer z).pCoreIn 2) (zpowers z) b hQU ≠
      (involutionCentralizer z).pCoreIn 2 := by
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  intro he
  have hF : (frattini Q).map Q.subtype =
      ((frattini (pCore 2 H)).map (pCore 2 H).subtype).map H.subtype :=
    frattini_image_map (pCore 2 H) H.subtype H.subtype_injective
  have hbcore : (⟨b, hbH⟩ : H) ∈ pCore 2 H := by
    apply mem_pCore_of_frattini_displacement h.centralizer_twoCore_selfCentralizing
    intro x
    apply (mem_map_iff_mem H.subtype_injective).mp
    rw [← hF]
    apply line_le_frattini h c hc hc2
    have hx : ((x : H) : G) ∈ Q := ⟨x.val, x.property, rfl⟩
    have ht : ((x : H) : G) ∈ lineDisplacement Q (zpowers z) b hQU := he ▸ hx
    change ⁅b, ((x : H) : G)⁆ ∈ zpowers z
    rw [← commutatorElement_inv]
    exact (zpowers z).inv_mem ht.2
  exact hbQ ⟨⟨b, hbH⟩, hbcore, rfl⟩

omit [Finite G] in
private theorem displacement_commutes_actor (q b : G)
    (hqb : Commute (q ^ 2) b) (hd : ⁅q, b⁆ ^ 2 = 1) : Commute q ⁅q, b⁆ := by
  let d := ⁅q, b⁆
  have he : (q * d * q⁻¹) * d = 1 := by
    calc
      _ = q ^ 2 * b * (q ^ 2)⁻¹ * b⁻¹ := by dsimp [d]; simp only [commutatorElement_def, pow_two]; group
      _ = 1 := by rw [hqb.eq, mul_inv_cancel_right, mul_inv_cancel]
  have hi : d⁻¹ = d := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hd)
  have hf : q * d * q⁻¹ = d := (eq_inv_of_mul_eq_one_left he).trans hi
  exact mul_inv_eq_iff_eq_mul.mp hf

omit [Finite G] in
private theorem displacement_commutes_fixer (q r b : G)
    (hrb : Commute r b) (hkb : Commute ⁅r, q⁆ b)
    (hkd : Commute ⁅r, q⁆ ⁅q, b⁆) : Commute r ⁅q, b⁆ := by
  apply mul_inv_eq_iff_eq_mul.mp
  rw [conjugate_commutatorElement, hrb.eq, mul_inv_cancel_right]
  have hrq : r * q * r⁻¹ = ⁅r, q⁆ * q := by simp [commutatorElement_def, mul_assoc]
  rw [hrq, commutatorElement_mul_left_eq_conj_mul, hkb.commutator_eq,
    mul_one, hkd.eq, mul_inv_cancel_right]

omit [Finite G] in
private theorem relative_card (A B : Subgroup G) (hAB : A ≤ B) :
    Nat.card A * A.relIndex B = Nat.card B := by
  have hh := (A.subgroupOf B).card_mul_index
  change Nat.card (A.subgroupOf B) * A.relIndex B = Nat.card B at hh
  rwa [Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv] at hh

omit [Finite G] in
private theorem relative_index_two_generate (T Q : Subgroup G) (hTQ : T ≤ Q)
    (hi : T.relIndex Q = 2) (q : G) (hq : q ∈ Q) (hqt : q ∉ T) :
    T ⊔ zpowers q = Q := by
  apply le_antisymm (sup_le hTQ (zpowers_le.mpr hq))
  intro x hx
  by_cases hxt : x ∈ T
  · exact (show T ≤ T ⊔ zpowers q from le_sup_left) hxt
  have ht : x * q⁻¹ ∈ T := by
    have hh := (T.subgroupOf Q).mul_mem_iff_of_index_two hi
      (a := (⟨x, hx⟩ : Q)) (b := (⟨q, hq⟩ : Q)⁻¹)
    exact hh.mpr (iff_of_false hxt (fun hh => hqt (by change q⁻¹ ∈ T at hh; exact T.inv_mem_iff.mp hh)))
  have hh := (T ⊔ zpowers q).mul_mem ((show T ≤ T ⊔ zpowers q from le_sup_left) ht)
    ((show zpowers q ≤ T ⊔ zpowers q from le_sup_right) (mem_zpowers q))
  simpa using hh

private theorem exterior_stabilizer {z : G} {V : Subgroup G} (h : TypeAt z V)
    (E : pointCoreEights z) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hEA : E.val ≤ A) (hAQ : A ⊓ (involutionCentralizer z).pCoreIn 2 = E.val)
    (hQN : (involutionCentralizer z).pCoreIn 2 ≤ normalizer (A : Set G))
    (c b : G) (hc4 : orderOf c = 4) (hc2 : c ^ 2 = z)
    (hcZ : c ∈ (center ((involutionCentralizer z).pCoreIn 2)).map
      ((involutionCentralizer z).pCoreIn 2).subtype)
    (hbA : b ∈ A) (hnc : ¬ Commute b c) (hbc : b * c * b⁻¹ = c⁻¹) :
    (involutionCentralizer z).pCoreIn 2 ⊓ involutionCentralizer b = E.val := by
  classical
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  let U := zpowers z
  let C := Q ⊓ involutionCentralizer b
  obtain ⟨cQ, hcQ, hec⟩ := hcZ
  have hc : c ∈ Q := hec ▸ cQ.property
  have hccomm (q : G) (hq : q ∈ Q) : Commute q c := by
    rw [← hec]
    exact congrArg Subtype.val (mem_center_iff.mp hcQ (⟨q, hq⟩ : Q))
  have hQU : Q ≤ centralizer (U : Set G) := by
    intro q hq x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    have hz : Commute q z := mem_centralizer_singleton_iff.mp (pCoreIn_le 2 H hq)
    exact (hz.zpow_right n).eq.symm
  let T := lineDisplacement Q U b hQU
  have hTQ : T ≤ Q := fun _ hx => hx.1
  have hbH : b ∈ H := mem_centralizer_singleton_iff.mpr
    (setLike_mul_comm hbA (hEA E.property.2.1))
  have hbQ : b ∉ Q := fun hh => hnc (hccomm b hh)
  have hTne : T ≠ Q := displacement_ne_core h c hc hc2 b hbH hbQ hQU
  have hbU : b ∈ centralizer (U : Set G) :=
    centralizer_le (zpowers_le.mpr E.property.2.1)
      (fun e he => setLike_mul_comm (hEA he) hbA)
  have hcb : ⁅c, b⁆ = z := by
    have he : b * c⁻¹ * b⁻¹ = c := by
      have hh := congrArg Inv.inv hbc
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using hh
    calc
      ⁅c, b⁆ = c * (b * c⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
      _ = c * c := by rw [he]
      _ = z := by simpa only [pow_two] using hc2
  have hCT : C ≤ T := by
    rintro q ⟨hq, hqb⟩
    exact ⟨hq, by rw [(show Commute q b from mem_centralizer_singleton_iff.mp hqb).commutator_eq]; exact U.one_mem⟩
  have hcT : c ∈ T := ⟨hc, hcb ▸ mem_zpowers z⟩
  have hEC : E.val ≤ C := fun e he => ⟨E.property.1 he,
    mem_centralizer_singleton_iff.mpr (setLike_mul_comm (hEA he) hbA)⟩
  have hCZ : C ⊓ zpowers c = zpowers z := by
    have hlo : zpowers z ≤ C ⊓ zpowers c := by
      apply zpowers_le.mpr
      change z ∈ C ∧ z ∈ zpowers c
      exact ⟨hEC E.property.2.1, hc2 ▸ (zpowers c).pow_mem (mem_zpowers c) 2⟩
    apply le_antisymm ?_ hlo
    intro x hx
    have hxC : x ∈ C := hx.1
    have hxc : x ∈ zpowers c := hx.2
    rw [mem_zpowers_iff_mem_range_orderOf, hc4] at hxc
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hxc
    have hn4 : n < 4 := Finset.mem_range.mp hn
    have hxc : Commute (c ^ n) b := mem_centralizer_singleton_iff.mp hxC.2
    interval_cases n
    · simp
    · exact (hnc (by simpa using hxc.symm)).elim
    · rw [hc2]; exact mem_zpowers z
    · have hi : c ^ 3 = c⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ]
        change c ^ 4 = 1
        rw [← hc4, pow_orderOf_eq_one]
      rw [hi] at hxc
      exact (hnc (by simpa using hxc.inv_left.symm)).elim
  have hTjoin : T = C ⊔ zpowers c := by
    apply le_antisymm ?_ (sup_le hCT (zpowers_le.mpr hcT))
    intro q hq
    rcases line_cases z ⁅q, b⁆ h.involution hq.2 with hz | hz
    · exact (show C ≤ C ⊔ zpowers c from le_sup_left)
        ⟨hq.1, mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_commute.mp hz).eq⟩
    · have hdiff : q * c⁻¹ ∈ C := by
        refine ⟨Q.mul_mem hq.1 (Q.inv_mem hc), mem_centralizer_singleton_iff.mpr ?_⟩
        apply commutatorElement_eq_one_iff_commute.mp
        have hcbi : ⁅c⁻¹, b⁆ = z⁻¹ := by
          rw [commutatorElement_inv_left, ← commutatorElement_inv, hcb]
          rw [← hQU (Q.inv_mem hc) _ (U.inv_mem (mem_zpowers z)), inv_mul_cancel_right]
        rw [commutatorElement_mul_left_eq_conj_mul, hcbi,
          ← hQU hq.1 _ (U.inv_mem (mem_zpowers z)), mul_inv_cancel_right, hz, inv_mul_cancel]
      have hh := (C ⊔ zpowers c).mul_mem
        ((show C ≤ C ⊔ zpowers c from le_sup_left) hdiff)
        ((show zpowers c ≤ C ⊔ zpowers c from le_sup_right) (mem_zpowers c))
      simpa using hh
  have hTcard : Nat.card T = 2 * Nat.card C := by
    have hn : zpowers c ≤ normalizer (C : Set G) := by
      apply zpowers_le.mpr
      apply centralizer_le_normalizer
      intro x hx
      exact (hccomm x hx.1).eq
    have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes C (zpowers c) hn
    rw [hCZ, Nat.card_zpowers, Nat.card_zpowers, hc4, h.involution, ← hTjoin] at hp
    omega
  apply (eq_of_le_of_card_ge hEC ?_).symm
  by_contra hsmall
  have hCbig : 16 ≤ Nat.card C := by
    have hp := relative_card E.val C hEC
    rw [E.property.2.2.2] at hp
    have hi : E.val.relIndex C ≠ 1 := by intro hi; rw [hi, mul_one] at hp; omega
    have hip : E.val.relIndex C ≠ 0 := index_ne_zero_of_finite
    omega
  have hQ64 : Nat.card Q = 64 := by
    change Nat.card ((pCore 2 H).map H.subtype) = 64
    rw [card_map_of_injective H.subtype_injective, ← h.centralizer_fitting]
    exact h.centralizer_core_card
  have hTi : T.relIndex Q = 2 := by
    have hp := relative_card T Q hTQ
    rw [hTcard, hQ64] at hp
    have hi : T.relIndex Q ≠ 1 := fun he => hTne (le_antisymm hTQ (relIndex_eq_one.mp he))
    have hip : T.relIndex Q ≠ 0 := index_ne_zero_of_finite
    have hilo : 2 ≤ T.relIndex Q := by omega
    have hh := Nat.mul_le_mul_right (T.relIndex Q) (show 32 ≤ 2 * Nat.card C by omega)
    rw [hp] at hh
    omega
  obtain ⟨q, hqQ, hqT⟩ := SetLike.not_le_iff_exists.mp (show ¬ Q ≤ T from fun he => hTne (le_antisymm hTQ he))
  let d := ⁅q, b⁆
  have hdE : d ∈ E.val := by
    rw [← hAQ]
    change d ∈ A ∧ d ∈ Q
    constructor
    · exact A.mul_mem (le_normalizer_iff.mp hQN q hqQ b hbA) (A.inv_mem hbA)
    · have hnorm : H ≤ normalizer (Q : Set G) := by
        apply le_normalizer_iff.mpr
        intro g hg x hx
        obtain ⟨xH, hxH, rfl⟩ := hx
        exact ⟨⟨g, hg⟩ * xH * (⟨g, hg⟩ : H)⁻¹,
          (inferInstance : (pCore 2 H).Normal).conj_mem xH hxH ⟨g, hg⟩, rfl⟩
      have hh := le_normalizer_iff.mp hnorm b hbH q⁻¹ (Q.inv_mem hqQ)
      simpa only [d, commutatorElement_def, mul_assoc] using Q.mul_mem hqQ hh
  have hd2 : d ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian d (hEA hdE)
  have hdq : Commute q d := displacement_commutes_actor q b
    (mem_centralizer_iff.mp hbU _ (h.centralizer_core_square_mem q hqQ))
    hd2
  have hdC : C ≤ centralizer ({d} : Set G) := by
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    apply displacement_commutes_fixer q r b (mem_centralizer_singleton_iff.mp hr.2)
    · exact mem_centralizer_iff.mp hbU _ (h.point_core_commutator_mem r q hr.1 hqQ)
    · exact mem_centralizer_iff.mp (hQU (E.property.1 hdE)) _
        (h.point_core_commutator_mem r q hr.1 hqQ)
  have hdc : Commute c d := (hccomm d (E.property.1 hdE)).symm
  have hdQ : Q ≤ centralizer ({d} : Set G) := by
    rw [← relative_index_two_generate T Q hTQ hTi q hqQ hqT, hTjoin]
    exact sup_le (sup_le hdC (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hdc.eq)))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hdq.eq))
  have hdU := center_line_of_square_one h d (E.property.1 hdE)
    (fun r hr => mem_centralizer_singleton_iff.mp (hdQ hr)) hd2
  exact hqT ⟨hqQ, hdU⟩

private theorem exterior_orbit {z : G} {V : Subgroup G} (h : TypeAt z V)
    (E : pointCoreEights z) (A : Subgroup G) (hEA : E.val ≤ A) (hA16 : Nat.card A = 16)
    (hQN : (involutionCentralizer z).pCoreIn 2 ≤ normalizer (A : Set G))
    (b : G) (hbA : b ∈ A) (hbQ : b ∉ (involutionCentralizer z).pCoreIn 2)
    (hstab : (involutionCentralizer z).pCoreIn 2 ⊓ involutionCentralizer b = E.val) :
    ∀ x ∈ A, x ∉ E.val → ∃ q ∈ (involutionCentralizer z).pCoreIn 2, q * b * q⁻¹ = x := by
  let H := involutionCentralizer z
  let Q := H.pCoreIn 2
  let : MulAction Q G := MulAction.compHom G (MulAut.conj.comp Q.subtype)
  let O := MulAction.orbit Q b
  have hst : MulAction.stabilizer Q b = (involutionCentralizer b).subgroupOf Q := by
    ext q
    change (q : G) * b * (q : G)⁻¹ = b ↔ (q : G) ∈ involutionCentralizer b
    rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hsc : Nat.card (MulAction.stabilizer Q b) = 8 := by
    rw [hst, ← card_subtype Q, subgroupOf_map_subtype, inf_comm, hstab]
    exact E.property.2.2.2
  have hQc : Nat.card Q = 64 := by
    change Nat.card ((pCore 2 H).map H.subtype) = 64
    rw [card_map_of_injective H.subtype_injective, ← h.centralizer_fitting]
    exact h.centralizer_core_card
  have hOc : O.ncard = 8 := by
    have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Q b)
    rw [Nat.card_prod, hsc, hQc] at hh
    change O.ncard * 8 = 64 at hh
    omega
  have hsub : O ⊆ (A : Set G) \ (E.val : Set G) := by
    rintro x ⟨q, rfl⟩
    change (q : G) * b * (q : G)⁻¹ ∈ A ∧ (q : G) * b * (q : G)⁻¹ ∉ E.val
    refine ⟨le_normalizer_iff.mp hQN q q.property b hbA, ?_⟩
    intro he
    have hh := Q.mul_mem (Q.mul_mem (Q.inv_mem q.property) (E.property.1 he)) q.property
    exact hbQ (by simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh)
  have hdiff : ((A : Set G) \ (E.val : Set G)).ncard = 8 := by
    have hh := Set.ncard_sdiff_add_ncard_of_subset hEA
    change ((A : Set G) \ (E.val : Set G)).ncard + Nat.card E.val = Nat.card A at hh
    rw [hA16, E.property.2.2.2] at hh
    omega
  have he : O = (A : Set G) \ (E.val : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hdiff, hOc])
  intro x hx hxE
  have hxO : x ∈ O := he ▸ (show x ∈ (A : Set G) \ (E.val : Set G) from ⟨hx, hxE⟩)
  obtain ⟨q, hq⟩ := hxO
  exact ⟨q, q.property, hq⟩

/-- The original point core is transitive on the exterior of any literal
nonseed eight in any elementary-sixteen extension of that eight. -/
theorem TypeAt.nonseed_extension_exterior_transitive {z : G} {V : Subgroup G}
    (h : TypeAt z V) (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA16 : Nat.card A = 16)
    (hEA : E.val ≤ A) (b : G) (hbA : b ∈ A) (hbE : b ∉ E.val) :
    ∀ x ∈ A, x ∉ E.val →
      ∃ q ∈ (involutionCentralizer z).pCoreIn 2, q * b * q⁻¹ = x := by
  obtain ⟨hQN, hCA, hAQ⟩ := h.nonseed_eight_extension_structure E hEn A hEA inferInstance hA16
  obtain ⟨c, hc4, hc2, hcZ, _⟩ := h.exists_point_core_central_four
  have hcE (e : G) (he : e ∈ E.val) : Commute e c := by
    obtain ⟨cQ, hcQ, hec⟩ := hcZ
    rw [← hec]
    exact congrArg Subtype.val (mem_center_iff.mp hcQ ⟨e, E.property.1 he⟩)
  have hgen : E.val ⊔ zpowers b = A := by
    have hi : E.val.relIndex A = 2 := by
      have hh := relative_card E.val A hEA
      rw [E.property.2.2.2, hA16] at hh
      omega
    exact relative_index_two_generate E.val A hEA hi b hbA hbE
  have hnc : ¬ Commute b c := by
    intro hbc
    have hAC : A ≤ centralizer ({c} : Set G) := by
      rw [← hgen]
      exact sup_le (fun e he => mem_centralizer_singleton_iff.mpr (hcE e he).eq)
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hbc.eq))
    have hcA : c ∈ A := by
      rw [← hCA]
      intro a ha
      exact mem_centralizer_singleton_iff.mp (hAC ha)
    have hd := orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian (p := 2) c hcA)
    rw [hc4] at hd
    norm_num at hd
  have hbH : b ∈ involutionCentralizer z := mem_centralizer_singleton_iff.mpr
    (setLike_mul_comm hbA (hEA E.property.2.1))
  have hbc := h.point_core_central_four_inverted c hc4 hcZ b hbH hnc
  have hbQ : b ∉ (involutionCentralizer z).pCoreIn 2 := by
    intro hb
    exact hbE (hAQ ▸ (show b ∈ A ⊓ (involutionCentralizer z).pCoreIn 2 from ⟨hbA, hb⟩))
  have hstab := exterior_stabilizer h E A hEA hAQ hQN c b hc4 hc2 hcZ hbA hnc hbc
  exact exterior_orbit h E A hEA hA16 hQN b hbA hbQ hstab

end CFSG.Quasithin.HigmanSims

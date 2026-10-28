module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSActionNormalizer
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingSetup
public import Theory.GroupTheory.IrreducibleSectionCore.Ambient
public import Theory.GroupTheory.ElementaryCentralDisplacements

/-!
# Elementary factorization of the original larger two-core

Choose the actual Sylow-invariant elementary lift A with U<A<Q. Minimality
of U and A/U makes O₂(KS) act trivially on both sections. The nonbinary
MS action-normalizer identity therefore identifies its action on A with
Q's action, giving O₂(KS)=Q C_{O₂(KS)}(A), with intersection A.

The centralizer factor C is elementary: its K-displacements lie in A,
which it centralizes, so its squares centralize K. The original C_S(K)=1
kills every square. This constructs A and C with the literal original
subgroup maps and gives |A|=2^(6n).

The remaining source rank argument must prove C=A to obtain Q=O₂(KS).
That step, original MS/secondary construction and terminal exclusions
remain with qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher–Smith C.1.35, printed pp.138–139; original 4.3.11, p.617.
-/


@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

omit [Finite G] in
private theorem core_le_K : Q c ≤ K c :=
  (Subgroup.commutator_le_sup _ _).trans (sup_le (pCoreIn_le 2 _) le_rfl)

omit [Finite G] in
private theorem center_minimal (d : MSData c n) (B : Subgroup G)
    (hB : B ≤ U c) (hn : K c ≤ normalizer (B : Set G)) : B = ⊥ ∨ B = U c := by
  by_cases hz : B = ⊥
  · exact Or.inl hz
  right
  have hm := d.natural
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,hKU,_,hbot,e,he⟩ := hm
  let := hbot
  let u := QuotientGroup.quotientBot.symm.trans e
  obtain ⟨a,ha1⟩ := ne_bot_iff_exists_ne_one.mp hz
  have ha := a.property
  let x : U c := ⟨a,hB ha⟩
  have hx : (u x).toAdd ≠ 0 := by
    intro hh
    have hh' : u x = 1 := Multiplicative.toAdd.injective hh
    exact ha1 (Subtype.ext (congrArg (fun z : U c => (z : G)) (u.map_eq_one_iff.mp hh')))
  apply le_antisymm hB
  intro b hb
  by_cases hb1 : b = 1
  · exact hb1 ▸ B.one_mem
  let y : U c := ⟨b,hb⟩
  have hy : (u y).toAdd ≠ 0 := by
    intro hh
    have hh' : u y = 1 := Multiplicative.toAdd.injective hh
    exact hb1 (congrArg Subtype.val (u.map_eq_one_iff.mp hh'))
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three (u x).toAdd (u y).toAdd hx hy
  obtain ⟨k,hk⟩ := d.model.surjective.comp (QuotientGroup.mk'_surjective _) g
  let z : U c := ⟨(k : G)*a*(k : G)⁻¹,(mem_normalizer_iff.mp (hKU k.property) a).mp x.property⟩
  have hz : z = y := by
    apply u.injective
    apply Multiplicative.toAdd.injective
    have hh := he k x z rfl
    change (u z).toAdd = Representation.specialLinearNatural 3 (linearThreeActor d.model k) (u x).toAdd at hh
    exact hh.trans (by rw [show linearThreeActor d.model k = g from hk]; exact hg)
  have hh : (z : G) ∈ B := (mem_normalizer_iff.mp (hn k.property) a).mp ha
  rwa [hz] at hh

omit [Finite G] in
private theorem join_normalizes_center :
    K c ⊔ S c ≤ normalizer (U c : Set G) :=
  ((sup_le (map_subtype_le _) inf_le_right).trans (core_normalized c)).trans
    (normalizer_le_normalizer_characteristic_image (Q c) (center (Q c)))

/-- The larger two-core fixes the original natural center pointwise. -/
theorem MSData.joinCore_centralizes_center (d : MSData c n) :
    (K c ⊔ S c).pCoreIn 2 ≤ Subgroup.centralizer (U c : Set G) := by
  have hQU : U c ≤ Q c := map_subtype_le _
  apply pCoreIn_le_centralizer_of_irreducible (U c) (K c) (K c ⊔ S c)
    ((isPGroup_pCoreIn 2 (K c)).to_le (hQU.trans ?_))
    (hQU.trans (core_le_K.trans le_sup_left)) join_normalizes_center le_sup_left
    (center_minimal d)
  exact le_normalizer_iff_commutator_le_left.mp ((K c).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c))))

/-- On a Sylow-invariant lift the larger core fixes both sections U and A/U. -/
theorem MSData.joinCore_liftAction_mem_sectionKernel (d : MSData c n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G))
    (x : G) (hx : x ∈ (K c ⊔ S c).pCoreIn 2) :
    A.val.normalizerMonoidHom ⟨x,hA (pCoreIn_le 2 _ hx)⟩ ∈
      sectionKernel ((U c).subgroupOf A.val) := by
  have hdisp : ⁅A.val,(K c ⊔ S c).pCoreIn 2⁆ ≤ U c :=
    ambient_irreducible_section_core (U c) A.val (K c ⊔ S c) A.property.1.le
      (A.property.2.1.le.trans (core_le_K.trans le_sup_left)) join_normalizes_center hA
      (T.isPGroup'.to_le (A.property.2.1.le.trans ((core_le_sylow c).trans inf_le_left)))
      (fun B hUB hBA hn => d.invariantCoreLifts_minimal A B hUB hBA (le_sup_left.trans hn))
  constructor
  · intro a
    change x*(a : G)*x⁻¹*(a : G)⁻¹ ∈ U c
    apply hdisp
    rw [commutator_comm]
    exact commutator_mem_commutator hx a.property
  · intro a ha
    apply Subtype.ext
    change x*(a : G)*x⁻¹ = a
    have hh := mem_centralizer_iff.mp (d.joinCore_centralizes_center hx) a ha
    rw [←hh,mul_inv_cancel_right]

omit [Finite G] in
/-- Normalizing the original K induces normalization of its literal action image. -/
private theorem liftAction_normalizes (A : invariantCoreLifts c)
    (x : normalizer (A.val : Set G)) (hx : (x : G) ∈ normalizer (K c : Set G)) :
    A.val.normalizerMonoidHom x ∈
      normalizer ((invariantLiftAction A).range : Set (MulAut A.val)) := by
  apply mem_normalizer_iff.mpr
  intro a
  constructor
  · rintro ⟨k,rfl⟩
    let k' : K c := ⟨(x : G)*k*(x : G)⁻¹,(mem_normalizer_iff.mp hx k).mp k.property⟩
    refine ⟨k',?_⟩
    have he : inclusion A.property.2.2 k' = x * inclusion A.property.2.2 k * x⁻¹ :=
      Subtype.ext rfl
    change A.val.normalizerMonoidHom (inclusion A.property.2.2 k') = _
    rw [he,map_mul,map_mul,map_inv]
    rfl
  · rintro ⟨k,hk⟩
    let k' : K c := ⟨(x : G)⁻¹*k*x,by simpa only [inv_inv] using (mem_normalizer_iff.mp ((normalizer (K c : Set G)).inv_mem hx) k).mp k.property⟩
    refine ⟨k',?_⟩
    have he : inclusion A.property.2.2 k' = x⁻¹ * inclusion A.property.2.2 k * x :=
      Subtype.ext rfl
    change A.val.normalizerMonoidHom (inclusion A.property.2.2 k') = a
    rw [he,map_mul,map_mul,map_inv]
    change (A.val.normalizerMonoidHom x)⁻¹ * invariantLiftAction A k * A.val.normalizerMonoidHom x = a
    rw [hk]
    group

/-- The first larger-core identity in C.1.35, with the original Sylow join:
O₂(KS)=Q C_{O₂(KS)}(A), and that centralizer meets Q in A. -/
theorem MSData.joinCore_eq_core_sup_liftCentralizer (d : MSData c n) (hn : 1 < n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G)) :
    (K c ⊔ S c).pCoreIn 2 =
      Q c ⊔ ((K c ⊔ S c).pCoreIn 2 ⊓ Subgroup.centralizer (A.val : Set G)) ∧
    Q c ⊓ ((K c ⊔ S c).pCoreIn 2 ⊓ Subgroup.centralizer (A.val : Set G)) = A.val := by
  let P := (K c ⊔ S c).pCoreIn 2
  have hQP : Q c ≤ P := by
    rw [←sylow_join_commutator_eq c]
    exact le_normalizer_iff_commutator_le_left.mp ((le_sup_left : K c ≤ K c ⊔ S c).trans
      ((K c ⊔ S c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K c ⊔ S c) (pCore 2 (K c ⊔ S c : Subgroup G)))))
  constructor
  · apply le_antisymm ?_ (sup_le hQP inf_le_left)
    intro x hx
    let xN : normalizer (A.val : Set G) := ⟨x,hA (pCoreIn_le 2 _ hx)⟩
    have hxK : x ∈ normalizer (K c : Set G) :=
      c.normalizer_component.le ((sup_le (map_subtype_le _) inf_le_right) (pCoreIn_le 2 _ hx))
    have hxR := (d.invariantLift_sectionKernel_normalizer hn A).le
      ⟨d.joinCore_liftAction_mem_sectionKernel A hA x hx,liftAction_normalizes A xN hxK⟩
    obtain ⟨q,hq⟩ := hxR
    have hqN : (q : G) ∈ normalizer (A.val : Set G) := hA (hQP.trans (pCoreIn_le 2 _) q.property)
    let qN : normalizer (A.val : Set G) := ⟨q,hqN⟩
    have hker : qN⁻¹*xN ∈ A.val.normalizerMonoidHom.ker := by
      change A.val.normalizerMonoidHom (qN⁻¹*xN) = 1
      rw [map_mul,map_inv]
      change (invariantLiftCoreAction A q)⁻¹ * A.val.normalizerMonoidHom xN = 1
      rw [hq,inv_mul_cancel]
    have hc : (q : G)⁻¹*x ∈ Subgroup.centralizer (A.val : Set G) := by
      rwa [normalizerMonoidHom_ker] at hker
    have hpx : (q : G)⁻¹*x ∈ P := P.mul_mem (P.inv_mem (hQP q.property)) hx
    have hh := (Q c ⊔ (P ⊓ Subgroup.centralizer (A.val : Set G))).mul_mem
      (mem_sup_left q.property) (mem_sup_right ⟨hpx,hc⟩)
    simpa only [mul_inv_cancel_left] using hh
  · rw [←inf_assoc,inf_eq_left.mpr hQP,d.invariantCoreLifts_selfCentralizing A]

/-- The centralizer factor in C.1.35 has elementary exponent: squares are
fixed by K, and the original Sylow centralizer is trivial. -/
theorem MSData.joinCore_liftCentralizer_elementary (d : MSData c n)
    (A : invariantCoreLifts c) :
    IsElementaryAbelian 2 ((K c ⊔ S c).pCoreIn 2 ⊓ Subgroup.centralizer (A.val : Set G) : Subgroup G) := by
  let P := (K c ⊔ S c).pCoreIn 2
  let C := P ⊓ Subgroup.centralizer (A.val : Set G)
  let := (d.invariantCoreLifts_elementary A).1
  have hPC : K c ⊔ S c ≤ normalizer (P : Set G) :=
    (K c ⊔ S c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K c ⊔ S c)
        (pCore 2 (K c ⊔ S c : Subgroup G)))
  have hKC : K c ≤ normalizer (C : Set G) :=
    (le_inf (le_sup_left.trans hPC)
      (A.property.2.2.trans (normalizer_le_normalizer_centralizer A.val))).trans
      inf_normalizer_le_normalizer_inf
  have hd : ⁅K c,C⁆ ≤ A.val := by
    have hQ : ⁅K c,C⁆ ≤ Q c := by
      rw [←sylow_join_commutator_eq c,commutator_comm (K c) C]
      exact commutator_mono inf_le_left le_rfl
    have hC : ⁅K c,C⁆ ≤ C := le_normalizer_iff_commutator_le_right.mp hKC
    exact (le_inf hQ (hC.trans inf_le_right)).trans_eq (d.invariantCoreLifts_selfCentralizing A)
  have hCS : C ≤ S c :=
    inf_le_left.trans (c.block_join_core_le.trans (c.core_sylow.le.trans inf_le_left))
  apply elementary_of_central_displacements C A.val (K c) inf_le_right hd
  exact bot_unique ((inf_le_inf_right _ hCS).trans d.centralizer.le)

/-- The source has an actual Sylow-normalized elementary lift A and an
elementary centralizer C with O₂(KS)=QC, Q∩C=A and |A|=2^(6n). -/
theorem MSData.exists_joinCore_elementary_factorization (d : MSData c n) (hn : 1 < n) :
    ∃ A C : Subgroup G, U c < A ∧ A < Q c ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 2^(6*n) ∧
      K c ⊔ S c ≤ normalizer (A : Set G) ∧
      C = (K c ⊔ S c).pCoreIn 2 ⊓ Subgroup.centralizer (A : Set G) ∧
      IsElementaryAbelian 2 C ∧ (K c ⊔ S c).pCoreIn 2 = Q c ⊔ C ∧ Q c ⊓ C = A := by
  obtain ⟨A,hUA,hAQ,hE,hcard,hnA,_,_⟩ := d.exists_sylow_invariant_elementary_lift
  let a : invariantCoreLifts c := ⟨A,hUA,hAQ,le_sup_left.trans hnA⟩
  exact ⟨A,_,hUA,hAQ,hE,hcard,hnA,rfl,d.joinCore_liftCentralizer_elementary a,
    d.joinCore_eq_core_sup_liftCentralizer hn a hnA⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end

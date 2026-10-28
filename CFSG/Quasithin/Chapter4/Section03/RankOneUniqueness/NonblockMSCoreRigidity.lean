module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSLargerCore
public import Theory.Representation.FirstCohomologyConjugationSplitting
public import Theory.ThreeSubgroups

/-!
# Core centralizers in the original nonbinary MS configuration

Nonbinary natural first cohomology and C_S(K)=1 identify Z(O₂(KS))
with the original U=Z(Q). The three-subgroups lemma then shows that
C_{O₂(KS)}(Q) is that same center. Neither argument assumes Q=O₂(KS).

On each of the two complementary elementary lifts, the original O₂(K)
has exactly Q's action image. Their abelian factorization matches these
actions simultaneously with one element of Q. The remaining element
centralizes Q, proving O₂(K)=Q with the original embedded subgroups.

The larger identity O₂(KS)=Q still requires the C.1.35 rank argument.
The MSData constructor, secondary geometry and terminal exclusions remain
with qt-d-1222-rankone-uniqueness-nonblock; MSData is explicit here.
Source: Aschbacher–Smith C.1.35, printed pp.138–139, and original
4.3.10–11, printed p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Representation.OneCohomology
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

private theorem core_le_joinCore : Q c ≤ (K c ⊔ S c).pCoreIn 2 := by
  rw [←sylow_join_commutator_eq c]
  exact le_normalizer_iff_commutator_le_left.mp ((le_sup_left : K c ≤ K c ⊔ S c).trans
    ((K c ⊔ S c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K c ⊔ S c) (pCore 2 (K c ⊔ S c : Subgroup G)))))

omit [Finite G] in
private theorem joinCore_le_sylow : (K c ⊔ S c).pCoreIn 2 ≤ S c :=
  c.block_join_core_le.trans (c.core_sylow.le.trans inf_le_left)

omit [Finite G] in
private theorem centerIn_eq (X : Subgroup G) :
    (center X).map X.subtype = X ⊓ Subgroup.centralizer (X : Set G) := by
  ext x
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,mem_centralizer_iff.mpr ?_⟩
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  · rintro ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hc y y.property)

/-- Nonbinary natural cohomology identifies the center of the larger core,
without assuming that larger core equals Q. -/
theorem MSData.joinCore_center_eq (d : MSData c n) (hn : 1 < n) :
    (center ((K c ⊔ S c).pCoreIn 2)).map ((K c ⊔ S c).pCoreIn 2).subtype = U c := by
  let P := (K c ⊔ S c).pCoreIn 2
  let E := (center P).map P.subtype
  have hEP : E ≤ P := map_subtype_le _
  have hEC : E ≤ Subgroup.centralizer (P : Set G) := (centerIn_eq P).le.trans inf_le_right
  have hUP : U c ≤ P := (map_subtype_le _).trans core_le_joinCore
  have hUE : U c ≤ E := by
    change U c ≤ (center P).map P.subtype
    rw [centerIn_eq]
    exact le_inf hUP (le_centralizer_iff.mp d.joinCore_centralizes_center)
  have hKP : K c ≤ normalizer (P : Set G) :=
    (le_sup_left : K c ≤ K c ⊔ S c).trans
      ((K c ⊔ S c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K c ⊔ S c) (pCore 2 (K c ⊔ S c : Subgroup G))))
  have hKE : K c ≤ normalizer (E : Set G) := hKP.trans
    (normalizer_le_normalizer_characteristic_image P (center P))
  have hdisp : ⁅K c,E⁆ ≤ U c := by
    have hQ : ⁅K c,E⁆ ≤ Q c := by
      rw [←sylow_join_commutator_eq c,commutator_comm]
      exact commutator_mono hEP le_rfl
    have hE : ⁅K c,E⁆ ≤ E := le_normalizer_iff_commutator_le_right.mp hKE
    change ⁅K c,E⁆ ≤ (center (Q c)).map (Q c).subtype
    rw [centerIn_eq]
    exact le_inf hQ (hE.trans (hEC.trans (centralizer_le core_le_joinCore)))
  have hm := d.natural
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,hKU,_,hbot,e,he⟩ := hm
  let := hbot
  let u : U c ≃* Multiplicative (Fin 3 → d.field.Carrier) := QuotientGroup.quotientBot.symm.trans e
  have hu (k : K c) (v : Fin 3 → d.field.Carrier) :
      (u.symm (Multiplicative.ofAdd (Representation.specialLinearNatural 3
        (linearThreeActor d.model k) v)) : G) =
      k*(u.symm (Multiplicative.ofAdd v) : G)*(k : G)⁻¹ := by
    let x := u.symm (Multiplicative.ofAdd v)
    let y : U c := ⟨(k : G)*x*(k : G)⁻¹,(mem_normalizer_iff.mp (hKU k.property) x).mp x.property⟩
    have hh := he k x y rfl
    change (u y).toAdd = Representation.specialLinearNatural 3
      (linearThreeActor d.model k) (u x).toAdd at hh
    have hy : u y = Multiplicative.ofAdd (Representation.specialLinearNatural 3
        (linearThreeActor d.model k) v) := Multiplicative.toAdd.injective (by simpa [x] using hh)
    rw [←hy,u.symm_apply_apply]
  have hker (k : K c) (hk : linearThreeActor d.model k = 1) :
      (k : G) ∈ Subgroup.centralizer (E : Set G) := by
    have hk0 : k ∈ pCore 2 (K c) := (QuotientGroup.eq_one_iff k).mp
      (d.model.map_eq_one_iff.mp hk)
    have hKJ : K c ⊔ S c ≤ normalizer (K c : Set G) :=
      sup_le (K c).le_normalizer (inf_le_right.trans c.normalizer_component.le)
    have hkP := pCoreIn_mono_of_normalizes (p := 2) le_sup_left hKJ (mem_map_of_mem _ hk0)
    exact (le_centralizer_iff.mp hEC) hkP
  have hF : 2 < Nat.card d.field.Carrier := by
    rw [d.field.card_eq,d.degree_eq]
    exact (show (2 : ℕ)^1 < 2^n from pow_lt_pow_right₀ (by decide) hn)
  let := SLHigherNatural.H1_subsingleton_sl3_large_field hF
  have hs := sup_centralizer_eq_of_conjugation_H1 (K c) E (U c) hUE
    (linearThreeActor d.model) (d.model.surjective.comp (QuotientGroup.mk'_surjective _))
    (Representation.specialLinearNatural 3) u hu hker
    (fun k x => hdisp (commutator_mem_commutator k.property x.property))
  have hz : E ⊓ Subgroup.centralizer (K c : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ (hEP.trans joinCore_le_sylow)).trans d.centralizer.le)
  rw [hz,sup_bot_eq] at hs
  exact hs.symm


/-- The original Q is self-centralizing in the larger core, modulo its
natural center. The three-subgroups lemma first identifies this centralizer
with the larger core's center, then nonbinary cohomology removes the excess. -/
theorem MSData.joinCore_coreCentralizer_eq (d : MSData c n) (hn : 1 < n) :
    (K c ⊔ S c).pCoreIn 2 ⊓ Subgroup.centralizer (Q c : Set G) = U c := by
  let P := (K c ⊔ S c).pCoreIn 2
  let E := P ⊓ Subgroup.centralizer (Q c : Set G)
  have hKP : K c ≤ normalizer (P : Set G) :=
    (le_sup_left : K c ≤ K c ⊔ S c).trans
      ((K c ⊔ S c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K c ⊔ S c) (pCore 2 (K c ⊔ S c : Subgroup G))))
  have hKQ : K c ≤ normalizer (Q c : Set G) := (map_subtype_le _).trans (core_normalized c)
  have hKE : K c ≤ normalizer (E : Set G) :=
    (le_inf hKP (hKQ.trans (normalizer_le_normalizer_centralizer (Q c)))).trans
      inf_normalizer_le_normalizer_inf
  have hd : ⁅E,K c⁆ ≤ U c := by
    have hQ : ⁅E,K c⁆ ≤ Q c := by
      rw [←sylow_join_commutator_eq c]
      exact commutator_mono inf_le_left le_rfl
    have hE : ⁅E,K c⁆ ≤ E := le_normalizer_iff_commutator_le_left.mp hKE
    change ⁅E,K c⁆ ≤ (center (Q c)).map (Q c).subtype
    rw [centerIn_eq]
    exact le_inf hQ (hE.trans inf_le_right)
  have hrot₁ : ⁅⁅P,K c⁆,E⁆ = ⊥ := by
    rw [show ⁅P,K c⁆ = Q c from sylow_join_commutator_eq c]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp inf_le_right)
  have hrot₂ : ⁅⁅K c,E⁆,P⁆ = ⊥ := by
    rw [commutator_comm (K c) E]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hd.trans (le_centralizer_iff.mp d.joinCore_centralizes_center)
  have hcomm : ⁅⁅E,P⁆,K c⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate hrot₁ hrot₂
  have hEP : ⁅E,P⁆ ≤ P := (Subgroup.commutator_le_sup _ _).trans (sup_le inf_le_left le_rfl)
  have hEC : ⁅E,P⁆ ≤ Subgroup.centralizer (K c : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hbot : ⁅E,P⁆ = ⊥ :=
    bot_unique ((le_inf (hEP.trans joinCore_le_sylow) hEC).trans d.centralizer.le)
  have hEcenter : E ≤ (center P).map P.subtype := by
    rw [centerIn_eq]
    exact le_inf inf_le_left (commutator_eq_bot_iff_le_centralizer.mp hbot)
  apply le_antisymm (hEcenter.trans_eq (d.joinCore_center_eq hn))
  exact le_inf ((map_subtype_le _).trans core_le_joinCore)
    ((centerIn_eq (Q c)).le.trans inf_le_right)

private theorem originalCore_action_matches (d : MSData c n) (hn : 1 < n)
    (A : invariantCoreLifts c) (k : K c) (hk : k ∈ pCore 2 (K c)) :
    ∃ q ∈ Q c, ∀ a ∈ A.val, (k : G)*a*(k : G)⁻¹ = q*a*q⁻¹ := by
  obtain ⟨q,hq⟩ := (d.invariantLift_originalCore_image hn A).le (mem_map_of_mem _ hk)
  refine ⟨q,q.property,?_⟩
  intro a ha
  exact (congrArg Subtype.val (DFunLike.congr_fun hq (⟨a,ha⟩ : A.val))).symm

/-- The original intrinsic two-core is exactly its commutator Q. The two
complementary elementary lifts let their separate inner actions be matched
simultaneously; the remaining element centralizes Q and hence lies in U. -/
theorem MSData.originalCore_eq (d : MSData c n) (hn : 1 < n) :
    (K c).pCoreIn 2 = Q c := by
  obtain ⟨A,B,hAe,hBe,hAc,hBc,hAn,hBn,hi,hs,hCA,hCB⟩ :=
    d.exists_selfCentralizing_elementary_core_decomposition
  let := hAe
  let := hBe
  have hQK : Q c ≤ K c := (Subgroup.commutator_le_sup _ _).trans (sup_le (pCoreIn_le 2 _) le_rfl)
  have hAQ : A ≤ Q c := le_sup_left.trans_eq hs
  have hBQ : B ≤ Q c := le_sup_right.trans_eq hs
  have hAstrict : A < Q c := by
    apply lt_of_le_of_ne hAQ
    intro he
    have hh := hAc
    rw [he,d.core_card] at hh
    have hp : (2:ℕ)^(6*n) < 2^(9*n) := pow_lt_pow_right₀ (by decide) (by omega)
    omega
  have hBstrict : B < Q c := by
    apply lt_of_le_of_ne hBQ
    intro he
    have hh := hBc
    rw [he,d.core_card] at hh
    have hp : (2:ℕ)^(6*n) < 2^(9*n) := pow_lt_pow_right₀ (by decide) (by omega)
    omega
  have hUA : U c < A := by
    apply lt_of_le_of_ne (hi ▸ inf_le_left)
    intro he
    have hc : Q c ≤ Subgroup.centralizer (A : Set G) := by
      rw [←he]
      exact le_centralizer_iff.mp ((centerIn_eq (Q c)).le.trans inf_le_right)
    have hh := hCA
    rw [inf_eq_left.mpr hc] at hh
    exact hAstrict.ne hh.symm
  have hUB : U c < B := by
    apply lt_of_le_of_ne (hi ▸ inf_le_right)
    intro he
    have hc : Q c ≤ Subgroup.centralizer (B : Set G) := by
      rw [←he]
      exact le_centralizer_iff.mp ((centerIn_eq (Q c)).le.trans inf_le_right)
    have hh := hCB
    rw [inf_eq_left.mpr hc] at hh
    exact hBstrict.ne hh.symm
  let a : invariantCoreLifts c := ⟨A,hUA,hAstrict,hAn⟩
  let b : invariantCoreLifts c := ⟨B,hUB,hBstrict,hBn⟩
  have hfactor (q : G) (hq : q ∈ Q c) : ∃ x ∈ A, ∃ y ∈ B, x*y=q := by
    have hm : q ∈ A ⊔ B := hs.symm ▸ hq
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left A B (hBQ.trans (hQK.trans hAn))] at hm
    exact hm
  apply le_antisymm ?_ (le_normalizer_iff_commutator_le_left.mp
    ((K c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c)))))
  rintro k ⟨k,hk,rfl⟩
  change (k : G) ∈ Q c
  obtain ⟨q₁,hq₁,h₁⟩ := originalCore_action_matches d hn a k hk
  obtain ⟨q₂,hq₂,h₂⟩ := originalCore_action_matches d hn b k hk
  obtain ⟨a₁,ha₁,b₁,hb₁,rfl⟩ := hfactor q₁ hq₁
  obtain ⟨a₂,ha₂,b₂,hb₂,rfl⟩ := hfactor q₂ hq₂
  have hmatchA (x : G) (hx : x ∈ A) :
      (k : G)*x*(k : G)⁻¹ = (a₂*b₁)*x*(a₂*b₁)⁻¹ := by
    rw [h₁ x hx]
    have hy : b₁*x*b₁⁻¹ ∈ A := (mem_normalizer_iff.mp (hAn (hBQ.trans hQK hb₁)) x).mp hx
    have hc₁ := mem_centralizer_iff.mp (le_centralizer A ha₁) _ hy
    have hc₂ := mem_centralizer_iff.mp (le_centralizer A ha₂) _ hy
    calc
      (a₁*b₁)*x*(a₁*b₁)⁻¹ = a₁*(b₁*x*b₁⁻¹)*a₁⁻¹ := by group
      _ = b₁*x*b₁⁻¹ := by rw [←hc₁,mul_inv_cancel_right]
      _ = a₂*(b₁*x*b₁⁻¹)*a₂⁻¹ := by rw [←hc₂,mul_inv_cancel_right]
      _ = (a₂*b₁)*x*(a₂*b₁)⁻¹ := by group
  have hmatchB (x : G) (hx : x ∈ B) :
      (k : G)*x*(k : G)⁻¹ = (a₂*b₁)*x*(a₂*b₁)⁻¹ := by
    rw [h₂ x hx]
    have hc₁ := mem_centralizer_iff.mp (le_centralizer B hb₁) x hx
    have hc₂ := mem_centralizer_iff.mp (le_centralizer B hb₂) x hx
    calc
      (a₂*b₂)*x*(a₂*b₂)⁻¹ = a₂*(b₂*x*b₂⁻¹)*a₂⁻¹ := by group
      _ = a₂*x*a₂⁻¹ := by rw [←hc₂,mul_inv_cancel_right]
      _ = a₂*(b₁*x*b₁⁻¹)*a₂⁻¹ := by rw [←hc₁,mul_inv_cancel_right]
      _ = (a₂*b₁)*x*(a₂*b₁)⁻¹ := by group
  let q := a₂*b₁
  have hq : q ∈ Q c := (Q c).mul_mem (hAQ ha₂) (hBQ hb₁)
  have hcent : q⁻¹*(k : G) ∈ Subgroup.centralizer (Q c : Set G) := by
    have hAcent : q⁻¹*(k : G) ∈ Subgroup.centralizer (A : Set G) := by
      apply mem_centralizer_iff.mpr
      intro x hx
      have hh := congrArg (fun z : G => q⁻¹*z*(k : G)) (hmatchA x hx)
      dsimp [q] at hh ⊢
      group at hh ⊢
      exact hh.symm
    have hBcent : q⁻¹*(k : G) ∈ Subgroup.centralizer (B : Set G) := by
      apply mem_centralizer_iff.mpr
      intro x hx
      have hh := congrArg (fun z : G => q⁻¹*z*(k : G)) (hmatchB x hx)
      dsimp [q] at hh ⊢
      group at hh ⊢
      exact hh.symm
    apply mem_centralizer_iff.mpr
    intro x hx
    obtain ⟨y,hy,z,hz,rfl⟩ := hfactor x hx
    exact (Commute.mul_left (show Commute y (q⁻¹*(k : G)) from mem_centralizer_iff.mp hAcent y hy)
        (show Commute z (q⁻¹*(k : G)) from mem_centralizer_iff.mp hBcent z hz)).eq
  have hKP : (K c).pCoreIn 2 ≤ (K c ⊔ S c).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le (K c).le_normalizer (inf_le_right.trans c.normalizer_component.le))
  have hP : q⁻¹*(k : G) ∈ (K c ⊔ S c).pCoreIn 2 :=
    ((K c ⊔ S c).pCoreIn 2).mul_mem
      (((K c ⊔ S c).pCoreIn 2).inv_mem (core_le_joinCore hq)) (hKP (mem_map_of_mem _ hk))
  have hu := (d.joinCore_coreCentralizer_eq hn).le ⟨hP,hcent⟩
  have hh := (Q c).mul_mem hq ((map_subtype_le _) hu)
  simpa only [mul_inv_cancel_left] using hh

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end

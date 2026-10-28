module

public import Stellmacher.Recognition.FongWreathedCoordinates
public import Stellmacher.Recognition.FongWreathedLocal
public import Theory.GroupTheory.PPrimeCoreSupplement
public import ABG.ChapterII.Section3.SourceThreeWreathedQuotient
public import ABG.ChapterII.Section3.CharacteristicPowerQuotient

/-!
# Odd-core comparison for Fong's centralizers

In a finite simple group with a wreathed Sylow subgroup of order 32, use
the actual coordinates of `FongWreathedCoordinates`. The centralizers of
`F²` and `J = F⁴` have canonically isomorphic odd-core quotients. In each,
the image of `F²` generates a central subgroup of order four. If one
involution centralizer is solvable, both odd-core quotients have order 96,
and their further quotients by that cyclic subgroup are S₄. All these
statements hold for every presentation, independently of fusion orientation.

The original Sylow subgroup lies in both centralizers. Apply ABG's
Q-group Sylow-center theorem in `C(J)`: its odd core and `C(F²)` generate
`C(J)`. The core-supplement theorem identifies the two odd cores on
intersection and supplies the quotient equivalence. Surjectivity of the
restricted quotient map also proves the required centrality. The source
characteristic power is three, so the Q-group projective theorem gives
the order-96 group and the actual S₄ quotient, retaining the Sylow center
as its kernel. The canonical comparison carries the chosen square to
the chosen square, identifying both required quotient denominators.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), 65–76, pp. 70–71, following (5);
ABG II.3 Proposition 1 for the centralizer supplement.
-/

namespace Stellmacher.Recognition.FongWreathedIntrinsic
open ABG

variable {G : Type*} [Group G] (S : Sylow 2 G)
  (P : Wreathed.Presentation S 2)

local notation "CJ" => Subgroup.centralizer ({((J P : S) : G)} : Set G)
local notation "CF2" => Subgroup.centralizer ({((F P ^ 2 : S) : G)} : Set G)

include P in
private theorem presentation_shape : IsWreathedOfHeight S 2 :=
  ⟨P.height, P.card, P.s, P.t, P.z, P.s_pow, P.t_pow, P.z_sq,
    P.conj_s, P.conj_t, P.commute, P.generate⟩

public theorem ambientCentralizer_F_cube :
    Subgroup.centralizer ({((F P ^ 3 : S) : G)} : Set G) =
      Subgroup.centralizer ({((F P : S) : G)} : Set G) := by
  ext g
  constructor
  · intro hg
    have h : Commute g ((F P ^ 3 : S) : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hg
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have heq : ((F P ^ 3 : S) : G) ^ 3 = ((F P : S) : G) :=
      congrArg Subtype.val (F_cube_cube P)
    simpa only [heq] using (h.pow_right 3).eq
  · intro hg
    have h : Commute g ((F P : S) : G) := Subgroup.mem_centralizer_singleton_iff.mp hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h.pow_right 3).eq

public theorem sylow_le_centralizerF2 : (S : Subgroup G) ≤ CF2 := by
  intro s hs
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val
    (Subgroup.mem_center_iff.mp (F_sq_mem_center P) (⟨s, hs⟩ : S))

public theorem centralizerF2_le_centralizerJ : CF2 ≤ CJ := by
  intro g hg
  have h : Commute g ((F P ^ 2 : S) : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hpow := h.pow_right 2
  have heq : ((F P ^ 2 : S) : G) ^ 2 = ((J P : S) : G) := by
    change (((F P ^ 2) ^ 2 : S) : G) = ((J P : S) : G)
    rw [← pow_mul, show 2 * 2 = 4 from rfl, F_four]
  simpa only [heq] using hpow.eq

public theorem sylow_le_centralizerJ : (S : Subgroup G) ≤ CJ :=
  (sylow_le_centralizerF2 S P).trans (centralizerF2_le_centralizerJ S P)

/-- The actual element `F²`, regarded as an element of `C(J)`. -/
@[expose] public def squareInCentralizerJ : CJ :=
  ⟨(F P ^ 2 : S), sylow_le_centralizerJ S P (F P ^ 2).property⟩

/-- The same actual square, in its own centralizer. -/
@[expose] public def squareInCentralizerF2 : CF2 :=
  ⟨(F P ^ 2 : S), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

variable [Finite G] [IsSimpleGroup G]

public theorem isConj_X_J : IsConj ((X P : S) : G) ((J P : S) : G) := by
  have hQD := isQDGroup_of_simple_wreathed32 S (presentation_shape S P)
  have hc : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  obtain ⟨r, _, _, hcov⟩ := hc
  obtain ⟨i, hi⟩ := hcov (X P : S) ((Subgroup.orderOf_coe (X P)).trans (X_orderOf P))
  obtain ⟨j, hj⟩ := hcov (J P : S) ((Subgroup.orderOf_coe (J P)).trans (J_orderOf P))
  exact hi.trans ((Subsingleton.elim i j) ▸ hj.symm)

public theorem centralizerJ_isQGroup : IsQGroup CJ :=
  (qd_involutionCentralizer_isQGroup
    (isQDGroup_of_simple_wreathed32 S (presentation_shape S P)) (J P : S)
      ((Subgroup.orderOf_coe (J P)).trans (J_orderOf P))).1

/-- `C(F²)` supplements the odd core inside `C(J)`. -/
public theorem centralizerF2_oddCore_supplement :
    pPrimeCore 2 CJ ⊔ (CF2).subgroupOf CJ = ⊤ := by
  let T : Sylow 2 CJ := S.subtype (sylow_le_centralizerJ S P)
  let e : T ≃* S := Subgroup.subgroupOfEquivOfLe (sylow_le_centralizerJ S P)
  have ht : e.symm (F P ^ 2) ∈ Subgroup.center T := by
    apply Subgroup.mem_center_iff.mpr
    intro t
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_center_iff.mp (F_sq_mem_center P) (e t)
  have hz : squareInCentralizerJ S P ∈ subgroupCenter (T : Subgroup CJ) :=
    ⟨e.symm (F P ^ 2), ht, rfl⟩
  have hle : Subgroup.centralizer (subgroupCenter (T : Subgroup CJ) : Set CJ) ≤
      (CF2).subgroupOf CJ := by
    intro g hg
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hg _ hz).symm)
  apply top_unique
  rw [← qGroup_eq_oddCore_mul_sylowCenterCentralizer (centralizerJ_isQGroup S P) T]
  exact sup_le_sup_left hle _

/-- The odd core of the restricted subgroup is exactly the core intersection. -/
public theorem centralizerF2_oddCore_intersection :
    pPrimeCore 2 ((CF2).subgroupOf CJ) = (pPrimeCore 2 CJ).subgroupOf ((CF2).subgroupOf CJ) :=
  (Subgroup.quotient_pPrimeCore_equiv_of_sup_eq_top 2 ((CF2).subgroupOf CJ)
    (centralizerF2_oddCore_supplement S P)).1

/-- The inclusion followed by the quotient map retains the actual elements. -/
@[expose] public def centralizerF2ToQuotientJ : CF2 →* (CJ ⧸ pPrimeCore 2 CJ) :=
  (QuotientGroup.mk' (pPrimeCore 2 CJ)).comp
    (Subgroup.inclusion (centralizerF2_le_centralizerJ S P))

public theorem centralizerF2ToQuotientJ_surjective :
    Function.Surjective (centralizerF2ToQuotientJ S P) := by
  let q := QuotientGroup.mk' (pPrimeCore 2 CJ)
  have hmap : ((CF2).subgroupOf CJ).map q = ⊤ := by
    have h := congrArg (Subgroup.map q) (centralizerF2_oddCore_supplement S P)
    simpa only [q, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using h
  intro y
  obtain ⟨g, hg, rfl⟩ := hmap.ge (show y ∈ ⊤ from Subgroup.mem_top y)
  exact ⟨⟨g.val, hg⟩, rfl⟩

public theorem centralizerF2ToQuotientJ_ker :
    (centralizerF2ToQuotientJ S P).ker = pPrimeCore 2 CF2 := by
  let e : (CF2).subgroupOf CJ ≃* CF2 :=
    Subgroup.subgroupOfEquivOfLe (centralizerF2_le_centralizerJ S P)
  have hcore : pPrimeCore 2 CF2 =
      (pPrimeCore 2 ((CF2).subgroupOf CJ)).comap e.symm.toMonoidHom := by
    rw [← Subgroup.map_equiv_eq_comap_symm', pPrimeCore_map_iso]
  rw [hcore, centralizerF2_oddCore_intersection]
  ext x
  exact QuotientGroup.eq_one_iff (N := pPrimeCore 2 CJ)
    (Subgroup.inclusion (centralizerF2_le_centralizerJ S P) x)

/-- The canonical odd-core quotient equivalence induced by inclusion. -/
public noncomputable def centralizerF2OddCoreEquiv :
    (CF2 ⧸ pPrimeCore 2 CF2) ≃* (CJ ⧸ pPrimeCore 2 CJ) :=
  (QuotientGroup.quotientMulEquivOfEq
    (centralizerF2ToQuotientJ_ker S P).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (centralizerF2ToQuotientJ S P)
        (centralizerF2ToQuotientJ_surjective S P))

public theorem centralizerF2OddCoreEquiv_mk (x : CF2) :
    centralizerF2OddCoreEquiv S P (QuotientGroup.mk' (pPrimeCore 2 CF2) x) =
      centralizerF2ToQuotientJ S P x := by
  unfold centralizerF2OddCoreEquiv
  rfl

public theorem centralizerF2OddCoreEquiv_square :
    centralizerF2OddCoreEquiv S P
        (QuotientGroup.mk' (pPrimeCore 2 CF2) (squareInCentralizerF2 S P)) =
      QuotientGroup.mk' (pPrimeCore 2 CJ) (squareInCentralizerJ S P) := by
  rw [centralizerF2OddCoreEquiv_mk]
  rfl

/-- The two centralizers have the same quotient by their respective odd cores. -/
public theorem centralizerF2_oddCore_quotient_equiv :
    Nonempty ((CF2 ⧸ pPrimeCore 2 CF2) ≃* (CJ ⧸ pPrimeCore 2 CJ)) :=
  ⟨centralizerF2OddCoreEquiv S P⟩

public theorem squareInCentralizerJ_quotient_mem_center :
    QuotientGroup.mk' (pPrimeCore 2 CJ) (squareInCentralizerJ S P) ∈
      Subgroup.center (CJ ⧸ pPrimeCore 2 CJ) := by
  let q := QuotientGroup.mk' (pPrimeCore 2 CJ)
  let M := (CF2).subgroupOf CJ
  have hmap : M.map q = ⊤ := by
    have h := congrArg (Subgroup.map q) (centralizerF2_oddCore_supplement S P)
    simpa only [q, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using h
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨g, hg, rfl⟩ := hmap.ge (show y ∈ ⊤ from Subgroup.mem_top y)
  have hcomm : g * squareInCentralizerJ S P = squareInCentralizerJ S P * g := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  simpa only [map_mul] using congrArg q hcomm

/-- The exact cyclic image used as the denominator of Fong's `S₄` quotient is normal. -/
public theorem squareInCentralizerJ_quotient_zpowers_normal :
    (Subgroup.zpowers (QuotientGroup.mk' (pPrimeCore 2 CJ)
      (squareInCentralizerJ S P))).Normal := by
  have hle : Subgroup.zpowers (QuotientGroup.mk' (pPrimeCore 2 CJ)
      (squareInCentralizerJ S P)) ≤ Subgroup.center (CJ ⧸ pPrimeCore 2 CJ) :=
    Subgroup.zpowers_le.mpr (squareInCentralizerJ_quotient_mem_center S P)
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_center_iff.mp (hle hx) g, mul_inv_cancel_right]
  exact hx

/-- Equivalently, the subgroup `O(C(J))⟨F²⟩` is normal before taking the quotient. -/
public theorem squareInCentralizerJ_oddCore_sup_normal :
    (pPrimeCore 2 CJ ⊔ Subgroup.zpowers (squareInCentralizerJ S P)).Normal := by
  let q := QuotientGroup.mk' (pPrimeCore 2 CJ)
  have hi : ((Subgroup.zpowers (squareInCentralizerJ S P)).map q).Normal := by
    rw [MonoidHom.map_zpowers]
    exact squareInCentralizerJ_quotient_zpowers_normal S P
  let := hi
  have h : (((Subgroup.zpowers (squareInCentralizerJ S P)).map q).comap q).Normal :=
    inferInstance
  simpa only [Subgroup.comap_map_eq, q, QuotientGroup.ker_mk', sup_comm] using h

omit [IsSimpleGroup G] in
public theorem squareInCentralizerJ_quotient_orderOf :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 CJ) (squareInCentralizerJ S P)) = 4 := by
  let T : Sylow 2 CJ := S.subtype (sylow_le_centralizerJ S P)
  let e : T ≃* S := Subgroup.subgroupOfEquivOfLe (sylow_le_centralizerJ S P)
  let q := QuotientGroup.mk' (pPrimeCore 2 CJ)
  let f := q.comp (T : Subgroup CJ).subtype
  have hdis : Disjoint (T : Subgroup CJ) (pPrimeCore 2 CJ) := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := CJ)).pow_left n
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxO : (x : CJ) ∈ pPrimeCore 2 CJ := (QuotientGroup.eq_one_iff _).mp hx
    exact Subtype.ext (Subgroup.disjoint_def.mp hdis x.property hxO)
  exact (orderOf_injective f hinj (e.symm (F P ^ 2))).trans
    ((e.symm.orderOf_eq _).trans (F_sq_orderOf P))

omit [IsSimpleGroup G] in
public theorem squareInCentralizerJ_quotient_zpowers_card :
    Nat.card (Subgroup.zpowers (QuotientGroup.mk' (pPrimeCore 2 CJ)
      (squareInCentralizerJ S P))) = 4 := by
  rw [Nat.card_zpowers, squareInCentralizerJ_quotient_orderOf]

/-- The actual order-96 quotient and its projective map with prescribed kernel. -/
public theorem centralizerJ_oddCore_projective
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    Nat.card (CJ ⧸ pPrimeCore 2 CJ) = 96 ∧
      ∃ f : (CJ ⧸ pPrimeCore 2 CJ) →* Equiv.Perm (Fin 4),
        Function.Surjective f ∧ f.ker = Subgroup.zpowers
          (QuotientGroup.mk' (pPrimeCore 2 CJ) (squareInCentralizerJ S P)) := by
  let T : Sylow 2 CJ := S.subtype (sylow_le_centralizerJ S P)
  let e : T ≃* S := Subgroup.subgroupOfEquivOfLe (sylow_le_centralizerJ S P)
  let q := QuotientGroup.mk' (pPrimeCore 2 CJ)
  let R := T.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  obtain ⟨eR⟩ := sylow_quotient_equiv T (pPrimeCore 2 CJ) pPrimeCore_coprime_card
  have hR : IsWreathedOfHeight R 2 :=
    wreathed_equiv (e.symm.trans eR) (presentation_shape S P)
  have hQD := isQDGroup_of_simple_wreathed32 S (presentation_shape S P)
  have hq : HasSourceQCharacteristicPower CJ 3 :=
    (sourceCharacteristicPower_three_of_simple_wreathed32 S (presentation_shape S P) x hx).at_involution hQD (J P : S) ((Subgroup.orderOf_coe (J P)).trans (J_orderOf P))
  obtain ⟨hcard, f, hf, hker⟩ := qGroup_wreathed32_sourceThree_projective
    (centralizerJ_isQGroup S P).oddCore_quotient (pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2))
    R hR hq.oddCore_quotient
  have hzR : q (squareInCentralizerJ S P) ∈ (R : Subgroup (CJ ⧸ pPrimeCore 2 CJ)) :=
    Subgroup.mem_map_of_mem q (show squareInCentralizerJ S P ∈ (T : Subgroup CJ) from
      (e.symm (F P ^ 2)).property)
  have hzcenter : q (squareInCentralizerJ S P) ∈ subgroupCenter (R : Subgroup (CJ ⧸ pPrimeCore 2 CJ)) := by
    refine ⟨⟨q (squareInCentralizerJ S P), hzR⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro r
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (squareInCentralizerJ_quotient_mem_center S P) r.val
  have hle : Subgroup.zpowers (q (squareInCentralizerJ S P)) ≤
      subgroupCenter (R : Subgroup (CJ ⧸ pPrimeCore 2 CJ)) := Subgroup.zpowers_le.mpr hzcenter
  have hcR : Nat.card (subgroupCenter (R : Subgroup (CJ ⧸ pPrimeCore 2 CJ))) = 4 := by
    obtain ⟨PR⟩ := Wreathed.nonempty_presentation hR
    rw [subgroupCenter, Subgroup.card_map_of_injective (R : Subgroup (CJ ⧸ pPrimeCore 2 CJ)).subtype_injective,
      PR.card_center]
    decide
  have hZ := Subgroup.eq_of_le_of_card_ge hle (by
    rw [hcR, squareInCentralizerJ_quotient_zpowers_card])
  exact ⟨hcard, f, hf, hker.trans hZ.symm⟩

/-- Fong's further quotient of `C(J)/O(C(J))` is the actual symmetric group. -/
public theorem centralizerJ_oddCore_square_quotient_equiv
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    let Z := Subgroup.zpowers
      (QuotientGroup.mk' (pPrimeCore 2 CJ) (squareInCentralizerJ S P))
    let _ : Z.Normal := squareInCentralizerJ_quotient_zpowers_normal S P
    Nonempty (((CJ ⧸ pPrimeCore 2 CJ) ⧸ Z) ≃* Equiv.Perm (Fin 4)) := by
  let := squareInCentralizerJ_quotient_zpowers_normal S P
  obtain ⟨_, f, hf, hker⟩ := centralizerJ_oddCore_projective S P x hx
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

/-- The same order 96 for the square centralizer follows through the canonical map. -/
public theorem centralizerF2_oddCore_card
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    Nat.card (CF2 ⧸ pPrimeCore 2 CF2) = 96 :=
  (Nat.card_congr (centralizerF2OddCoreEquiv S P).toEquiv).trans
    (centralizerJ_oddCore_projective S P x hx).1

public theorem centralizerF2_oddCore_projective
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    ∃ f : (CF2 ⧸ pPrimeCore 2 CF2) →* Equiv.Perm (Fin 4),
      Function.Surjective f ∧ f.ker = Subgroup.zpowers
        (QuotientGroup.mk' (pPrimeCore 2 CF2) (squareInCentralizerF2 S P)) := by
  obtain ⟨_, f, hf, hker⟩ := centralizerJ_oddCore_projective S P x hx
  let e := centralizerF2OddCoreEquiv S P
  have hmap : (Subgroup.zpowers
      (QuotientGroup.mk' (pPrimeCore 2 CF2) (squareInCentralizerF2 S P))).map e.toMonoidHom =
      Subgroup.zpowers (QuotientGroup.mk' (pPrimeCore 2 CJ) (squareInCentralizerJ S P)) := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers (centralizerF2OddCoreEquiv_square S P)
  refine ⟨f.comp e.toMonoidHom, hf.comp e.surjective, ?_⟩
  rw [← MonoidHom.comap_ker, hker, ← hmap, Subgroup.comap_map_eq,
    (MonoidHom.ker_eq_bot_iff _).mpr e.injective, sup_bot_eq]

public theorem squareInCentralizerF2_quotient_zpowers_normal :
    (Subgroup.zpowers (QuotientGroup.mk' (pPrimeCore 2 CF2)
      (squareInCentralizerF2 S P))).Normal := by
  have hc : QuotientGroup.mk' (pPrimeCore 2 CF2) (squareInCentralizerF2 S P) ∈
      Subgroup.center (CF2 ⧸ pPrimeCore 2 CF2) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply (centralizerF2OddCoreEquiv S P).injective
    rw [map_mul, map_mul, centralizerF2OddCoreEquiv_square]
    exact Subgroup.mem_center_iff.mp (squareInCentralizerJ_quotient_mem_center S P) _
  have hle := Subgroup.zpowers_le.mpr hc
  refine ⟨fun z hz g => ?_⟩
  rw [Subgroup.mem_center_iff.mp (hle hz) g, mul_inv_cancel_right]
  exact hz

/-- Fong's further quotient of `C(F²)/O(C(F²))`, with its exact cyclic denominator. -/
public theorem centralizerF2_oddCore_square_quotient_equiv
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    let Z := Subgroup.zpowers
      (QuotientGroup.mk' (pPrimeCore 2 CF2) (squareInCentralizerF2 S P))
    let _ : Z.Normal := squareInCentralizerF2_quotient_zpowers_normal S P
    Nonempty (((CF2 ⧸ pPrimeCore 2 CF2) ⧸ Z) ≃* Equiv.Perm (Fin 4)) := by
  let := squareInCentralizerF2_quotient_zpowers_normal S P
  obtain ⟨f, hf, hker⟩ := centralizerF2_oddCore_projective S P x hx
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

end Stellmacher.Recognition.FongWreathedIntrinsic

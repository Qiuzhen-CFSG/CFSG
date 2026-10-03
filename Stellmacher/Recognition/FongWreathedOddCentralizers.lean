module

public import Stellmacher.Recognition.FongWreathedCentralizerQuotients
public import Theory.GroupTheory.SpecificGroups.SymmetricFourCentralizer
public import ABG.ChapterII.Section1.WreathedOrderEightCentralizer

/-!
# Fong's odd complements and small centralizer quotients

For Fong's actual wreathed coordinates, the centralizers of F, F³, and XF²
have normal odd complements. Their odd-core quotients are respectively
cyclic of order eight, cyclic of order eight, and the product of two cyclic
groups of order four.

Inside C(J), pass through its odd core and its central cyclic four-subgroup
to S₄. Each chosen element has nonidentity involution image, whose centralizer
is a two-group. Lifting through the central four-subgroup and the odd core
proves the normal-complement assertion. The internal wreathed centralizers
then identify the quotient models.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), pp. 70–71, following (5).
-/

namespace Stellmacher.Recognition.FongWreathedIntrinsic
open ABG

private theorem quotient_sylow_equiv {H : Type*} [Group H] [Finite H]
    (R : Sylow 2 H) (hH : HasNormalPComplement 2 H) :
    Nonempty ((H ⧸ pPrimeCore 2 H) ≃* R) := by
  let q := QuotientGroup.mk' (pPrimeCore 2 H)
  let T := R.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := sylow_quotient_equiv R (pPrimeCore 2 H) pPrimeCore_coprime_card
  have htop : (T : Subgroup (H ⧸ pPrimeCore 2 H)) = ⊤ :=
    (T.is_maximal' ((isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 H hH).to_subgroup ⊤) le_top).symm
  exact ⟨((Subgroup.topEquiv).symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e.symm⟩

variable {G : Type*} [Group G] (S : Sylow 2 G)
  (P : Wreathed.Presentation S 2)

local notation "CJ" => Subgroup.centralizer ({((J P : S) : G)} : Set G)

/-- The original Sylow subgroup maps faithfully into the odd-core quotient of C(J). -/
@[expose] public def sylowToOddQuotientJ : S →* (CJ ⧸ pPrimeCore 2 CJ) :=
  (QuotientGroup.mk' (pPrimeCore 2 CJ)).comp
    ((S : Subgroup G).subtype.codRestrict CJ (fun s => sylow_le_centralizerJ S P s.property))

variable [Finite G]

public theorem sylowToOddQuotientJ_injective :
    Function.Injective (sylowToOddQuotientJ S P) := by
  let i : S →* CJ := (S : Subgroup G).subtype.codRestrict CJ
    (fun s => sylow_le_centralizerJ S P s.property)
  have hdis : Disjoint i.range (pPrimeCore 2 CJ) := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := (S.isPGroup'.of_surjective i.rangeRestrict i.rangeRestrict_surjective).exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := CJ)).pow_left n
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro y hy
  have hyO : i y ∈ pPrimeCore 2 CJ := (QuotientGroup.eq_one_iff _).mp hy
  have hy1 : i y = 1 := Subgroup.disjoint_def.mp hdis ⟨y, rfl⟩ hyO
  exact show y = 1 from Subtype.ext (congrArg (fun z : CJ => z.val) hy1)

omit [Finite G] in
public theorem ambientCentralizer_le_centralizerJ_of_pow (y : S) (n : ℕ)
    (hy : y ^ n = J P) :
    Subgroup.centralizer ({(y : G)} : Set G) ≤ CJ := by
  intro g hg
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hc : Commute g (y : G) := Subgroup.mem_centralizer_singleton_iff.mp hg
  simpa only [← Subgroup.coe_pow, hy] using (hc.pow_right n).eq

variable [IsSimpleGroup G]

private theorem normalComplement_of_projective_involution
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))]
    (y : S) (hy : y ∉ Subgroup.center S) (hy2 : y ^ 2 ∈ Subgroup.center S)
    (hle : Subgroup.centralizer ({(y : G)} : Set G) ≤ CJ) :
    HasNormalPComplement 2 (Subgroup.centralizer ({(y : G)} : Set G)) := by
  let Q := CJ ⧸ pPrimeCore 2 CJ
  let q := QuotientGroup.mk' (pPrimeCore 2 CJ)
  let a := sylowToOddQuotientJ S P
  obtain ⟨_, f, _, hker⟩ := centralizerJ_oddCore_projective S P x hx
  have hkcent : f.ker ≤ Subgroup.center Q := by
    rw [hker]
    exact Subgroup.zpowers_le.mpr (squareInCentralizerJ_quotient_mem_center S P)
  have hfne : f (a y) ≠ 1 := by
    intro h
    have hcent := hkcent (MonoidHom.mem_ker.mpr h)
    apply hy
    apply Subgroup.mem_center_iff.mpr
    intro s
    apply sylowToOddQuotientJ_injective S P
    simpa only [map_mul] using Subgroup.mem_center_iff.mp hcent (a s)
  have hf2 : f (a y) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow]
    apply MonoidHom.mem_ker.mp
    rw [hker]
    rw [center_eq P] at hy2
    obtain ⟨n, hn⟩ := hy2
    rw [← hn, map_zpow]
    exact (Subgroup.zpowers (q (squareInCentralizerJ S P))).zpow_mem
      (Subgroup.mem_zpowers _) n
  have hkTwo : IsPGroup 2 f.ker := by
    apply IsPGroup.of_card (n := 2)
    rw [hker, squareInCentralizerJ_quotient_zpowers_card]
    rfl
  have hpre : IsPGroup 2 ((Subgroup.centralizer ({f (a y)} : Set (Equiv.Perm (Fin 4)))).comap f) :=
    (Equiv.Perm.centralizer_involution_isTwoGroup _ hfne hf2).comap_of_ker_isPGroup f hkTwo
  let C := Subgroup.centralizer ({(y : G)} : Set G)
  let i : C →* CJ := Subgroup.inclusion hle
  let r : C →* Q := q.comp i
  have hrTwo : IsPGroup 2 r.range := by
    apply hpre.to_le
    rintro _ ⟨c, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hc : i c * ((S : Subgroup G).subtype.codRestrict CJ
        (fun s => sylow_le_centralizerJ S P s.property)) y =
        ((S : Subgroup G).subtype.codRestrict CJ
        (fun s => sylow_le_centralizerJ S P s.property)) y * i c :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.property)
    simpa only [r, a, sylowToOddQuotientJ, map_mul, MonoidHom.comp_apply,
      MonoidHom.codRestrict_apply] using congrArg (f.comp q) hc
  have hodd : Nat.Coprime 2 (Nat.card r.ker) := by
    let k : r.ker →* pPrimeCore 2 CJ :=
      (i.comp r.ker.subtype).codRestrict (pPrimeCore 2 CJ)
        (fun c => (QuotientGroup.eq_one_iff _).mp c.property)
    have hki : Function.Injective k := by
      intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : pPrimeCore 2 CJ => z.val.val) huv
    exact pPrimeCore_coprime_card.of_dvd_right (Subgroup.card_dvd_of_injective k hki)
  exact ⟨r.ker, inferInstance, hodd,
    hrTwo.of_equiv (QuotientGroup.quotientKerEquivRange r).symm⟩

public theorem centralizerF_hasNormalPComplement
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    HasNormalPComplement 2 (Subgroup.centralizer ({((F P : S) : G)} : Set G)) := by
  apply normalComplement_of_projective_involution S P x hx (F P)
  · intro hf
    have hcard : Nat.card S = 8 := by
      have heq : Subgroup.centralizer ({F P} : Set S) = ⊤ := by
        apply top_unique
        intro s _
        exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hf s)
      simpa only [heq, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).toEquiv] using
        card_centralizer_F P
    have := P.card
    norm_num at this
    omega
  · exact F_sq_mem_center P
  · exact ambientCentralizer_le_centralizerJ_of_pow S P (F P) 4 (F_four P)

public theorem centralizerF_cube_hasNormalPComplement
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    HasNormalPComplement 2 (Subgroup.centralizer ({((F P ^ 3 : S) : G)} : Set G)) := by
  rw [ambientCentralizer_F_cube S P]
  exact centralizerF_hasNormalPComplement S P x hx

omit [Finite G] [IsSimpleGroup G] in
private theorem XF_sq_noncentral : X P * F P ^ 2 ∉ Subgroup.center S := by
  intro hf
  have hcard : Nat.card S = 16 := by
    have heq : Subgroup.centralizer ({X P * F P ^ 2} : Set S) = ⊤ := by
      apply top_unique
      intro s _
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hf s)
    simpa only [heq, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).toEquiv] using
      card_centralizer_XF_sq P
  have := P.card
  norm_num at this
  omega

public theorem centralizerXF_sq_hasNormalPComplement
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    HasNormalPComplement 2 (Subgroup.centralizer ({((X P * F P ^ 2 : S) : G)} : Set G)) := by
  apply normalComplement_of_projective_involution S P x hx (X P * F P ^ 2)
  · exact XF_sq_noncentral S P
  · rw [XF_sq_sq, ← F_four, show 4 = 2 * 2 from rfl, pow_mul]
    exact (Subgroup.center S).pow_mem (F_sq_mem_center P) 2
  · exact ambientCentralizer_le_centralizerJ_of_pow S P _ 2 (XF_sq_sq P)

/-- A noncentral coordinate with a power equal to J is noncentral in every
ambient Sylow subgroup that contains it. -/
public theorem not_central_in_sylow_of_pow_J
    (y : S) (hy : y ∉ Subgroup.center S) (n : ℕ) (hpow : y ^ n = J P)
    (T : Sylow 2 G) (hyT : (y : G) ∈ (T : Subgroup G)) :
    (⟨(y : G), hyT⟩ : T) ∉ Subgroup.center T := by
  intro hcentral
  have hTC : (T : Subgroup G) ≤ Subgroup.centralizer ({(y : G)} : Set G) := by
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hcentral (⟨t, ht⟩ : T)))
  have hTJ := hTC.trans (ambientCentralizer_le_centralizerJ_of_pow S P y n hpow)
  let R : Sylow 2 CJ := T.subtype hTJ
  let e : R ≃* T := Subgroup.subgroupOfEquivOfLe hTJ
  let yJ : CJ := ⟨y, sylow_le_centralizerJ S P y.property⟩
  have hyZ : yJ ∈ subgroupCenter (R : Subgroup CJ) := by
    refine ⟨e.symm ⟨y, hyT⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro r
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_center_iff.mp hcentral (e r)
  let q := QuotientGroup.mk' (pPrimeCore 2 CJ)
  have hmap : (Subgroup.centralizer (subgroupCenter (R : Subgroup CJ) : Set CJ)).map q = ⊤ := by
    have hh := congrArg (Subgroup.map q)
      (qGroup_eq_oddCore_mul_sylowCenterCentralizer (centralizerJ_isQGroup S P) R)
    simpa only [Subgroup.map_sup, q, QuotientGroup.map_mk'_self, bot_sup_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using hh
  have hycent : q yJ ∈ Subgroup.center (CJ ⧸ pPrimeCore 2 CJ) := by
    apply Subgroup.mem_center_iff.mpr
    intro z
    obtain ⟨c, hc, rfl⟩ := hmap.ge (show z ∈ ⊤ from Subgroup.mem_top z)
    simpa only [map_mul] using congrArg q
      ((Subgroup.mem_centralizer_iff.mp hc) yJ hyZ).symm
  apply hy
  apply Subgroup.mem_center_iff.mpr
  intro s
  apply sylowToOddQuotientJ_injective S P
  simpa only [map_mul, sylowToOddQuotientJ, MonoidHom.comp_apply,
    MonoidHom.codRestrict_apply, Subgroup.subtype_apply, q, yJ] using
    Subgroup.mem_center_iff.mp hycent (sylowToOddQuotientJ S P s)

omit [IsSimpleGroup G] in
include S P in
private theorem orderEight_centralizer_sylow_model (y : G) (hy : orderOf y = 8)
    (R : Sylow 2 (Subgroup.centralizer ({y} : Set G))) :
    Nonempty (R ≃* Multiplicative (ZMod 8)) := by
  let C := Subgroup.centralizer ({y} : Set G)
  let yC : C := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hycent : yC ∈ Subgroup.center C := by
    apply Subgroup.mem_center_iff.mpr
    intro c
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.property)
  have hZle : Subgroup.zpowers yC ≤ Subgroup.center C := Subgroup.zpowers_le.mpr hycent
  let : (Subgroup.zpowers yC).Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZle hz) g, mul_inv_cancel_right]
    exact hz⟩
  have hZtwo : IsPGroup 2 (Subgroup.zpowers yC) := by
    apply IsPGroup.of_card (n := 3)
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe yC, hy]
    rfl
  have hyR : yC ∈ (R : Subgroup C) := hZtwo.le_sylow_of_normal R (Subgroup.mem_zpowers yC)
  obtain ⟨Q, hQ⟩ := R.exists_comap_subtype_eq
  let yQ : Q := ⟨y, show yC ∈ (Q : Subgroup G).comap C.subtype from hQ.symm ▸ hyR⟩
  let e : R ≃* Subgroup.centralizer ({yQ} : Set Q) :=
    { toFun := fun r => ⟨⟨r.val.val, show r.val ∈ (Q : Subgroup G).comap C.subtype from hQ.symm ▸ r.property⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp r.val.property))⟩
      invFun := fun z => ⟨⟨z.val.val, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp z.property))⟩,
        hQ ▸ z.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hshape : IsWreathedOfHeight Q 2 := wreathed_equiv (Sylow.equiv S Q)
    ⟨P.height, P.card, P.s, P.t, P.z, P.s_pow, P.t_pow, P.z_sq,
      P.conj_s, P.conj_t, P.commute, P.generate⟩
  obtain ⟨PQ⟩ := Wreathed.nonempty_presentation hshape
  have hc := PQ.centralizer_eq_zpowers_of_order_eight yQ ((Subgroup.orderOf_coe yQ).symm.trans hy)
  let ez : Subgroup.zpowers yQ ≃* Multiplicative (ZMod 8) :=
    mulEquivOfCyclicCardEq (by rw [Nat.card_zpowers, ← Subgroup.orderOf_coe yQ, hy]; simp)
  exact ⟨e.trans ((MulEquiv.subgroupCongr hc).trans ez)⟩

private theorem XF_sq_centralizer_sylow_model :
    ∃ R : Sylow 2 (Subgroup.centralizer ({((X P * F P ^ 2 : S) : G)} : Set G)),
      Nonempty (R ≃* Subgroup.centralizer ({X P * F P ^ 2} : Set S)) := by
  let y := X P * F P ^ 2
  let C := Subgroup.centralizer ({(y : G)} : Set G)
  let D := Subgroup.centralizer ({y} : Set S)
  let j : D →* C :=
    { toFun := fun d => ⟨d.val.val, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp d.property))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro d e h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C => z.val) h))
  have hjTwo : IsPGroup 2 j.range :=
    (S.isPGroup'.to_subgroup D).of_surjective j.rangeRestrict j.rangeRestrict_surjective
  obtain ⟨R, hR⟩ := hjTwo.exists_le_sylow
  obtain ⟨Q, hQ⟩ := R.exists_comap_subtype_eq
  let yC : C := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hyR : yC ∈ (R : Subgroup C) :=
    hR ⟨⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, rfl⟩
  have hyQ : (y : G) ∈ (Q : Subgroup G) :=
    show yC ∈ (Q : Subgroup G).comap C.subtype from hQ.symm ▸ hyR
  let rQ : R →* Q :=
    { toFun := fun r => ⟨r.val.val,
        show r.val ∈ (Q : Subgroup G).comap C.subtype from hQ.symm ▸ r.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hrQ : Function.Injective rQ := by
    intro u v h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Q => z.val) h))
  have hproper : rQ.range ≠ ⊤ := by
    intro htop
    apply not_central_in_sylow_of_pow_J S P y (XF_sq_noncentral S P) 2
      (XF_sq_sq P) Q hyQ
    apply Subgroup.mem_center_iff.mpr
    intro t
    obtain ⟨r, rfl⟩ := htop.ge (show t ∈ ⊤ from Subgroup.mem_top t)
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp r.val.property)
  have hindex := rQ.range.one_lt_index_of_ne_top hproper
  have hmul := rQ.range.index_mul_card
  have hRcard : Nat.card rQ.range = Nat.card R :=
    Nat.card_congr (MonoidHom.ofInjective hrQ).symm.toEquiv
  have hQcard : Nat.card Q = 32 :=
    (Nat.card_congr (Sylow.equiv Q S).toEquiv).trans P.card
  rw [hRcard, hQcard] at hmul
  have hbound : Nat.card R ≤ 16 := by nlinarith
  have hjcard : Nat.card j.range = 16 :=
    (Nat.card_congr (MonoidHom.ofInjective hj).symm.toEquiv).trans
      (card_centralizer_XF_sq P)
  have heq : j.range = (R : Subgroup C) :=
    Subgroup.eq_of_le_of_card_ge hR (by rw [hjcard]; exact hbound)
  exact ⟨R, ⟨(MulEquiv.subgroupCongr heq.symm).trans (MonoidHom.ofInjective hj).symm⟩⟩

public theorem centralizerXF_sq_oddCore_quotient_equiv
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    Nonempty (((Subgroup.centralizer ({((X P * F P ^ 2 : S) : G)} : Set G)) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({((X P * F P ^ 2 : S) : G)} : Set G))) ≃*
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  obtain ⟨R, ⟨d⟩⟩ := XF_sq_centralizer_sylow_model S P
  obtain ⟨e⟩ := quotient_sylow_equiv R (centralizerXF_sq_hasNormalPComplement S P x hx)
  obtain ⟨m⟩ := centralizer_XF_sq_model P
  exact ⟨(e.trans d).trans m⟩

public theorem centralizerXF_sq_oddCore_card
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    Nat.card ((Subgroup.centralizer ({((X P * F P ^ 2 : S) : G)} : Set G)) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({((X P * F P ^ 2 : S) : G)} : Set G))) = 16 := by
  obtain ⟨e⟩ := centralizerXF_sq_oddCore_quotient_equiv S P x hx
  simpa using Nat.card_congr e.toEquiv

public theorem centralizerF_oddCore_quotient_equiv
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    Nonempty (((Subgroup.centralizer ({((F P : S) : G)} : Set G)) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({((F P : S) : G)} : Set G))) ≃*
        Multiplicative (ZMod 8)) := by
  let R : Sylow 2 (Subgroup.centralizer ({((F P : S) : G)} : Set G)) := Classical.arbitrary _
  obtain ⟨e⟩ := quotient_sylow_equiv R (centralizerF_hasNormalPComplement S P x hx)
  obtain ⟨d⟩ := orderEight_centralizer_sylow_model S P (F P : S)
    ((Subgroup.orderOf_coe (F P)).trans (F_orderOf P)) R
  exact ⟨e.trans d⟩

public theorem centralizerF_cube_oddCore_quotient_equiv
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    Nonempty (((Subgroup.centralizer ({((F P ^ 3 : S) : G)} : Set G)) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({((F P ^ 3 : S) : G)} : Set G))) ≃*
        Multiplicative (ZMod 8)) := by
  rw [ambientCentralizer_F_cube S P]
  exact centralizerF_oddCore_quotient_equiv S P x hx

public theorem centralizerF_oddCore_card
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    Nat.card ((Subgroup.centralizer ({((F P : S) : G)} : Set G)) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({((F P : S) : G)} : Set G))) = 8 := by
  obtain ⟨e⟩ := centralizerF_oddCore_quotient_equiv S P x hx
  simpa using Nat.card_congr e.toEquiv

public theorem centralizerF_cube_oddCore_card
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    Nat.card ((Subgroup.centralizer ({((F P ^ 3 : S) : G)} : Set G)) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({((F P ^ 3 : S) : G)} : Set G))) = 8 := by
  rw [ambientCentralizer_F_cube S P]
  exact centralizerF_oddCore_card S P x hx

end Stellmacher.Recognition.FongWreathedIntrinsic

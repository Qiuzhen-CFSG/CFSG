module
public import Theory.SpecificGroups.OddThreeRank
public import Theory.SpecificGroups.OddThreeCyclicCentralizers
public import Theory.SpecificGroups.SU3.UnitaryTwoPerfectCentralizer
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import ABG.ChapterII.Section2.UnitaryCard

/-!
# Sylow obstruction for a ternary-seven residual

A full Sylow overgroup of a normal SL₂(7) in an odd ternary group lies
in the centralizer of its unique central involution. Lift through the
actual cubic central quotient of GL₂(7) or GU₂(7). Perfectness makes its
centralizer scalar, and quasisimplicity makes the overgroup's two-core
centralize it. The scalar orders 6 and 8 bound that two-core, whereas the
full Sylow orders are 32 and 128. Thus the overgroup's two-core quotient
cannot have order dividing 168. Special and projective groups and arbitrary
supplied Hermitian forms are all retained.

The actual consumer is the original point residual intersection in
Chapter12.Section05.NaturalSource.Local.Components.PointTernaryExclusion.
Source: Aschbacher--Smith, 12.5.3, printed p.818, and A.3.21(a), p.55.
-/

public noncomputable section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.OddThreeSevenResidual
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem core_card_dvd_centralizer {H : Type*} [Group H] [Finite H]
    (B J : Subgroup H) [IsQuasisimple B] (hBJ : B ≤ J)
    (hn : J ≤ normalizer (B : Set H)) :
    Nat.card (pCore 2 J) ∣ Nat.card (centralizer (B : Set H)) := by
  let A := B.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hBJ).symm
  let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
  have hc : pCore 2 J ≤ centralizer (A : Set J) :=
    le_centralizer_iff.mp ((show IsComponent J A from
      ⟨(inferInstance : A.Normal).isSubnormal,inferInstance⟩).le_centralizer_of_solvable_normal (pCore 2 J))
  let f : pCore 2 J →* centralizer (B : Set H) :=
    (J.subtype.comp (pCore 2 J).subtype).codRestrict _ (by
      intro x y hy
      exact congrArg Subtype.val (hc x.property ⟨y,hBJ hy⟩ hy))
  exact card_dvd_of_injective f (fun x y he =>
    Subtype.ext (Subtype.ext (congrArg (fun c : centralizer (B : Set H) => (c : H)) he)))

private theorem centralizer_card_dvd_of_lift {A H : Type*} [Group A] [Finite A]
    [Group H] [Finite H] (f : A →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center A) (P : Subgroup A) [Group.IsPerfect P]
    {B : Subgroup H} (hP : P.map f = B) :
    Nat.card (centralizer (B : Set H)) ∣ Nat.card (centralizer (P : Set A)) := by
  have he : (centralizer (B : Set H)).comap f = centralizer (P : Set A) := by
    rw [←hP,comap_centralizer_map_eq_of_perfect f P
      (hc.trans (center_le_centralizer (P : Set A)))]
  let e := MulEquiv.subgroupCongr he
  exact card_dvd_of_surjective ((f.subgroupComap (centralizer (B : Set H))).comp e.symm.toMonoidHom)
    ((f.subgroupComap_surjective_of_surjective _ hf).comp e.symm.surjective)

private theorem two_power_dvd_of_cube_kernel {A H : Type*} [Group A] [Finite A]
    [Group H] [Finite H] (f : A →* H) (hf : Function.Surjective f)
    (h3 : ∀ a ∈ f.ker, a^3 = 1) {n : ℕ} (hd : 2^n ∣ Nat.card A) :
    2^n ∣ Nat.card H := by
  have hk : IsPGroup 3 f.ker := fun x => ⟨1,Subtype.ext (h3 x x.property)⟩
  obtain ⟨k,hk⟩ := hk.exists_card_dvd_pow
  have hcop : Nat.Coprime (2^n) (Nat.card f.ker) :=
    (((by decide : Nat.Coprime 2 3).pow_left n).pow_right k).coprime_dvd_right hk
  apply hcop.dvd_of_dvd_mul_left
  have he := f.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top] at he
  rwa [he]

private theorem quotient_bound_contradiction {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (B J : Subgroup H) [IsQuasisimple B]
    (hBJ : B ≤ J) (hn : J ≤ normalizer (B : Set H))
    (hTJ : (T : Subgroup H) ≤ J)
    {c n : ℕ} (hc : Nat.card (centralizer (B : Set H)) ∣ c)
    (hfull : 2^n ∣ Nat.card H) (hbad : ¬2^n ∣ c*168)
    (hsmall : Nat.card (J ⧸ pCore 2 J) ∣ 168) : False := by
  have hcore := (core_card_dvd_centralizer B J hBJ hn).trans hc
  have hj : Nat.card J ∣ c*168 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 J),mul_comm]
    exact Nat.mul_dvd_mul hcore hsmall
  exact hbad (((T.pow_dvd_card_of_pow_dvd_card hfull).trans (card_dvd_of_le hTJ)).trans hj)

private theorem noncommutative_cover {A H : Type*} [Group A] [Group H]
    (f : A →* H) (hf : Function.Surjective f) (B : Subgroup H)
    [IsQuasisimple B] : ¬IsMulCommutative A := by
  intro ha
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  apply Group.IsPerfect.not_isMulCommutative B
  apply IsMulCommutative.of_comm
  intro x y
  obtain ⟨a,ha'⟩ := hf x
  obtain ⟨b,hb'⟩ := hf y
  apply Subtype.ext
  change (x : H) * y = (y : H) * x
  rw [←ha',←hb',←map_mul,←map_mul,ha.is_comm.comm]

/-- A full Sylow overgroup of a normal quasisimple subgroup in a cubic
central quotient of GL₂(7) cannot have two-core quotient of order dividing 168. -/
theorem linear_centralizer_no_small_quotient
    {F H : Type*} [Field F] [Finite F] [Group H] [Finite H]
    (hF : Nat.card F = 7) (f : GL (Fin 2) F →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ center (GL (Fin 2) F)) (h3 : ∀ a ∈ f.ker, a^3 = 1)
    (T : Sylow 2 H) (B J : Subgroup H) [IsQuasisimple B]
    (hBJ : B ≤ J) (hn : J ≤ normalizer (B : Set H)) (hTJ : (T : Subgroup H) ≤ J) :
    ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168 := by
  obtain ⟨S,A,e,_,_,_,he⟩ := OddThreeLevi.exists_perfect_sylow_normalized_lift
    (MonoidHom.id _) Function.injective_id (noncommutative_cover f hf B)
    f hf hk h3 T B (hTJ.trans hn)
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  let : Nontrivial A := e.nontrivial
  have hmap : A.map f = B := by
    apply le_antisymm
    · rintro _ ⟨a,ha,rfl⟩
      exact (he ⟨a,ha⟩) ▸ (e ⟨a,ha⟩).property
    · intro b hb
      obtain ⟨a,ha⟩ := e.surjective ⟨b,hb⟩
      exact ⟨a,a.property,(he a).trans (congrArg Subtype.val ha)⟩
  have hc : Nat.card (centralizer (B : Set H)) ∣ 6 := by
    apply (centralizer_card_dvd_of_lift f hf hk A hmap).trans
    apply (card_dvd_of_le (GeneralLinearGroup.centralizer_le_scalar_of_noncommutative A
      (Group.IsPerfect.not_isMulCommutative A))).trans
    have hd := card_dvd_of_surjective (GeneralLinearGroup.scalar (Fin 2) (R := F)).rangeRestrict
      (GeneralLinearGroup.scalar (Fin 2) (R := F)).rangeRestrict_surjective
    simpa only [Nat.card_units,hF] using hd
  have hfull : 2^5 ∣ Nat.card H := by
    apply two_power_dvd_of_cube_kernel f hf h3
    let : Fintype F := Fintype.ofFinite F
    rw [Matrix.card_GL_field,←Nat.card_eq_fintype_card,hF]
    norm_num [Fin.prod_univ_two]
  exact quotient_bound_contradiction T B J hBJ hn hTJ hc hfull (by decide)

/-- The corresponding actual GU₂(7) scalar bound retains its order-eight
center and the full order-128 Sylow two-part. -/
theorem unitary_centralizer_no_small_quotient
    {H : Type*} [Group H] [Finite H]
    (f : ABG.GU2 7 1 one_ne_zero →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ center (ABG.GU2 7 1 one_ne_zero)) (h3 : ∀ a ∈ f.ker, a^3 = 1)
    (T : Sylow 2 H) (B J : Subgroup H) [IsQuasisimple B]
    (hBJ : B ≤ J) (hn : J ≤ normalizer (B : Set H)) (hTJ : (T : Subgroup H) ≤ J) :
    ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168 := by
  obtain ⟨S,A,e,_,_,_,he⟩ := OddThreeLevi.exists_perfect_sylow_normalized_lift
    (ABG.unitaryForm 2 7 1 one_ne_zero).unitarySubgroup.subtype Subtype.val_injective
    (noncommutative_cover f hf B) f hf hk h3 T B (hTJ.trans hn)
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  let : Nontrivial A := e.nontrivial
  have hmap : A.map f = B := by
    apply le_antisymm
    · rintro _ ⟨a,ha,rfl⟩
      exact (he ⟨a,ha⟩) ▸ (e ⟨a,ha⟩).property
    · intro b hb
      obtain ⟨a,ha⟩ := e.surjective ⟨b,hb⟩
      exact ⟨a,a.property,(he a).trans (congrArg Subtype.val ha)⟩
  have hc : Nat.card (centralizer (B : Set H)) ∣ 8 := by
    have hd := centralizer_card_dvd_of_lift f hf hk A hmap
    rwa [ABG.GU2_noncommutative_centralizer_card 7 1 one_ne_zero A
      (Group.IsPerfect.not_isMulCommutative A)] at hd
  have hfull : 2^7 ∣ Nat.card H := by
    apply two_power_dvd_of_cube_kernel f hf h3
    rw [ABG.GU2_card 7 1 (by decide) one_ne_zero]
    decide
  exact quotient_bound_contradiction T B J hBJ hn hTJ hc hfull (by decide)
private theorem no_small_quotient_of_centralizers
    {Q : Type*} [Group Q] [Finite Q]
    (hcentralizers : ∀ (z : Q), orderOf z = 2 →
      ∀ (S : Sylow 2 (centralizer ({z} : Set Q)))
        (A I : Subgroup (centralizer ({z} : Set Q))), IsQuasisimple A →
        A ≤ I → I ≤ normalizer (A : Set (centralizer ({z} : Set Q))) →
        (S : Subgroup _) ≤ I → ¬ Nat.card (I ⧸ pCore 2 I) ∣ 168)
    (T : Sylow 2 Q) (B J : Subgroup Q) [IsQuasisimple B]
    (hc : Nat.card (center B) = 2) (hBJ : B ≤ J)
    (hn : J ≤ normalizer (B : Set Q)) (hTJ : (T : Subgroup Q) ≤ J)
    (hsmall : Nat.card (J ⧸ pCore 2 J) ∣ 168) : False := by
  let Z := (center B).map B.subtype
  have hZ : Nat.card Z = 2 := by rw [card_map_of_injective B.subtype_injective,hc]
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hZ])
  have hN : normalizer (B : Set Q) ≤ centralizer ({(z : Q)} : Set Q) :=
    (normalizer_le_normalizer_characteristic_image B (center B)).trans
      ((normalizer_le_centralizer_of_card_two Z hZ).trans
        (centralizer_le (Set.singleton_subset_iff.mpr z.property)))
  let C := centralizer ({(z : Q)} : Set Q)
  have hJC : J ≤ C := hn.trans hN
  have hBC : B ≤ C := hBJ.trans hJC
  let eB := subgroupOfEquivOfLe hBC
  let eJ := subgroupOfEquivOfLe hJC
  have hnC : J.subgroupOf C ≤ normalizer (B.subgroupOf C : Set C) := by
    rw [←subgroupOf_normalizer_eq hBC]
    exact subgroupOf_mono C hn
  apply hcentralizers z ((orderOf_coe z).trans hz) (T.subtype (hTJ.trans hJC))
    (B.subgroupOf C) (J.subgroupOf C) (IsQuasisimple.of_mulEquiv eB.symm)
    (subgroupOf_mono C hBJ) hnC (subgroupOf_mono C hTJ)
  rwa [Nat.card_congr (QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)).toEquiv]

/-- In PSL₃(7), an SL₂(7) residual and its actual full Sylow normalizer
cannot have the exterior point quotient of order dividing 168. -/
theorem projective_linear_no_small_quotient
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 7)
    (T : Sylow 2 PSL(3,F)) (B J : Subgroup PSL(3,F))
    (e : B ≃* SL(2,ZMod 7)) (hBJ : B ≤ J)
    (hn : J ≤ normalizer (B : Set PSL(3,F))) (hTJ : (T : Subgroup _) ≤ J) :
    ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168 := by
  let : Group.IsPerfect SL(2,ZMod 7) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three _ (by norm_num)
  let : IsQuasisimple SL(2,ZMod 7) := ⟨ProjectiveSpecialLinearGroup.rank_two_simple (by norm_num)⟩
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e.symm
  have hc : Nat.card (center B) = 2 := by
    rw [Nat.card_congr (centerCongr e).toEquiv,Atlas.ExceptionalSupport.card_sl_center]
    norm_num
  apply no_small_quotient_of_centralizers ?_ T B J hc hBJ hn hTJ
  intro z hz S A I hA hAI hnA hSI
  let := hA
  have h2 : (2 : F) ≠ 0 := OddThreeRank.two_ne_zero_of_odd_card
    (by decide : Odd 7) (k := 1) (by simpa using hF)
  obtain ⟨f,hf,hk,h3⟩ := PSL3.OddInvolutionFixed.exists_gl2_cubic_central_surjection z hz h2
  exact linear_centralizer_no_small_quotient hF f hf hk h3 S A I hAI hnA hSI

/-- The same obstruction holds for every supplied Hermitian form of PSU₃(7),
using the full GU₂ centralizer and its actual cubic covering map. -/
theorem projective_unitary_no_small_quotient
    {F : Type*} [Field F] [Finite F] (M : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hF : Nat.card F = 7^2) (hconj : ∀ x, M.conj x = x^7)
    (T : Sylow 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup M))
    (B J : Subgroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup M))
    (e : B ≃* SL(2,ZMod 7)) (hBJ : B ≤ J)
    (hn : J ≤ normalizer (B : Set _)) (hTJ : (T : Subgroup _) ≤ J) :
    ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168 := by
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup M) :=
    Finite.of_surjective M.specialToProjective M.specialToProjective_surjective
  let : Group.IsPerfect SL(2,ZMod 7) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three _ (by norm_num)
  let : IsQuasisimple SL(2,ZMod 7) := ⟨ProjectiveSpecialLinearGroup.rank_two_simple (by norm_num)⟩
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e.symm
  have hc : Nat.card (center B) = 2 := by
    rw [Nat.card_congr (centerCongr e).toEquiv,Atlas.ExceptionalSupport.card_sl_center]
    norm_num
  apply no_small_quotient_of_centralizers ?_ T B J hc hBJ hn hTJ
  intro z hz S A I hA hAI hnA hSI
  let := hA
  obtain ⟨f,hf,hk,h3⟩ := SU3.OddCubicCentralizer.surjection 7 (by decide) F M hF hconj z hz
  exact unitary_centralizer_no_small_quotient f hf hk h3 S A I hAI hnA hSI
/-- Surjection only decreases the order of the quotient by the two-core. -/
theorem core_quotient_card_dvd_of_surjective
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    (f : A →* H) (hf : Function.Surjective f) :
    Nat.card (H ⧸ pCore 2 H) ∣ Nat.card (A ⧸ pCore 2 A) := by
  have hm : (pCore 2 A).map f ≤ pCore 2 H :=
    le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
  let g := QuotientGroup.map (pCore 2 A) (pCore 2 H) f (map_le_iff_le_comap.mp hm)
  exact card_dvd_of_surjective g
    (QuotientGroup.map_surjective_of_surjective _ _ f
      ((QuotientGroup.mk'_surjective _).comp hf) (map_le_iff_le_comap.mp hm))

/-- The smaller SL₂(7) and the full Sylow survive a central cubic quotient,
with the original normalizing subgroup and its two-core quotient bound. -/
theorem projective_transfer
    {Q H : Type*} [Group Q] [Finite Q] [Group H] [Finite H]
    (f : Q →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ center Q) (h3 : ∀ x ∈ f.ker, x^3 = 1)
    (T : Sylow 2 Q) (B J : Subgroup Q) (e : B ≃* SL(2,ZMod 7))
    (hBJ : B ≤ J) (hn : J ≤ normalizer (B : Set Q)) (hTJ : (T : Subgroup Q) ≤ J)
    (hsmall : Nat.card (J ⧸ pCore 2 J) ∣ 168) :
    ∃ _e' : B.map f ≃* SL(2,ZMod 7), B.map f ≤ J.map f ∧
      J.map f ≤ normalizer (B.map f : Set H) ∧
      (T.mapSurjective hf : Subgroup H) ≤ J.map f ∧
      Nat.card (J.map f ⧸ pCore 2 (J.map f)) ∣ 168 := by
  have hc : Nat.card (center B) = 2 := by
    rw [Nat.card_congr (centerCongr e).toEquiv,Atlas.ExceptionalSupport.card_sl_center]
    norm_num
  let e' := MulEquiv.ofBijective (f.subgroupMap B)
    ⟨OddThreeLevi.injective_on_subgroup_of_center_two f hk h3 B hc,f.subgroupMap_surjective B⟩
  exact ⟨e'.symm.trans e,map_mono hBJ,
    (map_mono hn).trans (B.le_normalizer_map f),map_mono hTJ,
    (core_quotient_card_dvd_of_surjective (f.subgroupMap J) (f.subgroupMap_surjective J)).trans hsmall⟩

/-- Special linear degree three keeps the complete central cover until the
canonical projectivization, which preserves the smaller SL₂(7) faithfully. -/
theorem special_linear_no_small_quotient
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 7)
    (T : Sylow 2 SL(3,F)) (B J : Subgroup SL(3,F))
    (e : B ≃* SL(2,ZMod 7)) (hBJ : B ≤ J)
    (hn : J ≤ normalizer (B : Set SL(3,F))) (hTJ : (T : Subgroup _) ≤ J) :
    ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168 := by
  intro hsmall
  let f := PSL3.projection F
  have hk : f.ker ≤ center SL(3,F) := by rw [PSL3.projection_ker]
  have h3 : ∀ x ∈ f.ker, x^3 = 1 := by
    intro x hx
    have hd := (orderOf_dvd_natCard (⟨x,hk hx⟩ : center SL(3,F))).trans (SL3.card_center_dvd_three F)
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp hd)
  obtain ⟨e',hBJ',hn',hTJ',hsmall'⟩ := projective_transfer f (PSL3.projection_surjective F)
    hk h3 T B J e hBJ hn hTJ hsmall
  exact projective_linear_no_small_quotient hF (T.mapSurjective (PSL3.projection_surjective F))
    (B.map f) (J.map f) e' hBJ' hn' hTJ' hsmall'

/-- Special unitary degree three retains the original form and cubic kernel. -/
theorem special_unitary_no_small_quotient
    {F : Type*} [Field F] [Finite F] (M : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hF : Nat.card F = 7^2) (hconj : ∀ x, M.conj x = x^7)
    (T : Sylow 2 M.specialSubgroup) (B J : Subgroup M.specialSubgroup)
    (e : B ≃* SL(2,ZMod 7)) (hBJ : B ≤ J)
    (hn : J ≤ normalizer (B : Set _)) (hTJ : (T : Subgroup _) ≤ J) :
    ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168 := by
  intro hsmall
  let f := M.specialToProjective
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup M) :=
    Finite.of_surjective f M.specialToProjective_surjective
  have h3 : ∀ x ∈ f.ker, x^3 = 1 := fun x hx =>
    congrArg Subtype.val (M.specialToProjective_ker_cube ⟨x,hx⟩)
  obtain ⟨e',hBJ',hn',hTJ',hsmall'⟩ := projective_transfer f M.specialToProjective_surjective
    M.specialToProjective_ker_le_center h3 T B J e hBJ hn hTJ hsmall
  exact projective_unitary_no_small_quotient M hF hconj (T.mapSurjective M.specialToProjective_surjective)
    (B.map f) (J.map f) e' hBJ' hn' hTJ' hsmall'
end Theory.SpecificGroups.OddThreeSevenResidual



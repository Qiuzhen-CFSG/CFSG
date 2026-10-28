module

public import Mathlib.GroupTheory.GroupAction.OfQuotient
public import Stellmacher.SectionOne.CenterThreeGF4Embedding
public import Stellmacher.SectionOne.GLFourTwoClassification
public import Stellmacher.SectionOne.SLThreeFourClassification
public import Theory.GroupAction.Quotient
public import Theory.Representation.CardFourCommutingActions
public import Theory.Representation.CentralCardFourKernel
public import Theory.Representation.InvertedCardFourQuotientIndex

/-!
# The small-index involution p-group classification

This module proves the reduced classification at the heart of Stellmacher's
Lemma (1.3).  An odd normal `p`-subgroup `F`, together with an involution `x`,
generates the ambient group and acts faithfully and without fixed quotient on
an elementary abelian `2`-group `V`.  If the `x`-fixed-point index is at most
four, then `F` and `V` fall into exactly the cyclic, small linear, or
extraspecial alternatives stated by the source.

The proof follows the induction on `|F||V|` in
`refs/latex/stellmacher-n-group.tex`, proof of (1.3), pp. 15--16.  A central
element inverted by `x` has action commutator of order four or sixteen.  The
first case descends to its fixed-point quotient, while the second invokes the
`GL₄(2)` endpoint.  When `x` centralizes `Z(F)`, the center supplies a faithful
`GF(4)` structure; two noncommuting inverted generators give the `SL₃(4)`
endpoint.  If they generate a proper subgroup `F₀`, induction makes `F₀`
extraspecial of order `27`.  The normalizer chain
`F₀ ≤ C_F(Z(F₀)) < N_F(C_F(Z(F₀)))` and coprime action then force two rotated
triple commutators to vanish, contradicting the three-subgroup lemma.

The final ambient-action adapter applies the same restriction construction to
`F⟨x⟩` acting on `[V,F]` and transports the alternatives back to `F`.
If the restricted fixed-point index is four, injection of its involution
commutator image into the original image forces the original index to be
four as well. Coprime double-commutator idempotence is exported for the
source-facing application `F=[O₂′(G),x]`.
-/

@[expose] public section

open scoped IsMulCommutative commutatorElement

namespace Stellmacher.SectionOne
universe u v

private theorem involution_card_eq_fixed_mul_commutator
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite V] [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x : G) (hx : IsInvolution x) :
    Nat.card V =
      Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) *
        Nat.card (commutatorAction (Subgroup.zpowers x) V) := by
  classical
  let R : Subgroup G := Subgroup.zpowers x
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  have hcardR : Nat.card R = 2 := by
    simpa [R, Nat.card_zpowers] using hxorder
  let rx : R := ⟨x, Subgroup.mem_zpowers x⟩
  let d : V →* V :=
    { toFun := fun v => v⁻¹ * (x • v)
      map_one' := by simp
      map_mul' := by
        intro v w
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  have hker : d.ker = FixedPoints.subgroup R V := by
    ext v
    constructor
    · intro hv
      rw [FixedPoints.mem_subgroup]
      intro r
      have hvx : x • v = v := by
        exact (eq_of_inv_mul_eq_one (MonoidHom.mem_ker.mp hv)).symm
      by_cases hr : r = 1
      · simp [hr]
      · obtain ⟨z, hzne, hzuniq⟩ :=
          (Nat.card_eq_two_iff' (1 : R)).mp hcardR
        have hrxne : rx ≠ 1 := by
          intro h
          exact hx.1 (congrArg Subtype.val h)
        have hre : r = rx := (hzuniq r hr).trans (hzuniq rx hrxne).symm
        simpa [hre, rx] using hvx
    · intro hv
      rw [MonoidHom.mem_ker]
      have hvx := (FixedPoints.mem_subgroup (M := R) (a := v)).1 hv rx
      exact inv_mul_eq_one.mpr (by simpa [rx] using hvx.symm)
  have hrange : d.range = commutatorAction R V := by
    apply le_antisymm
    · intro z hz
      rcases hz with ⟨v, rfl⟩
      change v⁻¹ * (x • v) ∈ commutatorAction R V
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨rx, v, rfl⟩
    · rw [commutatorAction_eq_closure]
      refine (Subgroup.closure_le (K := d.range)).2 ?_
      intro z hz
      rcases hz with ⟨r, v, rfl⟩
      by_cases hr : r = 1
      · subst r
        exact ⟨1, by simp [d]⟩
      · obtain ⟨z, hzne, hzuniq⟩ :=
          (Nat.card_eq_two_iff' (1 : R)).mp hcardR
        have hrxne : rx ≠ 1 := by
          intro h
          exact hx.1 (congrArg Subtype.val h)
        have hre : r = rx := (hzuniq r hr).trans (hzuniq rx hrxne).symm
        exact ⟨v, by simp [d, hre, rx]⟩
  calc
    Nat.card V = Nat.card d.ker * d.ker.index := d.ker.card_mul_index.symm
    _ = Nat.card d.ker * Nat.card d.range := by rw [Subgroup.index_ker]
    _ = Nat.card (FixedPoints.subgroup R V) *
        Nat.card (commutatorAction R V) := by rw [hker, hrange]

private theorem involution_commutator_card_le_four
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite V] [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (x : G) (hx : IsInvolution x)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V)) :
    Nat.card (commutatorAction (Subgroup.zpowers x) V) ≤ 4 := by
  have hcard := involution_card_eq_fixed_mul_commutator (V := V) x hx
  rw [hcard, mul_comm 4] at hindex
  exact Nat.le_of_mul_le_mul_left hindex Nat.card_pos

private theorem exists_nontrivial_center_element_inverted_by_involution
    {G : Type u} [Group G]
    (F : Subgroup G) (hFnorm : F.Normal)
    (x : G) (hx : IsInvolution x)
    (hcomm :
      ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ ≠ ⊥) :
    ∃ a : G, a ≠ 1 ∧
      a ∈ (Subgroup.center F).map F.subtype ∧
      x * a * x⁻¹ = a⁻¹ := by
  classical
  let K : Subgroup G := (Subgroup.center F).map F.subtype
  let R : Subgroup G := Subgroup.zpowers x
  have hnle : ¬K ≤ Subgroup.centralizer (R : Set G) := by
    intro hle
    exact hcomm (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle)
  have hnsubset : ¬(K : Set G) ⊆ Subgroup.centralizer (R : Set G) := hnle
  obtain ⟨z, hzK, hznot⟩ := Set.not_subset.mp hnsubset
  have hzconj : x * z * x⁻¹ ≠ z := by
    intro heq
    apply hznot
    change z ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
    have hxz : x * z = z * x := by
      calc
        x * z = (x * z * x⁻¹) * x := by simp [mul_assoc]
        _ = z * x := by rw [heq]
    exact (show Commute x z from hxz).zpow_left n |>.eq
  let : F.Normal := hFnorm
  let : (Subgroup.center F).Characteristic := Subgroup.centerCharacteristic
  have hKnorm : K.Normal := by
    dsimp [K]
    infer_instance
  let a : G := z⁻¹ * (x * z * x⁻¹)
  have haK : a ∈ K :=
    K.mul_mem (K.inv_mem hzK) (hKnorm.conj_mem z hzK x)
  have hane : a ≠ 1 := by
    intro ha
    exact hzconj (inv_mul_eq_one.mp ha).symm
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two hxorder
  have hxsq : x * x = 1 := by simpa [pow_two] using hx.2
  refine ⟨a, hane, ?_, ?_⟩
  · simpa [K] using haK
  · simp [a, hxinv, hxsq, mul_assoc]

private theorem elementaryAbelian_subgroup
    {V : Type v} [Group V] [IsElementaryAbelian 2 V]
    (U : Subgroup V) : IsElementaryAbelian 2 U where
  toIsMulCommutative :=
    ⟨⟨fun x y => Subtype.ext
      (show (x : V) * (y : V) = (y : V) * (x : V) from
        (IsMulCommutative.is_comm (M := V)).comm x y)⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro z
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (z : V)

private theorem commutatorAction_restriction_faithful
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (K : Subgroup G) (hKodd : Nat.Coprime 2 (Nat.card K))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    let U : Subgroup V := commutatorAction K V
    letI : IsInvariant K V U := commutatorAction_isInvariant
    letI : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
    Function.Injective
      (Representation.ofElementaryAbelianAction
        (A := K) (G := U) (p := 2)).asGroupHom := by
  let U : Subgroup V := commutatorAction K V
  let hUinv : IsInvariant K V U := commutatorAction_isInvariant
  let : IsInvariant K V U := hUinv
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
  let : IsElementaryAbelian 2 U := hUelem
  let rho := Representation.ofElementaryAbelianAction
    (A := K) (G := U) (p := 2)
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro k hk
    have hrhok : rho k = 1 :=
      congrArg Units.val (MonoidHom.mem_ker.mp hk)
    have hkfixU (w : U) : k • w = w := by
      apply Additive.ofMul.injective
      have happ := LinearMap.congr_fun hrhok (Additive.ofMul w)
      simpa [rho] using happ
    obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    have hcop : Nat.Coprime (Nat.card K) (Nat.card V) := by
      rw [hm]
      exact hKodd.symm.pow_right m
    have hcompl :
        IsCompl (FixedPoints.subgroup K V) U :=
      isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := V) (A := K)
        (Group.isSolvable_of_comm fun x y =>
          (IsMulCommutative.is_comm (M := V)).comm x y)
        hcop (inferInstance : IsMulCommutative V)
    have hkfixV (w : V) : (k : G) • w = w := by
      have hwtop : w ∈ (FixedPoints.subgroup K V ⊔ U) := by
        rw [hcompl.sup_eq_top]
        exact Subgroup.mem_top w
      let hfixnorm : (FixedPoints.subgroup K V).Normal :=
        Subgroup.normal_of_isMulCommutative _
      let : (FixedPoints.subgroup K V).Normal := hfixnorm
      rcases Subgroup.mem_sup_of_normal_left.mp hwtop with
        ⟨c, hc, z, hz, hcz⟩
      have hkc : k • c = c :=
        (FixedPoints.mem_subgroup (M := K) (a := c)).1 hc k
      have hkc' : (k : G) • c = c := by
        simpa only [Subgroup.smul_def] using hkc
      have hkz : (k : G) • z = z :=
        congrArg Subtype.val (hkfixU ⟨z, hz⟩)
      rw [← hcz, smul_mul', hkc', hkz]
    have hkG : (k : G) ∈ fixingSubgroup G (Set.univ : Set V) :=
      (mem_fixingSubgroup_iff (M := G) (s := (Set.univ : Set V))).2
        (fun w _ => hkfixV w)
    rw [hfaith] at hkG
    simpa using hkG
  · exact bot_le

private theorem involution_extension_action_faithful
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [MulDistribMulAction G V]
    (F : Subgroup G) (hFnorm : F.Normal) (hFne : F ≠ ⊥)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hfaithF : fixingSubgroup F (Set.univ : Set V) = ⊥) :
    fixingSubgroup G (Set.univ : Set V) = ⊥ := by
  classical
  let rho : G →* MulAut V := MulDistribMulAction.toMulAut G V
  have hrhoF : Function.Injective (rho.comp F.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro f hf
      have hfix : f ∈ fixingSubgroup F (Set.univ : Set V) := by
        rw [mem_fixingSubgroup_iff]
        intro v _
        have hv := DFunLike.congr_fun (MonoidHom.mem_ker.mp hf) v
        change (f : G) • v = v
        simpa [rho] using hv
      rw [hfaithF] at hfix
      simpa using hfix
    · exact bot_le
  rw [fixingSubgroup_univ_eq_ker_toMulAut]
  change rho.ker = ⊥
  apply le_antisymm
  intro g hg
  have hgtop : g ∈ F ⊔ Subgroup.zpowers x := by
    rw [hgen]
    exact Subgroup.mem_top g
  let : F.Normal := hFnorm
  rcases Subgroup.mem_sup_of_normal_left.mp hgtop with
    ⟨f, hf, r, hr, hfr⟩
  by_cases hrone : r = 1
  · subst r
    have hgf : g = f := by simpa using hfr.symm
    have hrf : (rho.comp F.subtype) ⟨f, hf⟩ = 1 := by
      change rho f = 1
      rw [← hgf]
      exact MonoidHom.mem_ker.mp hg
    have : (⟨f, hf⟩ : F) = 1 := by
      apply hrhoF
      simpa using hrf
    simpa [hgf] using congrArg Subtype.val this
  · have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
    have hcardR : Nat.card (Subgroup.zpowers x) = 2 := by
      simpa [Nat.card_zpowers] using hxorder
    obtain ⟨z, hzne, hzuniq⟩ :=
      (Nat.card_eq_two_iff' (1 : Subgroup.zpowers x)).mp hcardR
    let rx : Subgroup.zpowers x := ⟨x, Subgroup.mem_zpowers x⟩
    have hrxne : rx ≠ 1 := by
      intro h
      exact hx.1 (congrArg Subtype.val h)
    have hre : r = x := by
      have hsub : (⟨r, hr⟩ : Subgroup.zpowers x) = rx :=
        (hzuniq ⟨r, hr⟩ (by simpa using hrone)).trans
        (hzuniq rx hrxne).symm
      exact congrArg Subtype.val hsub
    have hrhox : rho x = (rho f)⁻¹ := by
      have hprod : rho f * rho x = 1 := by
        calc
          rho f * rho x = rho (f * x) := (map_mul rho f x).symm
          _ = rho g := by rw [← hre, hfr]
          _ = 1 := MonoidHom.mem_ker.mp hg
      have hfEq : rho f = (rho x)⁻¹ := (mul_eq_one_iff_eq_inv).mp hprod
      rw [hfEq]
      simp
    have hordTwo : orderOf (rho x) ∣ 2 := by
      simpa [hxorder] using orderOf_map_dvd rho x
    have hordOdd : orderOf (rho x) ∣ Nat.card F := by
      rw [hrhox, orderOf_inv]
      have hfOrder : orderOf f ∣ Nat.card F := by
        simpa [Subgroup.orderOf_coe] using
          (orderOf_dvd_natCard (⟨f, hf⟩ : F))
      exact (orderOf_map_dvd rho f).trans hfOrder
    have hordOne : orderOf (rho x) = 1 :=
      Nat.eq_one_of_dvd_coprimes hFodd hordTwo hordOdd
    have hrhoxOne : rho x = 1 := orderOf_eq_one_iff.mp hordOne
    have hRmap : (Subgroup.zpowers x).map rho = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      simp [hrhoxOne]
    have hFmap : F.map rho = ⊥ := by
      calc
        F.map rho = (⁅F, Subgroup.zpowers x⁆).map rho := by rw [hcommFx]
        _ = ⁅F.map rho, (Subgroup.zpowers x).map rho⁆ :=
          Subgroup.map_commutator F (Subgroup.zpowers x) rho
        _ = ⊥ := by simp [hRmap]
    apply False.elim
    apply hFne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hry : rho y = 1 := by
      have hymap : rho y ∈ F.map rho := ⟨y, hy, rfl⟩
      rw [hFmap] at hymap
      simpa using hymap
    have hyone : (⟨y, hy⟩ : F) = 1 := by
      apply hrhoF
      change rho y = rho 1
      simpa using hry
    exact congrArg Subtype.val hyone
  exact bot_le

private theorem zpowers_normal_of_centered_and_inverted
    {G : Type u} [Group G]
    (F : Subgroup G) (hFnorm : F.Normal)
    (a x : G) (hx : IsInvolution x)
    (haZ : a ∈ (Subgroup.center F).map F.subtype)
    (hinv : x * a * x⁻¹ = a⁻¹)
    (hgen : F ⊔ Subgroup.zpowers x = ⊤) :
    (Subgroup.zpowers a).Normal := by
  classical
  let A : Subgroup G := Subgroup.zpowers a
  let R : Subgroup G := Subgroup.zpowers x
  obtain ⟨af, hafZ, hafval⟩ := Subgroup.mem_map.mp haZ
  have hFcommA : ∀ f : G, f ∈ F → ∀ z : G, z ∈ A → f * z = z * f := by
    intro f hf z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hfaF : (⟨f, hf⟩ : F) * af = af * ⟨f, hf⟩ :=
      (Subgroup.mem_center_iff.mp hafZ) ⟨f, hf⟩
    have hfa : Commute f a := by
      rw [← hafval]
      exact congrArg Subtype.val hfaF
    exact (hfa.zpow_right n).eq
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two hxorder
  have hxsq : x * x = 1 := by simpa [pow_two] using hx.2
  have hxforward : ∀ z : G, z ∈ A → x * z * x⁻¹ ∈ A := by
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, hinv]
    exact A.zpow_mem (A.inv_mem (Subgroup.mem_zpowers a)) n
  have hxnorm : x ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact hxforward z
    · intro hz
      have := hxforward (x * z * x⁻¹) hz
      have heq : x * (x * z * x⁻¹) * x⁻¹ = z := by
        rw [hxinv]
        calc
          x * (x * z * x) * x = (x * x) * z * (x * x) := by ac_rfl
          _ = z := by rw [hxsq]; simp
      rwa [heq] at this
  have hRnormA : R ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hxnorm
  refine ⟨?_⟩
  intro z hz g
  have hgtop : g ∈ F ⊔ R := by
    rw [show F ⊔ R = ⊤ by simpa [R] using hgen]
    exact Subgroup.mem_top g
  let : F.Normal := hFnorm
  rcases Subgroup.mem_sup_of_normal_left.mp hgtop with
    ⟨f, hf, r, hr, hfr⟩
  have hrconj : r * z * r⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp (hRnormA hr) z).mp hz
  have hfcomm := hFcommA f hf (r * z * r⁻¹) hrconj
  have heq : g * z * g⁻¹ = r * z * r⁻¹ := by
    rw [← hfr]
    simp only [mul_inv_rev]
    calc
      (f * r) * z * (r⁻¹ * f⁻¹) = f * (r * z * r⁻¹) * f⁻¹ := by
        simp [mul_assoc]
      _ = (r * z * r⁻¹) * f * f⁻¹ := by rw [hfcomm]
      _ = r * z * r⁻¹ := by simp
  rwa [heq]

private theorem quotient_involution_extension_data
    {G : Type u} [Group G] [Finite G]
    (F A : Subgroup G) (hFnorm : F.Normal) (hAnorm : A.Normal)
    (hAleF : A ≤ F) (hFne : F.map (QuotientGroup.mk' A) ≠ ⊥)
    (p : ℕ) [Fact p.Prime] (hFp : IsPGroup p F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F) :
    letI : A.Normal := hAnorm
    let q : G →* G ⧸ A := QuotientGroup.mk' A
    let Fbar : Subgroup (G ⧸ A) := F.map q
    let xbar : G ⧸ A := q x
    Fbar.Normal ∧ Fbar ≠ ⊥ ∧ IsPGroup p Fbar ∧
      Nat.Coprime 2 (Nat.card Fbar) ∧ IsInvolution xbar ∧
      Fbar ⊔ Subgroup.zpowers xbar = ⊤ ∧
      ⁅Fbar, Subgroup.zpowers xbar⁆ = Fbar := by
  classical
  let : A.Normal := hAnorm
  let q : G →* G ⧸ A := QuotientGroup.mk' A
  let Fbar : Subgroup (G ⧸ A) := F.map q
  let xbar : G ⧸ A := q x
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective A
  have hFbarNorm : Fbar.Normal := by
    dsimp [Fbar]
    exact hFnorm.map q hqsurj
  have hFbarP : IsPGroup p Fbar := by
    dsimp [Fbar]
    exact hFp.map q
  have hFbarOdd : Nat.Coprime 2 (Nat.card Fbar) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd F q) hFodd
  have hxbarSq : xbar ^ 2 = 1 := by
    dsimp [xbar, q]
    calc
      (x : G ⧸ A) ^ 2 = ((x ^ 2 : G) : G ⧸ A) := rfl
      _ = 1 := by rw [hx.2]; rfl
  have hxnotA : x ∉ A := by
    intro hxA
    have hxF : x ∈ F := hAleF hxA
    have hxOrderDvdF : orderOf x ∣ Nat.card F := by
      simpa [Subgroup.orderOf_coe] using
        (orderOf_dvd_natCard (⟨x, hxF⟩ : F))
    have hxOrderOne : orderOf x = 1 :=
      Nat.eq_one_of_dvd_coprimes hFodd (by simp [orderOf_eq_prime hx.2 hx.1]) hxOrderDvdF
    exact hx.1 (orderOf_eq_one_iff.mp hxOrderOne)
  have hxbarNe : xbar ≠ 1 := by
    intro h
    exact hxnotA (QuotientGroup.eq_one_iff x |>.mp h)
  have hxbar : IsInvolution xbar := ⟨hxbarNe, hxbarSq⟩
  have hgenbar : Fbar ⊔ Subgroup.zpowers xbar = ⊤ := by
    calc
      Fbar ⊔ Subgroup.zpowers xbar =
          F.map q ⊔ (Subgroup.zpowers x).map q := by
            rw [MonoidHom.map_zpowers]
      _ = (F ⊔ Subgroup.zpowers x).map q := (Subgroup.map_sup F _ q).symm
      _ = (⊤ : Subgroup G).map q := by rw [hgen]
      _ = ⊤ := Subgroup.map_top_of_surjective q hqsurj
  have hcommbar : ⁅Fbar, Subgroup.zpowers xbar⁆ = Fbar := by
    calc
      ⁅Fbar, Subgroup.zpowers xbar⁆ =
          ⁅F.map q, (Subgroup.zpowers x).map q⁆ := by
            rw [MonoidHom.map_zpowers]
      _ = (⁅F, Subgroup.zpowers x⁆).map q :=
        (Subgroup.map_commutator F (Subgroup.zpowers x) q).symm
      _ = Fbar := by rw [hcommFx]
  exact ⟨hFbarNorm, hFne, hFbarP, hFbarOdd, hxbar, hgenbar, hcommbar⟩

private theorem quotient_fixedPoint_action_faithful_of_kernel
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V]
    (F A : Subgroup G) (hAnorm : A.Normal)
    (hker : fixingSubgroup F (FixedPoints.subgroup A V : Set V) =
      A.subgroupOf F) :
    letI : A.Normal := hAnorm
    let q : G →* G ⧸ A := QuotientGroup.mk' A
    let C : Subgroup V := FixedPoints.subgroup A V
    let Fbar : Subgroup (G ⧸ A) := F.map q
    fixingSubgroup Fbar (Set.univ : Set C) = ⊥ := by
  classical
  let : A.Normal := hAnorm
  let q : G →* G ⧸ A := QuotientGroup.mk' A
  let C : Subgroup V := FixedPoints.subgroup A V
  let Fbar : Subgroup (G ⧸ A) := F.map q
  rw [Subgroup.eq_bot_iff_forall]
  intro fbar hfbarFix
  obtain ⟨f, hfF, hqf⟩ := Subgroup.mem_map.mp fbar.property
  have hfixf : (⟨f, hfF⟩ : F) ∈
      fixingSubgroup F (FixedPoints.subgroup A V : Set V) := by
    rw [mem_fixingSubgroup_iff]
    intro c hc
    let cC : FixedPoints.subgroup A V := ⟨c, hc⟩
    have hfixbar : fbar • cC = cC := by
      rw [mem_fixingSubgroup_iff] at hfbarFix
      exact hfbarFix cC (Set.mem_univ cC)
    have hfixq : (q f) • cC = cC := by
      rw [hqf]
      exact hfixbar
    change (f : G) • c = c
    calc
      (f : G) • c = (((q f) • cC : C) : V) := by rfl
      _ = c := congrArg Subtype.val hfixq
  have hfA : (⟨f, hfF⟩ : F) ∈ A.subgroupOf F := by
    rw [← hker]
    exact hfixf
  have hqfone : q f = 1 := by
    apply (QuotientGroup.eq_one_iff f).mpr
    exact hfA
  apply Subtype.ext
  calc
    (fbar : G ⧸ A) = q f := hqf.symm
    _ = 1 := hqfone
    _ = ((1 : Fbar) : G ⧸ A) := rfl

private theorem quotient_fixedPoint_commutatorAction_eq_top
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F A : Subgroup G) (hAnorm : A.Normal)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (hcommFV : commutatorAction F V = ⊤) :
    letI : A.Normal := hAnorm
    let q : G →* G ⧸ A := QuotientGroup.mk' A
    let C : Subgroup V := FixedPoints.subgroup A V
    letI : IsElementaryAbelian 2 C := elementaryAbelian_subgroup C
    let Fbar : Subgroup (G ⧸ A) := F.map q
    commutatorAction Fbar C = ⊤ := by
  classical
  let : A.Normal := hAnorm
  let q : G →* G ⧸ A := QuotientGroup.mk' A
  let C : Subgroup V := FixedPoints.subgroup A V
  let hCelem : IsElementaryAbelian 2 C := elementaryAbelian_subgroup C
  let : IsElementaryAbelian 2 C := hCelem
  let Fbar : Subgroup (G ⧸ A) := F.map q
  obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hcopFV : Nat.Coprime (Nat.card F) (Nat.card V) := by
    rw [hm]
    exact hFodd.symm.pow_right m
  have hcomplFV : IsCompl (FixedPoints.subgroup F V) (commutatorAction F V) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F)
      (Group.isSolvable_of_comm fun a b =>
        (IsMulCommutative.is_comm (M := V)).comm a b)
      hcopFV (inferInstance : IsMulCommutative V)
  have hfixedFV : FixedPoints.subgroup F V = ⊥ := by
    have := hcomplFV.inf_eq_bot
    rwa [hcommFV, inf_top_eq] at this
  have hfixedBar : FixedPoints.subgroup Fbar C = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    have hcF : (c : V) ∈ FixedPoints.subgroup F V := by
      rw [FixedPoints.mem_subgroup]
      intro f
      let fbar : Fbar :=
        ⟨q (f : G), ⟨(f : G), f.property, rfl⟩⟩
      have hcbar := (FixedPoints.mem_subgroup (M := Fbar) (a := c)).mp hc fbar
      change (f : G) • (c : V) = (c : V)
      exact congrArg Subtype.val hcbar
    rw [hfixedFV] at hcF
    apply Subtype.ext
    simpa using hcF
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 C).exists_card_eq
  have hFbarOdd : Nat.Coprime 2 (Nat.card Fbar) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd F q) hFodd
  have hcopBarC : Nat.Coprime (Nat.card Fbar) (Nat.card C) := by
    rw [hn]
    exact hFbarOdd.symm.pow_right n
  have hsup :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (G := C) (A := Fbar)
      (Group.isSolvable_of_comm fun a b =>
        (IsMulCommutative.is_comm (M := C)).comm a b)
      hcopBarC
  change FixedPoints.subgroup Fbar C ⊔ commutatorAction Fbar C = ⊤ at hsup
  change commutatorAction Fbar C = ⊤
  rwa [hfixedBar, bot_sup_eq] at hsup

private theorem quotient_fixedPoint_involution_index
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (A : Subgroup G) (hAnorm : A.Normal)
    (x : G) (hx : IsInvolution x)
    (hxbar : IsInvolution ((QuotientGroup.mk' A) x))
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V)) :
    letI : A.Normal := hAnorm
    let q : G →* G ⧸ A := QuotientGroup.mk' A
    let C : Subgroup V := FixedPoints.subgroup A V
    letI : IsElementaryAbelian 2 C := elementaryAbelian_subgroup C
    let xbar : G ⧸ A := q x
    Nat.card C ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers xbar) C) := by
  classical
  let : A.Normal := hAnorm
  let q : G →* G ⧸ A := QuotientGroup.mk' A
  let C : Subgroup V := FixedPoints.subgroup A V
  let hCelem : IsElementaryAbelian 2 C := elementaryAbelian_subgroup C
  let : IsElementaryAbelian 2 C := hCelem
  let xbar : G ⧸ A := q x
  let R : Subgroup G := Subgroup.zpowers x
  let Rbar : Subgroup (G ⧸ A) := Subgroup.zpowers xbar
  let D : Subgroup C := commutatorAction Rbar C
  let E : Subgroup V := commutatorAction R V
  have hmapDE : D.map C.subtype ≤ E := by
    rw [Subgroup.map_le_iff_le_comap]
    change commutatorAction Rbar C ≤ Subgroup.comap C.subtype E
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := Subgroup.comap C.subtype E)).2 ?_
    rintro d ⟨r, c, rfl⟩
    change ((c⁻¹ * (r • c) : C) : V) ∈ E
    have hxbarOrder : orderOf xbar = 2 := orderOf_eq_prime hxbar.2 hxbar.1
    have hcardRbar : Nat.card Rbar = 2 := by
      simpa [Rbar, Nat.card_zpowers] using hxbarOrder
    by_cases hr : r = 1
    · subst r
      simp
    · obtain ⟨z, hzne, hzuniq⟩ :=
        (Nat.card_eq_two_iff' (1 : Rbar)).mp hcardRbar
      let rxbar : Rbar := ⟨xbar, Subgroup.mem_zpowers xbar⟩
      have hrxbarne : rxbar ≠ 1 := by
        intro h
        exact hxbar.1 (congrArg Subtype.val h)
      have hre : r = rxbar := (hzuniq r hr).trans (hzuniq rxbar hrxbarne).symm
      rw [hre]
      change (c : V)⁻¹ * (x • (c : V)) ∈ E
      change (c : V)⁻¹ * (x • (c : V)) ∈ commutatorAction R V
      rw [commutatorAction_eq_closure]
      let rx : R := ⟨x, Subgroup.mem_zpowers x⟩
      exact Subgroup.subset_closure ⟨rx, (c : V), rfl⟩
  have hcardDmap : Nat.card D = Nat.card (D.map C.subtype) := by
    symm
    exact Subgroup.card_map_of_injective C.subtype_injective
  have hcardDE : Nat.card D ≤ Nat.card E := by
    rw [hcardDmap]
    let f : D.map C.subtype → E := fun d => ⟨d, hmapDE d.property⟩
    apply Nat.card_le_card_of_injective f
    intro d e hde
    apply Subtype.ext
    exact congrArg (fun z : E => (z : V)) hde
  have hcardEle : Nat.card E ≤ 4 := by
    simpa [E, R] using involution_commutator_card_le_four x hx hindex
  have hcardDle : Nat.card D ≤ 4 := hcardDE.trans hcardEle
  have hcardC := involution_card_eq_fixed_mul_commutator (V := C) xbar hxbar
  change Nat.card C ≤
    4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers xbar) C)
  rw [hcardC]
  rw [mul_comm 4]
  exact Nat.mul_le_mul_left _ (by simpa [D, Rbar] using hcardDle)

private theorem quotient_fixedPoint_measure_lt
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [MulDistribMulAction G V]
    (F A : Subgroup G) (hAnorm : A.Normal)
    (a : G) (haA : a ∈ A) (hane : a ≠ 1)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    letI : A.Normal := hAnorm
    let q : G →* G ⧸ A := QuotientGroup.mk' A
    let C : Subgroup V := FixedPoints.subgroup A V
    let Fbar : Subgroup (G ⧸ A) := F.map q
    Nat.card Fbar * Nat.card C < Nat.card F * Nat.card V := by
  classical
  let : A.Normal := hAnorm
  let q : G →* G ⧸ A := QuotientGroup.mk' A
  let C : Subgroup V := FixedPoints.subgroup A V
  let Fbar : Subgroup (G ⧸ A) := F.map q
  have hCneTop : C ≠ ⊤ := by
    intro hCtop
    have haFix : a ∈ fixingSubgroup G (Set.univ : Set V) := by
      rw [mem_fixingSubgroup_iff]
      intro v _
      have hvC : v ∈ C := by rw [hCtop]; exact Subgroup.mem_top v
      exact (FixedPoints.mem_subgroup (M := A) (a := v)).mp hvC ⟨a, haA⟩
    rw [hfaith] at haFix
    exact hane (by simpa using haFix)
  have hcardClt : Nat.card C < Nat.card V := by
    have hle : Nat.card C ≤ Nat.card V :=
      by simpa using
        (Subgroup.card_le_of_le (show C ≤ (⊤ : Subgroup V) from le_top))
    apply Nat.lt_of_le_of_ne hle
    intro heq
    exact hCneTop ((Subgroup.card_eq_iff_eq_top C).mp heq)
  have hcardFbarLe : Nat.card Fbar ≤ Nat.card F :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd F q)
  have hfirst : Nat.card Fbar * Nat.card C ≤ Nat.card F * Nat.card C :=
    Nat.mul_le_mul_right (Nat.card C) hcardFbarLe
  have hsecond : Nat.card F * Nat.card C < Nat.card F * Nat.card V :=
    Nat.mul_lt_mul_of_pos_left hcardClt Nat.card_pos
  exact hfirst.trans_lt hsecond

private theorem commutatorAction_isInvariant_of_normalizing_actor
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V]
    (B A : Subgroup G) (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    IsInvariant B V (commutatorAction A V) := by
  have hforward : ∀ g : B, ∀ v : V,
      v ∈ commutatorAction A V → g • v ∈ commutatorAction A V := by
    intro g v hv
    rw [commutatorAction_eq_closure] at hv ⊢
    refine Subgroup.closure_induction
      (p := fun w _ => g • w ∈ Subgroup.closure
        {d : V | ∃ a : A, ∃ v : V, d = v⁻¹ * a • v})
      (x := v) ?_ ?_ ?_ ?_ hv
    · rintro w ⟨a, z, rfl⟩
      let aga : A := ⟨(g : G) * (a : G) * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hBA g.property) (a : G)).mp a.property⟩
      refine Subgroup.subset_closure ⟨aga, g • z, ?_⟩
      change (g : G) • (z⁻¹ * (a : G) • z) =
        ((g : G) • z)⁻¹ * (aga : G) • ((g : G) • z)
      simp [aga, smul_mul', smul_inv', ← mul_smul, mul_assoc]
    · simp
    · intro y z _ _ hy hz
      simpa [smul_mul'] using
        (Subgroup.closure {d : V | ∃ a : A, ∃ v : V,
          d = v⁻¹ * a • v}).mul_mem hy hz
    · intro y _ hy
      simpa [smul_inv'] using
        (Subgroup.closure {d : V | ∃ a : A, ∃ v : V,
          d = v⁻¹ * a • v}).inv_mem hy
  constructor
  intro g v
  constructor
  · exact hforward g v
  · intro hgv
    have := hforward g⁻¹ (g • v) hgv
    simpa [inv_smul_smul] using this

private theorem commutatorAction_isInvariant_of_normal_actor
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V]
    (A : Subgroup G) (hAnorm : A.Normal) :
    IsInvariant G V (commutatorAction A V) := by
  have htop : IsInvariant (⊤ : Subgroup G) V (commutatorAction A V) := by
    apply commutatorAction_isInvariant_of_normalizing_actor (⊤ : Subgroup G) A
    let _ : A.Normal := hAnorm
    rw [Subgroup.normalizer_eq_top]
  constructor
  intro g v
  simpa only [Subgroup.smul_def] using
    (IsInvariant.invariant (A := (⊤ : Subgroup G)) (G := V)
      (H := commutatorAction A V) ⟨g, Subgroup.mem_top g⟩ v)

private theorem invariant_subgroup_eq_top_of_commutator_relations
    {G : Type u} {V : Type v} [Group G] [Group V]
    [IsMulCommutative V] [MulDistribMulAction G V]
    (F R : Subgroup G) (W : Subgroup V)
    (hWinv : IsInvariant G V W)
    (hcommRle : commutatorAction R V ≤ W)
    (hcommFR : ⁅F, R⁆ = F)
    (hcommFV : commutatorAction F V = ⊤) :
    W = ⊤ := by
  classical
  let hWnorm : W.Normal := Subgroup.normal_of_isMulCommutative W
  let _ : W.Normal := hWnorm
  let _ : IsInvariant G V W := hWinv
  let _ : MulDistribMulAction G (V ⧸ W) :=
    quotientMulDistribMulAction (A := G) (G := V) W hWinv
  let ρ : G →* MulAut (V ⧸ W) := MulDistribMulAction.toMulAut G (V ⧸ W)
  have hRmap : R.map ρ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro r hr
    rw [MonoidHom.mem_ker]
    ext qv
    refine QuotientGroup.induction_on qv ?_
    intro v
    change (((r • v : V) : V ⧸ W)) = (v : V ⧸ W)
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hgen : v⁻¹ * (r • v) ∈ commutatorAction R V := by
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨r, hr⟩, v, rfl⟩
    simpa [div_eq_mul_inv, mul_comm] using hcommRle hgen
  have hFmap : F.map ρ = ⊥ := by
    calc
      F.map ρ = (⁅F, R⁆).map ρ := by rw [hcommFR]
      _ = ⁅F.map ρ, R.map ρ⁆ := Subgroup.map_commutator F R ρ
      _ = ⊥ := by simp [hRmap]
  have hFker : F ≤ ρ.ker := (Subgroup.map_eq_bot_iff F).mp hFmap
  have hcommFle : commutatorAction F V ≤ W := by
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := W)).2 ?_
    rintro d ⟨f, v, rfl⟩
    have hρf : ρ (f : G) = 1 := MonoidHom.mem_ker.mp (hFker f.property)
    have hq : (((f : G) • v : V) : V ⧸ W) = (v : V ⧸ W) := by
      change ρ (f : G) (v : V ⧸ W) = (v : V ⧸ W)
      rw [hρf]
      rfl
    have hdiv : ((f : G) • v) / v ∈ W :=
      QuotientGroup.eq_iff_div_mem.mp hq
    rw [(IsMulCommutative.is_comm (M := V)).comm v⁻¹ (f • v)]
    change ((f : G) • v) * v⁻¹ ∈ W
    simpa [div_eq_mul_inv] using hdiv
  apply top_unique
  rw [← hcommFV]
  exact hcommFle

private theorem central_inverted_card_sixteen_commutatorAction_eq_top
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G)
    (a x : G) (ha : a ≠ 1) (haodd : Nat.Coprime 2 (orderOf a))
    (hx : IsInvolution x) (hinv : x * a * x⁻¹ = a⁻¹)
    (hAnorm : (Subgroup.zpowers a).Normal)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcommFV : commutatorAction F V = ⊤)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers a) V) = 2 ^ 4) :
    commutatorAction (Subgroup.zpowers a) V = ⊤ := by
  let A : Subgroup G := Subgroup.zpowers a
  let R : Subgroup G := Subgroup.zpowers x
  let W : Subgroup V := commutatorAction A V
  have hWinv : IsInvariant G V W := by
    simpa [A, W] using commutatorAction_isInvariant_of_normal_actor A hAnorm
  have hcommRle : commutatorAction R V ≤ W := by
    simpa [A, R, W] using
      invertedOddElement_cardSixteen_commutatorAction_le
        a x ha haodd hx hinv hindex hfaith hcard
  simpa [W] using
    invariant_subgroup_eq_top_of_commutator_relations
      F R W hWinv hcommRle (by simpa [R] using hcommFx) hcommFV

private theorem odd_subgroup_equiv_three_of_faithful_card_four
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFne : F ≠ ⊥)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (hcardV : Nat.card V = 4)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    Nonempty (F ≃* Multiplicative (ZMod 3)) := by
  let ρ := Representation.ofElementaryAbelianAction
    (A := F) (G := V) (p := 2)
  have hρinj : Function.Injective ρ.asGroupHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro f hf
      have hρf : ρ f = 1 := congrArg Units.val (MonoidHom.mem_ker.mp hf)
      have hfix : (f : G) ∈ fixingSubgroup G (Set.univ : Set V) := by
        rw [mem_fixingSubgroup_iff]
        intro v _
        change f • v = v
        apply Additive.ofMul.injective
        have happ := LinearMap.congr_fun hρf (Additive.ofMul v)
        simpa [ρ] using happ
      rw [hfaith] at hfix
      exact Subtype.ext (by simpa using hfix)
    · exact bot_le
  let n := Module.finrank (ZMod 2) (Additive V)
  have hn : n = 2 := by
    have hc := Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := Additive V)
    change Nat.card V = Nat.card (ZMod 2) ^ n at hc
    rw [hcardV, show Nat.card (ZMod 2) = 2 by norm_num] at hc
    change 2 ^ 2 = 2 ^ n at hc
    exact (Nat.pow_right_injective (by omega : 1 < 2) hc).symm
  let b : Module.Basis (Fin n) (ZMod 2) (Additive V) :=
    Module.finBasis (ZMod 2) (Additive V)
  let φ : F →* GL (Fin n) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
  have hφinj : Function.Injective φ :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hρinj
  have hdiv : Nat.card F ∣ Nat.card (GL (Fin n) (ZMod 2)) :=
    Subgroup.card_dvd_of_injective φ hφinj
  rw [hn, Matrix.card_GL_field] at hdiv
  norm_num [Fin.prod_univ_succ] at hdiv
  have hdiv3 : Nat.card F ∣ 3 := by
    apply hFodd.symm.dvd_of_dvd_mul_left
    simpa using hdiv
  have hcardF : Nat.card F = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv3 with h | h
    · exact False.elim (hFne ((Subgroup.card_eq_one (H := F)).mp h))
    · exact h
  let _ : Fact (Nat.Prime (Nat.card F)) := ⟨by simpa [hcardF] using Nat.prime_three⟩
  exact ⟨mulEquivOfPrimeCardEq hcardF (by norm_num)⟩

private abbrev SmallIndexConclusion
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (x : G) : Prop :=
  (Nat.card V = 4 ∧
      Nonempty (F ≃* Multiplicative (ZMod 3))) ∨
    (Nat.card V = 2 ^ 4 ∧
      Nat.card V =
        4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) ∧
      (Nonempty (F ≃* Multiplicative (ZMod 3)) ∨
       Nonempty (F ≃* Multiplicative (ZMod 5)) ∨
       Nonempty
         (F ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))))) ∨
    (Nat.card V = 2 ^ 6 ∧
      Nat.card V =
        4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) ∧
      ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥ ∧
      IsExtraspecial 3 F ∧ Nat.card F = 3 ^ 3)

private abbrev SmallIndexClassificationBelow (n : ℕ) : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V],
    ∀ (F : Subgroup G), F.Normal → F ≠ ⊥ →
    ∀ (p : ℕ), Fact p.Prime → IsPGroup p F →
    Nat.Coprime 2 (Nat.card F) →
    ∀ (x : G), IsInvolution x →
    F ⊔ Subgroup.zpowers x = ⊤ →
    ⁅F, Subgroup.zpowers x⁆ = F →
    commutatorAction F V = ⊤ →
    Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) →
    fixingSubgroup G (Set.univ : Set V) = ⊥ →
    Nat.card F * Nat.card V < n →
    SmallIndexConclusion (V := V) F x

private theorem card_four_quotient_conclusion_false
    {Q : Type u} {C : Type v} [Group Q] [Group C] [Finite C]
    [MulDistribMulAction Q C]
    {V : Type v} [Group V]
    (Fbar : Subgroup Q) (xbar : Q)
    (W : Subgroup V) (hcardW : Nat.card W = 4)
    (hcardProduct : Nat.card C * Nat.card W = Nat.card V)
    (hVne : Nat.card V ≠ 2 ^ 4)
    (hsharp : Nat.card C ≤
      2 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers xbar) C))
    (hrec : SmallIndexConclusion (V := C) Fbar xbar) : False := by
  rcases hrec with hsmall | hfour | hsix
  · exact hVne (by
      rw [← hcardProduct, hsmall.1, hcardW]
      norm_num)
  · have hpos : 0 <
        Nat.card (FixedPoints.subgroup (Subgroup.zpowers xbar) C) := Nat.card_pos
    omega
  · have hpos : 0 <
        Nat.card (FixedPoints.subgroup (Subgroup.zpowers xbar) C) := Nat.card_pos
    omega

private theorem central_element_eq_one_of_fixes_involution_commutator
    {G : Type u} {V : Type v} [Group G] [Group V]
    [IsMulCommutative V] [MulDistribMulAction G V]
    (F : Subgroup G) (z x : G)
    (hzZ : z ∈ (Subgroup.center F).map F.subtype)
    (hcenterComm :
      ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥)
    (hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcommFV : commutatorAction F V = ⊤)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hzfix : z ∈ fixingSubgroup G
      (commutatorAction (Subgroup.zpowers x) V : Set V)) :
    z = 1 := by
  classical
  let Z : Subgroup G := (Subgroup.center F).map F.subtype
  let R : Subgroup G := Subgroup.zpowers x
  let Cz : Subgroup G := Subgroup.centralizer ({z} : Set G)
  have hzCenterIn : z ∈ centerIn F := by
    simpa [centerIn_eq_map_center] using hzZ
  have hFleCz : F ≤ Cz := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact (Subgroup.mem_centralizer_iff.mp hzCenterIn.2 f hf).symm
  have hzCentR : z ∈ Subgroup.centralizer (R : Set G) := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by simpa [Z, R] using hcenterComm)) hzZ
  have hRleCz : R ≤ Cz := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact (Subgroup.mem_centralizer_iff.mp hzCentR r hr).symm
  have hGleCz : (⊤ : Subgroup G) ≤ Cz := by
    rw [← hgen]
    exact sup_le hFleCz hRleCz
  have hcommGz (g : G) : Commute g z := by
    have hgC : g ∈ Cz := hGleCz (Subgroup.mem_top g)
    exact (Subgroup.mem_centralizer_iff.mp hgC z (Set.mem_singleton z)).symm
  let A : Subgroup G := Subgroup.zpowers z
  let C : Subgroup V := FixedPoints.subgroup A V
  have hCinv : IsInvariant G V C := by
    have hforward : ∀ g : G, ∀ v : V, v ∈ C → g • v ∈ C := by
      intro g v hv
      rw [FixedPoints.mem_subgroup] at hv ⊢
      intro a
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.property
      have hga : Commute g (a : G) := by
        rw [← hn]
        exact (hcommGz g).zpow_right n
      change (a : G) • (g • v) = g • v
      calc
        (a : G) • (g • v) = ((a : G) * g) • v := by rw [mul_smul]
        _ = (g * (a : G)) • v := by rw [hga.eq]
        _ = g • ((a : G) • v) := by rw [mul_smul]
        _ = g • v := by
          change g • (a • v) = g • v
          rw [hv a]
    constructor
    intro g v
    constructor
    · exact hforward g v
    · intro hgv
      have := hforward g⁻¹ (g • v) hgv
      simpa [inv_smul_smul] using this
  have hRleC : commutatorAction R V ≤ C := by
    intro v hv
    rw [FixedPoints.mem_subgroup]
    intro a
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.property
    have hzv : z • v = v := by
      rw [mem_fixingSubgroup_iff] at hzfix
      exact hzfix v (by simpa [R] using hv)
    change (a : G) • v = v
    rw [← hn]
    exact MulAction.mem_fixedBy_zpow (MulAction.mem_fixedBy.mpr hzv) n
  have hCtop : C = ⊤ := by
    exact invariant_subgroup_eq_top_of_commutator_relations
      F R C hCinv hRleC (by simpa [R] using hcommFx) hcommFV
  have hzGlobal : z ∈ fixingSubgroup G (Set.univ : Set V) := by
    rw [mem_fixingSubgroup_iff]
    intro v _
    have hvC : v ∈ C := by rw [hCtop]; exact Subgroup.mem_top v
    have hvfix := (FixedPoints.mem_subgroup (M := A) (a := v)).mp hvC
      ⟨z, Subgroup.mem_zpowers z⟩
    simpa [A] using hvfix
  rw [hfaith] at hzGlobal
  simpa using hzGlobal

private theorem center_and_involution_commutator_card
    {p : ℕ} [Fact p.Prime]
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFne : F ≠ ⊥) (hFp : IsPGroup p F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcommFV : commutatorAction F V = ⊤)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcenterComm :
      ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥) :
    Nat.card (commutatorAction (Subgroup.zpowers x) V) = 4 ∧
      Nat.card (Subgroup.center F) = 3 := by
  classical
  let R : Subgroup G := Subgroup.zpowers x
  let U : Subgroup V := commutatorAction R V
  let Z : Subgroup G := (Subgroup.center F).map F.subtype
  have hUle : Nat.card U ≤ 4 := by
    simpa [U, R] using involution_commutator_card_le_four x hx hindex
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
  let _ : IsElementaryAbelian 2 U := hUelem
  have hZcentralR : Z ≤ Subgroup.centralizer (R : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by simpa [Z, R] using hcenterComm)
  have hZnormR : Z ≤ Subgroup.normalizer (R : Set G) :=
    hZcentralR.trans (Subgroup.centralizer_le_normalizer (R : Set G))
  let hUinv : IsInvariant Z V U := by
    simpa [U] using
      commutatorAction_isInvariant_of_normalizing_actor Z R hZnormR
  let _ : IsInvariant Z V U := hUinv
  have hUcard : Nat.card U = 4 := by
    by_contra hne
    have hUleTwo : Nat.card U ≤ 2 := by
      obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
      have hnle : n ≤ 2 := by
        apply (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp
        simpa [hn] using hUle
      interval_cases n
      · norm_num [hn]
      · norm_num [hn]
      · exact False.elim (hne (by norm_num [hn]))
    let _ : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).2 hFne
    let _ : Nontrivial (Subgroup.center F) := IsPGroup.center_nontrivial hFp
    obtain ⟨zc, hzcne⟩ := exists_ne (1 : Subgroup.center F)
    let z : Z := ⟨((zc : F) : G), ⟨(zc : F), zc.property, rfl⟩⟩
    have hfixU (u : U) : z • u = u := by
      have hcardCases : Nat.card U = 1 ∨ Nat.card U = 2 := by
        have hpos : 0 < Nat.card U := Nat.card_pos
        omega
      rcases hcardCases with hone | htwo
      · have hUbot : U = ⊥ := (Subgroup.card_eq_one (H := U)).mp hone
        have hu : (u : V) ∈ (⊥ : Subgroup V) := by simpa [hUbot] using u.property
        have huone : (u : V) = 1 := by simpa using hu
        have : u = 1 := Subtype.ext huone
        simp [this]
      · by_cases hu : u = 1
        · simp [hu]
        · have hzu : z • u ≠ 1 := by
            intro h
            apply hu
            apply smul_left_cancel z
            simpa using h
          obtain ⟨w, hwne, hwuniq⟩ :=
            (Nat.card_eq_two_iff' (1 : U)).mp htwo
          exact (hwuniq (z • u) hzu).trans (hwuniq u hu).symm
    have hzfix : (z : G) ∈ fixingSubgroup G (U : Set V) := by
      rw [mem_fixingSubgroup_iff]
      intro v hv
      have h := congrArg Subtype.val (hfixU ⟨v, hv⟩)
      change (((z • (⟨v, hv⟩ : U) : U) : V)) = v
      exact h
    have hzZ : (z : G) ∈ (Subgroup.center F).map F.subtype := z.property
    have hzone : (z : G) = 1 :=
      central_element_eq_one_of_fixes_involution_commutator
        F (z : G) x hzZ hcenterComm hgen hcommFx hcommFV hfaith
          (by simpa [U, R] using hzfix)
    apply hzcne
    apply Subtype.ext
    exact F.subtype_injective (by simpa [z, Z] using hzone)
  have hZodd : Nat.Coprime 2 (Nat.card Z) := by
    have hZF : Z ≤ F := by
      simpa [Z] using Subgroup.map_subtype_le (Subgroup.center F)
    exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hZF) hFodd
  have hZne : Z ≠ ⊥ := by
    let _ : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).2 hFne
    let _ : Nontrivial (Subgroup.center F) := IsPGroup.center_nontrivial hFp
    intro hZbot
    obtain ⟨zc, hzcne⟩ := exists_ne (1 : Subgroup.center F)
    have hzmem : (((zc : F) : G)) ∈ Z := ⟨(zc : F), zc.property, rfl⟩
    rw [hZbot] at hzmem
    apply hzcne
    apply Subtype.ext
    exact F.subtype_injective (by simpa using hzmem)
  have hZfaith : fixingSubgroup Z (Set.univ : Set U) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzfix : (z : G) ∈ fixingSubgroup G (U : Set V) := by
      rw [mem_fixingSubgroup_iff] at hz ⊢
      intro v hv
      have h := congrArg Subtype.val (hz ⟨v, hv⟩ (Set.mem_univ _))
      change (((z • (⟨v, hv⟩ : U) : U) : V)) = v
      exact h
    have hzOne : (z : G) = 1 :=
      central_element_eq_one_of_fixes_involution_commutator
        F (z : G) x z.property hcenterComm hgen hcommFx hcommFV hfaith
          (by simpa [U, R] using hzfix)
    exact Subtype.ext hzOne
  have hTopNe : (⊤ : Subgroup Z) ≠ ⊥ := by
    let _ : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).2 hZne
    exact top_ne_bot
  obtain ⟨e⟩ := odd_subgroup_equiv_three_of_faithful_card_four
    (G := Z) (V := U) (⊤ : Subgroup Z) hTopNe
      (by simpa using hZodd) hUcard hZfaith
  have hcardZ : Nat.card Z = 3 := by
    calc
      Nat.card Z = Nat.card (⊤ : Subgroup Z) := by simp
      _ = Nat.card (Multiplicative (ZMod 3)) := Nat.card_congr e.toEquiv
      _ = 3 := by norm_num
  have hmapCard : Nat.card Z = Nat.card (Subgroup.center F) := by
    simpa [Z] using
      (Subgroup.card_map_of_injective
        (K := Subgroup.center F) (f := F.subtype) F.subtype_injective)
  exact ⟨by simpa [U, R] using hUcard, hmapCard.symm.trans hcardZ⟩

private theorem order_three_faithful_card_four_commutatorAction_eq_top
    {A : Type u} {U : Type v} [Group A] [Group U]
    [Finite A] [Finite U] [IsElementaryAbelian 2 U]
    [MulDistribMulAction A U]
    (hcardA : Nat.card A = 3) (hcardU : Nat.card U = 4)
    (hfaith : fixingSubgroup A (Set.univ : Set U) = ⊥) :
    commutatorAction A U = ⊤ := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hcardA)
  let C : Subgroup U := FixedPoints.subgroup A U
  have hcardCle : Nat.card C ≤ 4 := by
    rw [← hcardU]
    simpa using Subgroup.card_le_of_le (show C ≤ (⊤ : Subgroup U) from le_top)
  have hmod : Nat.ModEq 3 4 (Nat.card C) := by
    have := hAp.card_modEq_card_fixedPoints U
    change Nat.ModEq 3 (Nat.card U)
      (Nat.card (FixedPoints.subgroup A U)) at this
    simpa [C, hcardU] using this
  have hcardC : Nat.card C = 1 ∨ Nat.card C = 4 := by
    have hpos : 0 < Nat.card C := Nat.card_pos
    have hneTwo : Nat.card C ≠ 2 := by
      intro h
      rw [h] at hmod
      norm_num at hmod
    have hneThree : Nat.card C ≠ 3 := by
      intro h
      rw [h] at hmod
      norm_num at hmod
    omega
  have hCneTop : C ≠ ⊤ := by
    intro hCtop
    have hAnontrivial : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcardA]
      norm_num)
    obtain ⟨a, hane⟩ := exists_ne (1 : A)
    have haFix : a ∈ fixingSubgroup A (Set.univ : Set U) := by
      rw [mem_fixingSubgroup_iff]
      intro u _
      have huC : u ∈ C := by rw [hCtop]; exact Subgroup.mem_top u
      exact (FixedPoints.mem_subgroup (M := A) (a := u)).mp huC a
    rw [hfaith] at haFix
    exact hane (by simpa using haFix)
  have hCbot : C = ⊥ := by
    apply (Subgroup.card_eq_one (H := C)).mp
    exact hcardC.resolve_right (fun h => hCneTop
      ((Subgroup.card_eq_iff_eq_top C).mp (by simpa [hcardU] using h)))
  have hcop : Nat.Coprime (Nat.card A) (Nat.card U) := by
    rw [hcardA, hcardU]
    norm_num
  have hsup := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := U) (A := A)
    (Group.isSolvable_of_comm fun a b =>
      (IsMulCommutative.is_comm (M := U)).comm a b) hcop
  change C ⊔ commutatorAction A U = ⊤ at hsup
  rwa [hCbot, bot_sup_eq] at hsup

private theorem center_map_commutatorAction_eq
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V]
    (F : Subgroup G) :
    commutatorAction ((Subgroup.center F).map F.subtype) V =
      commutatorAction (Subgroup.center F) V := by
  apply le_antisymm
  · rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro d ⟨z, v, rfl⟩
    obtain ⟨f, hf, hfeq⟩ := Subgroup.mem_map.mp z.property
    refine Subgroup.subset_closure ⟨⟨f, hf⟩, v, ?_⟩
    change v⁻¹ * (z : G) • v = v⁻¹ * ((f : F) : G) • v
    exact congrArg (fun g : G => v⁻¹ * g • v) hfeq.symm
  · rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro d ⟨z, v, rfl⟩
    let zmap : (Subgroup.center F).map F.subtype :=
      ⟨((z : F) : G), ⟨(z : F), z.property, rfl⟩⟩
    exact Subgroup.subset_closure ⟨zmap, v, rfl⟩

private theorem center_commutatorAction_eq_top_of_center_fixed
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFnorm : F.Normal)
    (x : G)
    (hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcommFV : commutatorAction F V = ⊤)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcenterComm :
      ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥)
    (hcardU : Nat.card (commutatorAction (Subgroup.zpowers x) V) = 4)
    (hcardZ : Nat.card (Subgroup.center F) = 3) :
    commutatorAction (Subgroup.center F) V = ⊤ := by
  classical
  let R : Subgroup G := Subgroup.zpowers x
  let U : Subgroup V := commutatorAction R V
  let Z : Subgroup G := (Subgroup.center F).map F.subtype
  let W : Subgroup V := commutatorAction Z V
  let hUelem : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
  let _ : IsElementaryAbelian 2 U := hUelem
  have hZcentralR : Z ≤ Subgroup.centralizer (R : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by simpa [Z, R] using hcenterComm)
  have hZnormR : Z ≤ Subgroup.normalizer (R : Set G) :=
    hZcentralR.trans (Subgroup.centralizer_le_normalizer (R : Set G))
  let hUinv : IsInvariant Z V U := by
    simpa [U] using
      commutatorAction_isInvariant_of_normalizing_actor Z R hZnormR
  let _ : IsInvariant Z V U := hUinv
  have hZfaith : fixingSubgroup Z (Set.univ : Set U) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzfix : (z : G) ∈ fixingSubgroup G (U : Set V) := by
      rw [mem_fixingSubgroup_iff] at hz ⊢
      intro v hv
      have h := congrArg Subtype.val (hz ⟨v, hv⟩ (Set.mem_univ _))
      change (((z • (⟨v, hv⟩ : U) : U) : V)) = v
      exact h
    have hzOne : (z : G) = 1 :=
      central_element_eq_one_of_fixes_involution_commutator
        F (z : G) x z.property hcenterComm hgen hcommFx hcommFV hfaith
          (by simpa [U, R] using hzfix)
    exact Subtype.ext hzOne
  have hcardZmap : Nat.card Z = 3 := by
    calc
      Nat.card Z = Nat.card (Subgroup.center F) := by
        simpa [Z] using
          (Subgroup.card_map_of_injective
            (K := Subgroup.center F) (f := F.subtype) F.subtype_injective)
      _ = 3 := hcardZ
  have hcommZU : commutatorAction Z U = ⊤ :=
    order_three_faithful_card_four_commutatorAction_eq_top
      hcardZmap (by simpa [U, R] using hcardU) hZfaith
  have hmaple : (commutatorAction Z U).map U.subtype ≤ W := by
    rw [Subgroup.map_le_iff_le_comap]
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro d ⟨z, u, rfl⟩
    change (u : V)⁻¹ * (z : G) • (u : V) ∈ commutatorAction Z V
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨z, (u : V), rfl⟩
  have hUleW : U ≤ W := by
    intro u hu
    have huTop : (⟨u, hu⟩ : U) ∈ (⊤ : Subgroup U) := Subgroup.mem_top _
    rw [← hcommZU] at huTop
    exact hmaple (Subgroup.mem_map_of_mem U.subtype huTop)
  have hZnorm : Z.Normal := by
    let _ : F.Normal := hFnorm
    let _ : (Subgroup.center F).Characteristic := Subgroup.centerCharacteristic
    dsimp [Z]
    infer_instance
  have hWinv : IsInvariant G V W := by
    simpa [W] using commutatorAction_isInvariant_of_normal_actor Z hZnorm
  have hWtop : W = ⊤ :=
    invariant_subgroup_eq_top_of_commutator_relations
      F R W hWinv (by simpa [U] using hUleW)
        (by simpa [R] using hcommFx) hcommFV
  rw [← center_map_commutatorAction_eq F]
  exact hWtop

private theorem actsTrivially_of_commuting_actor_trivial_on_commutator
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite V] [Nontrivial V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (A D : Subgroup G)
    (hcomm : ⁅A, D⁆ = ⊥)
    (hWinv : IsInvariant D V (commutatorAction A V))
    (htriv : letI : IsInvariant D V (commutatorAction A V) := hWinv
      ActsTrivially (A := D) (G := commutatorAction A V))
    (hDtop : commutatorAction D V = ⊤) :
    ActsTrivially (A := A) (G := V) := by
  classical
  let W : Subgroup V := commutatorAction A V
  let _ : IsInvariant D V W := by simpa [W] using hWinv
  have hADcomm : A ≤ Subgroup.centralizer (D : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro a v
  have hv : v ∈ commutatorAction D V := by rw [hDtop]; trivial
  rw [commutatorAction_eq_closure] at hv
  refine Subgroup.closure_induction
    (p := fun w _ => a • w = w) (x := v) ?_ ?_ ?_ ?_ hv
  · rintro w ⟨d, y, rfl⟩
    have had : (a : G) * (d : G) = (d : G) * (a : G) :=
      (Subgroup.mem_centralizer_iff.mp (hADcomm a.property)
        (d : G) d.property).symm
    have hyW : y⁻¹ * (a • y) ∈ W := by
      change y⁻¹ * (a • y) ∈ commutatorAction A V
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨a, y, rfl⟩
    have hdFix := htriv d (⟨y⁻¹ * (a • y), hyW⟩ : W)
    have hdFixV := congrArg Subtype.val hdFix
    change (d : G) • (y⁻¹ * (a • y)) = y⁻¹ * (a • y) at hdFixV
    simp only [smul_mul', smul_inv'] at hdFixV
    change (a : G) • (y⁻¹ * ((d : G) • y)) =
      y⁻¹ * ((d : G) • y)
    simp only [smul_mul', smul_inv']
    have hadAction : (a : G) • ((d : G) • y) =
        (d : G) • ((a : G) • y) := by
      simpa only [← mul_smul] using
        congrArg (fun g : G => g • y) had
    rw [hadAction]
    have hinvself (z : V) : z⁻¹ = z :=
      inv_eq_self_of_exponent_two IsElementaryAbelian.exponent_eq_prime z
    have hpow2 (z : V) : z * z = 1 := by
      calc
        z * z = z⁻¹ * z := congrArg (fun w : V => w * z) (hinvself z).symm
        _ = 1 := inv_mul_cancel z
    simp only [hinvself] at hdFixV ⊢
    calc
      (a • y) * (d • a • y) =
          ((d • y) * (d • y)) * ((a • y) * (d • a • y)) := by
            rw [hpow2, one_mul]
      _ = ((a • y) * (d • y)) * ((d • y) * (d • a • y)) := by
            ac_rfl
      _ = ((a • y) * (d • y)) * (y * (a • y)) :=
            congrArg (fun z : V => ((a • y) * (d • y)) * z) hdFixV
      _ = ((a • y) * (a • y)) * (y * (d • y)) := by ac_rfl
      _ = y * (d • y) := by rw [hpow2, one_mul]
  · simp
  · intro y z _ _ hy hz
    simp [smul_mul', hy, hz]
  · intro y _ hy
    simp [smul_inv', hy]

private theorem commutatorAction_subgroup_mono
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V]
    {A B : Subgroup G} (hAB : A ≤ B) :
    commutatorAction A V ≤ commutatorAction B V := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  refine Subgroup.closure_mono ?_
  rintro x ⟨a, w, rfl⟩
  exact ⟨⟨a, hAB a.property⟩, w, rfl⟩

private theorem isInvariant_of_subgroup_local
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V]
    (E Q : Subgroup G) (U : Subgroup V) [IsInvariant E V U]
    (hQE : Q ≤ E) : IsInvariant Q V U := by
  refine ⟨?_⟩
  intro q v
  exact IsInvariant.invariant (A := E) (G := V) (H := U)
    ⟨q, hQE q.property⟩ v

private theorem commutatorAction_subgroupOf_eq_local
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V]
    (H F : Subgroup G) (U : Subgroup V)
    [IsInvariant H V U] (hFH : F ≤ H) :
    let _ : IsInvariant F V U := isInvariant_of_subgroup_local H F U hFH
    commutatorAction (F.subgroupOf H) U = commutatorAction F U := by
  dsimp only
  let _ : IsInvariant F V U := isInvariant_of_subgroup_local H F U hFH
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a, u, rfl⟩
    let f : F := ⟨(a : H), a.property⟩
    exact ⟨f, u, rfl⟩
  · rintro ⟨f, u, rfl⟩
    let a : F.subgroupOf H := ⟨⟨f, hFH f.property⟩, f.property⟩
    exact ⟨a, u, rfl⟩

private theorem card_sup_le_mul_of_isMulCommutative
    {X : Type v} [Group X] [Finite X] (A B : Subgroup X)
    (hcomm : IsMulCommutative X) :
    Nat.card (↑(A ⊔ B : Subgroup X)) ≤ Nat.card A * Nat.card B := by
  let hAnorm : A.Normal :=
    ⟨fun a ha x => by
      rw [hcomm.is_comm.comm x a]
      simpa [mul_assoc] using ha⟩
  let _ : A.Normal := hAnorm
  let mu : A × B → ↑(A ⊔ B : Subgroup X) := fun x =>
    ⟨(x.1 : X) * (x.2 : X), Subgroup.mul_mem_sup x.1.property x.2.property⟩
  have hmu : Function.Surjective mu := by
    intro x
    rcases Subgroup.mem_sup_of_normal_left.mp x.property with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  simpa [Nat.card_prod] using Nat.card_le_card_of_surjective mu hmu

private theorem commutatorAction_sup_eq_sup
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V]
    (A B : Subgroup G) :
    commutatorAction (↑(A ⊔ B : Subgroup G)) V =
      commutatorAction A V ⊔ commutatorAction B V := by
  classical
  let U : Subgroup V := commutatorAction A V ⊔ commutatorAction B V
  let P : Subgroup G :=
    { carrier := {g : G | ∀ w : V, w⁻¹ * (g • w) ∈ U}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb w
        have hbmem := hb w
        have hamem := ha (b • w)
        have hmul :
            w⁻¹ * ((a * b) • w) =
              (w⁻¹ * (b • w)) * ((b • w)⁻¹ * (a • (b • w))) := by
          simp [smul_smul, mul_assoc]
        rw [hmul]
        exact U.mul_mem hbmem hamem
      inv_mem' := by
        intro a ha w
        have hmem := ha (a⁻¹ • w)
        have hinv :
            w⁻¹ * (a⁻¹ • w) =
              ((a⁻¹ • w)⁻¹ * (a • (a⁻¹ • w)))⁻¹ := by
          simp [smul_smul]
        rw [hinv]
        exact U.inv_mem hmem }
  have hAleP : A ≤ P := by
    intro a ha w
    apply (show commutatorAction A V ≤ U from le_sup_left)
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨a, ha⟩, w, rfl⟩
  have hBleP : B ≤ P := by
    intro b hb w
    apply (show commutatorAction B V ≤ U from le_sup_right)
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨b, hb⟩, w, rfl⟩
  apply le_antisymm
  · rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := U)).2 ?_
    rintro z ⟨g, w, rfl⟩
    exact (sup_le hAleP hBleP) g.property w
  · exact sup_le
      (commutatorAction_subgroup_mono (show A ≤ A ⊔ B from le_sup_left))
      (commutatorAction_subgroup_mono (show B ≤ A ⊔ B from le_sup_right))

private theorem card_le_sixty_four_of_card_sixteen_sup_and_common_four
    {V : Type v} [Group V] [Finite V] [IsMulCommutative V]
    (U A B : Subgroup V) (hUA : U ≤ A) (hUB : U ≤ B)
    (hcardU : Nat.card U = 4)
    (hcardA : Nat.card A = 2 ^ 4) (hcardB : Nat.card B = 2 ^ 4)
    (hABtop : A ⊔ B = ⊤) : Nat.card V ≤ 2 ^ 6 := by
  let hUnorm : U.Normal := Subgroup.normal_of_isMulCommutative U
  let _ : U.Normal := hUnorm
  let q : V →* V ⧸ U := QuotientGroup.mk' U
  have imageCard (K : Subgroup V) (hUK : U ≤ K)
      (hcardK : Nat.card K = 2 ^ 4) : Nat.card (K.map q) = 4 := by
    let f : K →* V ⧸ U := q.comp K.subtype
    have hker : f.ker = U.subgroupOf K := by
      ext k
      change q (k : V) = 1 ↔ (k : V) ∈ U
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    have hrange : f.range = K.map q := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨(k : V), k.property, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, hk⟩, rfl⟩
    have hcardKer : Nat.card f.ker = 4 := by
      rw [hker, natCard_subgroupOf_eq U K hUK, hcardU]
    have hcardProduct := f.ker.card_mul_index
    rw [Subgroup.index_ker, hcardKer, hrange, hcardK] at hcardProduct
    omega
  have hcardAbar : Nat.card (A.map q) = 4 := imageCard A hUA hcardA
  have hcardBbar : Nat.card (B.map q) = 4 := imageCard B hUB hcardB
  have hbarTop : A.map q ⊔ B.map q = ⊤ := by
    rw [← Subgroup.map_sup, hABtop]
    exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective U)
  have hquotientLe : Nat.card (V ⧸ U) ≤ 2 ^ 4 := by
    calc
      Nat.card (V ⧸ U) = Nat.card (⊤ : Subgroup (V ⧸ U)) := by simp
      _ = Nat.card (↑(A.map q ⊔ B.map q : Subgroup (V ⧸ U))) :=
        congrArg (fun K : Subgroup (V ⧸ U) => Nat.card K) hbarTop.symm
      _ ≤ Nat.card (A.map q) * Nat.card (B.map q) :=
        card_sup_le_mul_of_isMulCommutative _ _ inferInstance
      _ = 2 ^ 4 := by rw [hcardAbar, hcardBbar]; norm_num
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup U, hcardU]
  norm_num at hquotientLe ⊢
  omega

private theorem commutator_zpowers_inverted_eq_zpowers
    {G : Type u} [Group G] (a x : G)
    (haodd : Nat.Coprime 2 (orderOf a))
    (hx : IsInvolution x) (hinv : x * a * x⁻¹ = a⁻¹) :
    ⁅Subgroup.zpowers a, Subgroup.zpowers x⁆ = Subgroup.zpowers a := by
  classical
  let A : Subgroup G := Subgroup.zpowers a
  let R : Subgroup G := Subgroup.zpowers x
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two hxorder
  have hxx : x * x = 1 := by simpa [pow_two] using hx.2
  have hxNormForward (y : G) (hy : y ∈ A) : x * y * x⁻¹ ∈ A := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    have heq : x * y * x⁻¹ = (a⁻¹) ^ n := by
      calc
        x * y * x⁻¹ = x * a ^ n * x⁻¹ := by rw [hn]
        _ = (x * a * x⁻¹) ^ n := conj_zpow.symm
        _ = (a⁻¹) ^ n := by rw [hinv]
    rw [heq]
    exact A.zpow_mem (A.inv_mem (Subgroup.mem_zpowers a)) n
  have hxnormA : x ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hxNormForward y
    · intro hy
      have hback := hxNormForward (x * y * x⁻¹) hy
      have heq : x * (x * y * x⁻¹) * x⁻¹ = y := by
        rw [hxinv]
        calc
          x * (x * y * x) * x = (x * x) * y * (x * x) := by group
          _ = y := by rw [hxx, one_mul, mul_one]
      rwa [heq] at hback
  have hRnormA : R ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hxnormA
  apply le_antisymm
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp hRnormA
  · rw [Subgroup.zpowers_le]
    have hconjInv : x * a⁻¹ * x⁻¹ = a := by
      have h := congrArg Inv.inv hinv
      simpa [mul_inv_rev, mul_assoc] using h
    have haSq : ⁅a, x⁆ = a ^ 2 := by
      rw [commutatorElement_def, hxinv]
      calc
        a * x * a⁻¹ * x = a * (x * a⁻¹ * x) := by group
        _ = a * a := by rw [show x * a⁻¹ * x = a by simpa [hxinv] using hconjInv]
        _ = a ^ 2 := (pow_two a).symm
    have haSqMem : a ^ 2 ∈ ⁅A, R⁆ := by
      rw [← haSq]
      exact Subgroup.commutator_mem_commutator
        (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers x)
    have haMemPow : a ∈ Subgroup.zpowers (a ^ 2) := by
      rw [mem_zpowers_pow_iff]
      exact haodd
    exact (Subgroup.zpowers_le.mpr haSqMem) haMemPow

private theorem commutator_two_inverted_generators_eq
    {G : Type u} [Group G] (a b x : G)
    (haodd : Nat.Coprime 2 (orderOf a))
    (hbodd : Nat.Coprime 2 (orderOf b))
    (hx : IsInvolution x)
    (hainv : x * a * x⁻¹ = a⁻¹)
    (hbinv : x * b * x⁻¹ = b⁻¹) :
    ⁅Subgroup.zpowers a ⊔ Subgroup.zpowers b, Subgroup.zpowers x⁆ =
      Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  let A : Subgroup G := Subgroup.zpowers a
  let B : Subgroup G := Subgroup.zpowers b
  let R : Subgroup G := Subgroup.zpowers x
  have hcommA : ⁅A, R⁆ = A := by
    simpa [A, R] using
      commutator_zpowers_inverted_eq_zpowers a x haodd hx hainv
  have hcommB : ⁅B, R⁆ = B := by
    simpa [B, R] using
      commutator_zpowers_inverted_eq_zpowers b x hbodd hx hbinv
  have hRnormA : R ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (by rw [hcommA])
  have hRnormB : R ≤ Subgroup.normalizer (B : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (by rw [hcommB])
  have hRnormSup : R ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
    (show R ≤ Subgroup.normalizer (A : Set G) ⊓
        Subgroup.normalizer (B : Set G) from fun r hr => ⟨hRnormA hr, hRnormB hr⟩).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup A B)
  change ⁅A ⊔ B, R⁆ = A ⊔ B
  apply le_antisymm
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp hRnormSup
  · exact sup_le
      (calc
        A = ⁅A, R⁆ := hcommA.symm
        _ ≤ ⁅A ⊔ B, R⁆ := Subgroup.commutator_mono le_sup_left le_rfl)
      (calc
        B = ⁅B, R⁆ := hcommB.symm
        _ ≤ ⁅A ⊔ B, R⁆ := Subgroup.commutator_mono le_sup_right le_rfl)

private theorem recursive_call_on_proper_x_commutator_subgroup
    {n : ℕ}
    {p : ℕ} [Fact p.Prime]
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFp : IsPGroup p F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (recurse : SmallIndexClassificationBelow.{u, v} n)
    (F0 : Subgroup G) (hF0F : F0 ≤ F) (hF0ne : F0 ≠ ⊥)
    (hmeasure : Nat.card F0 * Nat.card V < n)
    (hcommF0x : ⁅F0, Subgroup.zpowers x⁆ = F0) :
    let R : Subgroup G := Subgroup.zpowers x
    let E : Subgroup G := F0 ⊔ R
    let V0 : Subgroup V := commutatorAction F0 V
    let hRnormF0 : R ≤ Subgroup.normalizer (F0 : Set G) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mpr (by
        rw [show ⁅F0, R⁆ = F0 by simpa [R] using hcommF0x])
    let hEnormF0 : E ≤ Subgroup.normalizer (F0 : Set G) :=
      sup_le Subgroup.le_normalizer hRnormF0
    let hV0inv : IsInvariant E V V0 := by
      simpa [V0] using
        commutatorAction_isInvariant_of_normalizing_actor E F0 hEnormF0
    letI : IsInvariant E V V0 := hV0inv
    let F0E : Subgroup E := F0.subgroupOf E
    let xE : E := ⟨x, (show R ≤ E from le_sup_right) (Subgroup.mem_zpowers x)⟩
    SmallIndexConclusion (V := V0) F0E xE := by
  classical
  let R : Subgroup G := Subgroup.zpowers x
  let E : Subgroup G := F0 ⊔ R
  let V0 : Subgroup V := commutatorAction F0 V
  have hF0E : F0 ≤ E := le_sup_left
  have hRE : R ≤ E := le_sup_right
  have hRnormF0 : R ≤ Subgroup.normalizer (F0 : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (by
      rw [show ⁅F0, R⁆ = F0 by simpa [R] using hcommF0x])
  have hEnormF0 : E ≤ Subgroup.normalizer (F0 : Set G) :=
    sup_le Subgroup.le_normalizer hRnormF0
  have hF0normalE : (F0.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hF0E).mpr hEnormF0
  let _ : (F0.subgroupOf E).Normal := hF0normalE
  let hV0inv : IsInvariant E V V0 := by
    simpa [V0] using
      commutatorAction_isInvariant_of_normalizing_actor E F0 hEnormF0
  let _ : IsInvariant E V V0 := hV0inv
  let hV0elem : IsElementaryAbelian 2 V0 := elementaryAbelian_subgroup V0
  let _ : IsElementaryAbelian 2 V0 := hV0elem
  let F0E : Subgroup E := F0.subgroupOf E
  let xE : E := ⟨x, show x ∈ E from hRE (Subgroup.mem_zpowers x)⟩
  have hcardF0E : Nat.card F0E = Nat.card F0 := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF0E)
  have hF0p : IsPGroup p F0 := by
    have hsub : IsPGroup p (F0.subgroupOf F) :=
      hFp.to_subgroup (F0.subgroupOf F)
    exact hsub.of_equiv (Subgroup.subgroupOfEquivOfLe hF0F)
  have hF0Ep : IsPGroup p F0E := by
    exact hF0p.of_equiv (Subgroup.subgroupOfEquivOfLe hF0E).symm
  have hF0Eodd : Nat.Coprime 2 (Nat.card F0E) := by
    rw [hcardF0E]
    exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hF0F) hFodd
  have hF0Ene : F0E ≠ ⊥ := by
    intro hbot
    have hmap := congrArg (Subgroup.map E.subtype) hbot
    rw [show F0E.map E.subtype = F0 by
      simpa [F0E] using Subgroup.map_subgroupOf_eq_of_le hF0E,
      Subgroup.map_bot] at hmap
    exact hF0ne hmap
  have hxE : IsInvolution xE := by
    refine ⟨?_, ?_⟩
    · intro heq
      exact hx.1 (congrArg Subtype.val heq)
    · apply Subtype.ext
      exact hx.2
  have hmapZpowers : (Subgroup.zpowers xE).map E.subtype = R := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le]
      exact Subgroup.mem_zpowers x
    · rw [Subgroup.zpowers_le]
      exact ⟨xE, Subgroup.mem_zpowers xE, rfl⟩
  have hgenE : F0E ⊔ Subgroup.zpowers xE = ⊤ := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_sup,
      show F0E.map E.subtype = F0 by
        simpa [F0E] using Subgroup.map_subgroupOf_eq_of_le hF0E,
      hmapZpowers]
    calc
      F0 ⊔ R = E := rfl
      _ = (⊤ : Subgroup E).map E.subtype := by
        symm
        ext g
        simp [E]
  have hcommE : ⁅F0E, Subgroup.zpowers xE⁆ = F0E := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_commutator,
      show F0E.map E.subtype = F0 by
        simpa [F0E] using Subgroup.map_subgroupOf_eq_of_le hF0E,
      hmapZpowers, show ⁅F0, R⁆ = F0 by simpa [R] using hcommF0x]
  let hF0inv : IsInvariant F0 V V0 :=
    isInvariant_of_subgroup_local E F0 V0 hF0E
  let _ : IsInvariant F0 V V0 := hF0inv
  have hF0copV : Nat.Coprime (Nat.card F0) (Nat.card V) := by
    obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hm]
    exact (Nat.Coprime.of_dvd_right
      (Subgroup.card_dvd_of_le hF0F) hFodd).symm.pow_right m
  have hcommV0 : commutatorAction F0E V0 = ⊤ := by
    apply (Subgroup.map_injective V0.subtype_injective)
    rw [commutatorAction_subgroupOf_eq_local E F0 V0 hF0E,
      commutatorAction_map_subtype_eq_commutatorAction₂,
      commutatorAction₂_eq_commutatorAction_of_coprime hF0copV]
    ext v
    simp [V0]
  have hF0faith : Function.Injective
      (Representation.ofElementaryAbelianAction
        (A := F0) (G := V0) (p := 2)).asGroupHom :=
    commutatorAction_restriction_faithful F0
      (Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hF0F) hFodd) hfaith
  have hfaithF0E : fixingSubgroup F0E (Set.univ : Set V0) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro f hf
    let f0 : F0 := ⟨((f : E) : G), f.property⟩
    have hf0one : f0 = 1 := by
      apply hF0faith
      apply Units.ext
      apply LinearMap.ext
      intro w
      change
        (Representation.ofElementaryAbelianAction
          (A := F0) (G := V0) (p := 2) f0) w =
        (Representation.ofElementaryAbelianAction
          (A := F0) (G := V0) (p := 2) 1) w
      rw [Representation.ofElementaryAbelianAction_apply,
        Representation.ofElementaryAbelianAction_apply]
      have hfix := (mem_fixingSubgroup_iff (M := F0E)
        (s := (Set.univ : Set V0))).mp hf (Additive.toMul w) (Set.mem_univ _)
      have hfix0 : f0 • Additive.toMul w = Additive.toMul w := by
        apply Subtype.ext
        exact congrArg Subtype.val hfix
      simpa only [one_smul] using congrArg Additive.ofMul hfix0
    apply Subtype.ext
    exact Subtype.ext (by
      simpa [f0, F0E] using congrArg Subtype.val hf0one)
  have hfaithE : fixingSubgroup E (Set.univ : Set V0) = ⊥ :=
    involution_extension_action_faithful
      F0E hF0normalE hF0Ene hF0Eodd xE hxE hgenE hcommE hfaithF0E
  have hRinvV0 : IsInvariant R V V0 :=
    isInvariant_of_subgroup_local E R V0 hRE
  let _ : IsInvariant R V V0 := hRinvV0
  have hcommXmapLe :
      (commutatorAction R V0).map V0.subtype ≤ commutatorAction R V := by
    rw [commutatorAction_eq_closure, MonoidHom.map_closure,
      commutatorAction_eq_closure]
    refine Subgroup.closure_mono ?_
    rintro z ⟨w, ⟨r, v, rfl⟩, rfl⟩
    exact ⟨r, (v : V), rfl⟩
  have hcommXcardLe : Nat.card (commutatorAction (Subgroup.zpowers xE) V0) ≤ 4 := by
    have hactorEq : R.subgroupOf E = Subgroup.zpowers xE := by
      apply Subgroup.map_injective E.subtype_injective
      rw [hmapZpowers]
      simpa using Subgroup.map_subgroupOf_eq_of_le hRE
    have hlocalEq : commutatorAction (Subgroup.zpowers xE) V0 =
        commutatorAction R V0 := by
      rw [← hactorEq, commutatorAction_subgroupOf_eq_local E R V0 hRE]
    rw [hlocalEq]
    calc
      Nat.card (commutatorAction R V0) =
          Nat.card ((commutatorAction R V0).map V0.subtype) := by
            symm
            exact Subgroup.card_map_of_injective V0.subtype_injective
      _ ≤ Nat.card (commutatorAction R V) := Subgroup.card_le_of_le hcommXmapLe
      _ ≤ 4 := by
        simpa [R] using involution_commutator_card_le_four x hx hindex
  have hindexV0 : Nat.card V0 ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers xE) V0) := by
    have hcardId := involution_card_eq_fixed_mul_commutator (V := V0) xE hxE
    rw [hcardId, mul_comm 4]
    exact Nat.mul_le_mul_left _ hcommXcardLe
  have hmeasureE : Nat.card F0E * Nat.card V0 < n := by
    rw [hcardF0E]
    have hV0le : Nat.card V0 ≤ Nat.card V :=
      Nat.card_le_card_of_injective V0.subtype V0.subtype_injective
    exact (Nat.mul_le_mul_left _ hV0le).trans_lt hmeasure
  exact recurse E V0 F0E hF0normalE hF0Ene p inferInstance hF0Ep hF0Eodd
    xE hxE hgenE hcommE hcommV0 hindexV0 hfaithE hmeasureE


private theorem inverted_element_commutatorAction_card_sixteen_of_center_fixed
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (a x : G) (haF : a ∈ F) (hane : a ≠ 1)
    (haodd : Nat.Coprime 2 (orderOf a))
    (hx : IsInvolution x) (hinv : x * a * x⁻¹ = a⁻¹)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcenterComm :
      ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥)
    (hcardZ : Nat.card (Subgroup.center F) = 3)
    (hcommZV : commutatorAction (Subgroup.center F) V = ⊤) :
    Nat.card (commutatorAction (Subgroup.zpowers a) V) = 2 ^ 4 := by
  classical
  let A : Subgroup G := Subgroup.zpowers a
  let D : Subgroup G := (Subgroup.center F).map F.subtype
  let Q : Subgroup G := Subgroup.zpowers x
  let W : Subgroup V := commutatorAction A V
  have hAF : A ≤ F := Subgroup.zpowers_le.mpr haF
  have hDcard : Nat.card D = 3 := by
    calc
      Nat.card D = Nat.card (Subgroup.center F) := by
        simpa [D] using
          (Subgroup.card_map_of_injective
            (K := Subgroup.center F) (f := F.subtype) F.subtype_injective)
      _ = 3 := hcardZ
  have hDtop : commutatorAction D V = ⊤ := by
    rw [center_map_commutatorAction_eq]
    exact hcommZV
  have hDcentralA : D ≤ Subgroup.centralizer (A : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hdcenter : (d : G) ∈ centerIn F := by
      simpa [D, centerIn_eq_map_center] using hd
    have hyF : (y : G) ∈ F := hAF hy
    exact Subgroup.mem_centralizer_iff.mp hdcenter.2 (y : G) hyF
  have hAcentralD : A ≤ Subgroup.centralizer (D : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_centralizer_iff.mp (hDcentralA hd) (y : G) hy).symm
  have hcommAD : ⁅A, D⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hAcentralD
  have hDnormA : D ≤ Subgroup.normalizer (A : Set G) :=
    hDcentralA.trans (Subgroup.centralizer_le_normalizer (A : Set G))
  let hDinvW : IsInvariant D V W := by
    simpa [W] using
      commutatorAction_isInvariant_of_normalizing_actor D A hDnormA
  let _ : IsInvariant D V W := hDinvW
  let hWelem : IsElementaryAbelian 2 W := elementaryAbelian_subgroup W
  let _ : IsElementaryAbelian 2 W := hWelem
  let _ : Nontrivial V := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply hane
    have haFix : a ∈ fixingSubgroup G (Set.univ : Set V) := by
      rw [mem_fixingSubgroup_iff]
      intro v _
      exact Subsingleton.elim _ _
    rw [hfaith] at haFix
    simpa using haFix
  have hDfaith : Function.Injective
      (Representation.ofElementaryAbelianAction
        (A := D) (G := W) (p := 2)).asGroupHom := by
    let rho := Representation.ofElementaryAbelianAction
      (A := D) (G := W) (p := 2)
    rw [← MonoidHom.ker_eq_bot_iff]
    let hprime : Fact (Nat.card D).Prime :=
      ⟨hDcard ▸ Nat.prime_three⟩
    let _ : Fact (Nat.card D).Prime := hprime
    rcases rho.asGroupHom.ker.eq_bot_or_eq_top_of_prime_card with hbot | htop
    · exact hbot
    · exfalso
      have hDtriv : ActsTrivially (A := D) (G := W) := by
        intro d w
        have hdker : d ∈ rho.asGroupHom.ker := by rw [htop]; trivial
        have hdrho : rho d = 1 :=
          congrArg Units.val (MonoidHom.mem_ker.mp hdker)
        apply Additive.ofMul.injective
        have happ := LinearMap.congr_fun hdrho (Additive.ofMul w)
        simpa [rho] using happ
      have hAtriv : ActsTrivially (A := A) (G := V) :=
        actsTrivially_of_commuting_actor_trivial_on_commutator
          A D hcommAD hDinvW hDtriv hDtop
      let aa : A := ⟨a, Subgroup.mem_zpowers a⟩
      have haFix : a ∈ fixingSubgroup G (Set.univ : Set V) := by
        rw [mem_fixingSubgroup_iff]
        intro v _
        simpa [aa] using hAtriv aa v
      rw [hfaith] at haFix
      exact hane (by simpa using haFix)
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two hxorder
  have hxx : x * x = 1 := by simpa [pow_two] using hx.2
  have hxNormForward (y : G) (hy : y ∈ A) : x * y * x⁻¹ ∈ A := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    have heq : x * y * x⁻¹ = (a⁻¹) ^ n := by
      calc
        x * y * x⁻¹ = x * a ^ n * x⁻¹ := by rw [hn]
        _ = (x * a * x⁻¹) ^ n := conj_zpow.symm
        _ = (a⁻¹) ^ n := by rw [hinv]
    rw [heq]
    exact A.zpow_mem (A.inv_mem (Subgroup.mem_zpowers a)) n
  have hxnormA : x ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hxNormForward y
    · intro hy
      have hback := hxNormForward (x * y * x⁻¹) hy
      have heq : x * (x * y * x⁻¹) * x⁻¹ = y := by
        rw [hxinv]
        calc
          x * (x * y * x) * x = (x * x) * y * (x * x) := by group
          _ = y := by rw [hxx, one_mul, mul_one]
      rwa [heq] at hback
  have hQnormA : Q ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hxnormA
  let hQinvW : IsInvariant Q V W := by
    simpa [W] using
      commutatorAction_isInvariant_of_normalizing_actor Q A hQnormA
  let _ : IsInvariant Q V W := hQinvW
  have hQcard : Nat.card Q = 2 := by
    simpa [Q, Nat.card_zpowers] using hxorder
  have hDQcentral : D ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by simpa [D, Q] using hcenterComm)
  have hactionsCommute : ∀ d : D, ∀ q : Q, ∀ w : W,
      d • (q • w) = q • (d • w) := by
    intro d q w
    apply Subtype.ext
    change (d : G) • ((q : G) • (w : V)) =
      (q : G) • ((d : G) • (w : V))
    rw [← mul_smul, ← mul_smul]
    exact congrArg (fun g : G => g • (w : V))
      (Subgroup.mem_centralizer_iff.mp (hDQcentral d.property)
        (q : G) q.property).symm
  rcases invertedOddElement_commutatorAction_card_eq_four_or_sixteen
      a x hane haodd hx hinv hindex hfaith with hfour | hsix
  · exfalso
    have hQtriv : ActsTrivially (A := Q) (G := W) :=
      Representation.actsTrivially_card_four_of_commuting_card_three_action
        (U := W) (D := D) (Q := Q) (by simpa [W, A] using hfour)
        hDcard hDfaith hQcard hactionsCommute
    let hAinvW : IsInvariant A V W := by
      simpa [W] using (commutatorAction_isInvariant (A := A) (G := V))
    let _ : IsInvariant A V W := hAinvW
    have hAodd : Nat.Coprime 2 (Nat.card A) := by
      simpa [A, Nat.card_zpowers] using haodd
    have hAfaith : Function.Injective
        (Representation.ofElementaryAbelianAction
          (A := A) (G := W) (p := 2)).asGroupHom :=
      commutatorAction_restriction_faithful A hAodd hfaith
    let aa : A := ⟨a, Subgroup.mem_zpowers a⟩
    let rx : Q := ⟨x, Subgroup.mem_zpowers x⟩
    have haaEq :
        (Representation.ofElementaryAbelianAction
          (A := A) (G := W) (p := 2)).asGroupHom aa =
        (Representation.ofElementaryAbelianAction
          (A := A) (G := W) (p := 2)).asGroupHom aa⁻¹ := by
      apply Units.ext
      apply LinearMap.ext
      intro w
      have hfixaw := hQtriv rx (aa • Additive.toMul w)
      have hfixw := hQtriv rx (Additive.toMul w)
      have hrel : x * a = a⁻¹ * x := by
        calc
          x * a = (x * a * x⁻¹) * x := by
            symm
            rw [mul_assoc, inv_mul_cancel, mul_one]
          _ = a⁻¹ * x := by rw [hinv]
      have hact : aa • Additive.toMul w = aa⁻¹ • Additive.toMul w := by
        calc
          aa • Additive.toMul w = rx • (aa • Additive.toMul w) := hfixaw.symm
          _ = aa⁻¹ • (rx • Additive.toMul w) := by
            apply Subtype.ext
            change x • (a • ((Additive.toMul w : W) : V)) =
              a⁻¹ • (x • ((Additive.toMul w : W) : V))
            simpa only [← mul_smul] using congrArg
              (fun g : G => g • ((Additive.toMul w : W) : V)) hrel
          _ = aa⁻¹ • Additive.toMul w := by rw [hfixw]
      change
        (Representation.ofElementaryAbelianAction
          (A := A) (G := W) (p := 2) aa) w =
        (Representation.ofElementaryAbelianAction
          (A := A) (G := W) (p := 2) aa⁻¹) w
      simpa only [Representation.ofElementaryAbelianAction_apply] using
        congrArg Additive.ofMul hact
    have haaInv : aa = aa⁻¹ := hAfaith haaEq
    have hainv : a = a⁻¹ := congrArg Subtype.val haaInv
    have hasq : a ^ 2 = 1 := by
      calc
        a ^ 2 = a * a := pow_two a
        _ = a⁻¹ * a := congrArg (fun z : G => z * a) hainv
        _ = 1 := inv_mul_cancel a
    have hadvdTwo : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hasq
    have haorderOne : orderOf a = 1 :=
      Nat.eq_one_of_dvd_coprimes haodd hadvdTwo dvd_rfl
    exact hane (orderOf_eq_one_iff.mp haorderOne)
  · exact hsix

private abbrev CenterFixedCases : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V],
    ∀ (F : Subgroup G), F.Normal → F ≠ ⊥ →
    ∀ (p : ℕ), Fact p.Prime → IsPGroup p F →
    Nat.Coprime 2 (Nat.card F) →
    ∀ (x : G), IsInvolution x →
    F ⊔ Subgroup.zpowers x = ⊤ →
    ⁅F, Subgroup.zpowers x⁆ = F →
    commutatorAction F V = ⊤ →
    Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) →
    fixingSubgroup G (Set.univ : Set V) = ⊥ →
    ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥ →
    SmallIndexClassificationBelow.{u, v} (Nat.card F * Nat.card V) →
    SmallIndexConclusion (V := V) F x

private theorem smallIndexClassification_of_centerFixedCases
    (terminal : CenterFixedCases.{u, v}) :
    ∀ (G : Type u) (V : Type v) [Group G] [Group V]
      [Finite G] [Finite V] [IsElementaryAbelian 2 V]
      [MulDistribMulAction G V],
      ∀ (F : Subgroup G), F.Normal → F ≠ ⊥ →
      ∀ (p : ℕ), Fact p.Prime → IsPGroup p F →
      Nat.Coprime 2 (Nat.card F) →
      ∀ (x : G), IsInvolution x →
      F ⊔ Subgroup.zpowers x = ⊤ →
      ⁅F, Subgroup.zpowers x⁆ = F →
      commutatorAction F V = ⊤ →
      Nat.card V ≤
        4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) →
      fixingSubgroup G (Set.univ : Set V) = ⊥ →
      SmallIndexConclusion (V := V) F x := by
  let P : ℕ → Prop := fun n =>
    ∀ (G : Type u) (V : Type v) [Group G] [Group V]
      [Finite G] [Finite V] [IsElementaryAbelian 2 V]
      [MulDistribMulAction G V],
      ∀ (F : Subgroup G), F.Normal → F ≠ ⊥ →
      ∀ (p : ℕ), Fact p.Prime → IsPGroup p F →
      Nat.Coprime 2 (Nat.card F) →
      ∀ (x : G), IsInvolution x →
      F ⊔ Subgroup.zpowers x = ⊤ →
      ⁅F, Subgroup.zpowers x⁆ = F →
      commutatorAction F V = ⊤ →
      Nat.card V ≤
        4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) →
      fixingSubgroup G (Set.univ : Set V) = ⊥ →
      Nat.card F * Nat.card V = n →
      SmallIndexConclusion (V := V) F x
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G V _ _ _ _ _ _ F hFnorm hFne p hpFact hFp hFodd x hx
        hgen hcommFx hcommFV hindex hfaith hmeasure
      let _ : Fact p.Prime := hpFact
      by_cases hV16 : Nat.card V = 2 ^ 4
      · right; left
        refine ⟨hV16, ?_⟩
        exact glFourTwo_involutionPGroup_classification F hFnorm hFne p hFp
          hFodd x hx hgen hcommFx hcommFV hV16 hindex hfaith
      · by_cases hcenter :
          ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥
        · exact terminal G V F hFnorm hFne p hpFact hFp hFodd x hx
            hgen hcommFx hcommFV hindex hfaith hcenter (by
              intro G' V' _ _ _ _ _ _ F' hF'norm hF'ne p' hp' hF'p
                hF'odd x' hx' hgen' hcomm' hcommV' hindex' hfaith' hlt
              exact ih (Nat.card F' * Nat.card V') (by
                simpa [hmeasure] using hlt)
                G' V' F' hF'norm hF'ne p' hp' hF'p hF'odd x' hx' hgen'
                  hcomm' hcommV' hindex' hfaith' rfl)
        · obtain ⟨a, ha, haZ, hinv⟩ :=
            exists_nontrivial_center_element_inverted_by_involution
              F hFnorm x hx hcenter
          have haF : a ∈ F := by
            have : a ∈ centerIn F := by
              simpa [centerIn_eq_map_center] using haZ
            exact this.1
          have haorder : orderOf a ∣ Nat.card F := by
            simpa [Subgroup.orderOf_coe] using
              (orderOf_dvd_natCard (⟨a, haF⟩ : F))
          have haodd : Nat.Coprime 2 (orderOf a) :=
            Nat.Coprime.of_dvd_right haorder hFodd
          have hsize :=
            invertedOddElement_commutatorAction_card_eq_four_or_sixteen
              a x ha haodd hx hinv hindex hfaith
          rcases hsize with hcard | hcard
          · let A : Subgroup G := Subgroup.zpowers a
            have hAF : A ≤ F := Subgroup.zpowers_le.mpr haF
            have hAnorm : A.Normal :=
              zpowers_normal_of_centered_and_inverted
                F hFnorm a x hx haZ hinv hgen
            let _ : A.Normal := hAnorm
            let q : G →* G ⧸ A := QuotientGroup.mk' A
            let C : Subgroup V := FixedPoints.subgroup A V
            let Fbar : Subgroup (G ⧸ A) := F.map q
            let xbar : G ⧸ A := q x
            by_cases hFbar : Fbar = ⊥
            · have hFA : F ≤ A := by
                have hker : F ≤ q.ker :=
                  (Subgroup.map_eq_bot_iff F).mp (by simpa [Fbar] using hFbar)
                simpa [q, QuotientGroup.ker_mk'] using hker
              have hFAeq : F = A := le_antisymm hFA hAF
              have hcardV : Nat.card V = 4 := by
                have htop : commutatorAction A V = ⊤ := by
                  rw [← hFAeq]
                  exact hcommFV
                calc
                  Nat.card V = Nat.card (⊤ : Subgroup V) := by simp
                  _ = Nat.card (commutatorAction A V) :=
                    congrArg (fun H : Subgroup V => Nat.card H) htop.symm
                  _ = 4 := by simpa [A] using hcard
              left
              exact ⟨hcardV,
                odd_subgroup_equiv_three_of_faithful_card_four
                  F hFne hFodd hcardV hfaith⟩
            · obtain ⟨hFbarNorm, -, hFbarP, hFbarOdd, hxbar,
                  hgenbar, hcommbar⟩ :=
                quotient_involution_extension_data F A hFnorm hAnorm hAF hFbar
                  p hFp hFodd x hx hgen hcommFx
              let hCelem : IsElementaryAbelian 2 C := elementaryAbelian_subgroup C
              let _ : IsElementaryAbelian 2 C := hCelem
              have hker :=
                centralOddPElement_cardFour_fixedPointKernel_eq_zpowers
                  F hFp hFodd ha
                    (by simpa [centerIn_eq_map_center] using haZ) hfaith
                    (by simpa [A] using hcard)
              have hfaithbar :
                  fixingSubgroup Fbar (Set.univ : Set C) = ⊥ :=
                quotient_fixedPoint_action_faithful_of_kernel
                  F A hAnorm (by simpa [A, C] using hker)
              have hfaithGbar :
                  fixingSubgroup (G ⧸ A) (Set.univ : Set C) = ⊥ :=
                involution_extension_action_faithful
                  Fbar hFbarNorm hFbar hFbarOdd xbar hxbar hgenbar hcommbar
                    hfaithbar
              have hcommC : commutatorAction Fbar C = ⊤ :=
                quotient_fixedPoint_commutatorAction_eq_top
                  F A hAnorm hFodd hcommFV
              have hsharp : Nat.card C ≤
                  2 * Nat.card
                    (FixedPoints.subgroup (Subgroup.zpowers xbar) C) :=
                invertedOddElement_cardFour_fixedPointQuotient_index_le_two
                  a x ha haodd hx hinv hAnorm
                    (by simpa [A] using hcard) hindex
              have hindexbar : Nat.card C ≤
                  4 * Nat.card
                    (FixedPoints.subgroup (Subgroup.zpowers xbar) C) := by
                omega
              have hlt : Nat.card Fbar * Nat.card C < n := by
                rw [← hmeasure]
                exact quotient_fixedPoint_measure_lt
                  F A hAnorm a (Subgroup.mem_zpowers a) ha hfaith
              have hrec : SmallIndexConclusion (V := C) Fbar xbar :=
                ih (Nat.card Fbar * Nat.card C) hlt
                  (G ⧸ A) C Fbar hFbarNorm hFbar p hpFact hFbarP
                    hFbarOdd xbar hxbar hgenbar hcommbar hcommC hindexbar
                    hfaithGbar rfl
              have hAdvdF : Nat.card A ∣ Nat.card F :=
                Subgroup.card_dvd_of_le hAF
              have hAodd : Nat.Coprime (Nat.card A) (Nat.card V) := by
                obtain ⟨m, hm⟩ :=
                  (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
                rw [hm]
                exact (Nat.Coprime.of_dvd_right hAdvdF hFodd).symm.pow_right m
              have hcomp : IsCompl C (commutatorAction A V) :=
                isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
                  (G := V) (A := A)
                  (Group.isSolvable_of_comm fun u v =>
                    (IsMulCommutative.is_comm (M := V)).comm u v)
                  hAodd (inferInstance : IsMulCommutative V)
              let hWnorm : (commutatorAction A V).Normal :=
                Subgroup.normal_of_isMulCommutative _
              let _ : (commutatorAction A V).Normal := hWnorm
              have hcomp' : C.IsComplement' (commutatorAction A V) := by
                apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hcomp.disjoint
                rw [← Subgroup.mul_normal C (commutatorAction A V), hcomp.sup_eq_top]
                rfl
              exact False.elim (card_four_quotient_conclusion_false
                Fbar xbar (commutatorAction A V) (by simpa [A] using hcard)
                  hcomp'.card_mul_card hV16 hsharp hrec)
          · have htop :=
              central_inverted_card_sixteen_commutatorAction_eq_top
                F a x ha haodd hx hinv
                  (zpowers_normal_of_centered_and_inverted
                    F hFnorm a x hx haZ hinv hgen)
                  hcommFx hcommFV hindex hfaith hcard
            apply False.elim
            apply hV16
            calc
              Nat.card V = Nat.card (⊤ : Subgroup V) := by simp
              _ = Nat.card (commutatorAction (Subgroup.zpowers a) V) :=
                congrArg (fun H : Subgroup V => Nat.card H) htop.symm
              _ = 2 ^ 4 := hcard
  intro G V _ _ _ _ _ _ F hFnorm hFne p hpFact hFp hFodd x hx
    hgen hcommFx hcommFV hindex hfaith
  exact hP (Nat.card F * Nat.card V) G V F hFnorm hFne p hpFact hFp
    hFodd x hx hgen hcommFx hcommFV hindex hfaith rfl

private theorem centerFixedCase_of_card_le_sixty_four
    {p : ℕ} [Fact p.Prime]
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFnorm : F.Normal) (hFne : F ≠ ⊥)
    (hFp : IsPGroup p F) (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcommFV : commutatorAction F V = ⊤)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcenterComm :
      ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥)
    (hcardUpper : Nat.card V ≤ 2 ^ 6) :
    SmallIndexConclusion (V := V) F x := by
  obtain ⟨hcardUx, hcardZ⟩ :=
    center_and_involution_commutator_card F hFne hFp hFodd x hx hgen
      hcommFx hcommFV hindex hfaith hcenterComm
  have hcommZV : commutatorAction (Subgroup.center F) V = ⊤ :=
    center_commutatorAction_eq_top_of_center_fixed
      F hFnorm x hgen hcommFx hcommFV hfaith hcenterComm hcardUx hcardZ
  obtain ⟨n, hn, hcardModule, _rho, _hrho⟩ :=
    centerThree_fixed_action_to_specialLinear
      F hFnorm hFne p hFp hFodd x hx hgen hcommFx hcardZ
        hcenterComm hcommZV hfaith
  have hlower : 2 ^ 6 ≤ Nat.card V := by
    rw [hcardModule]
    change 4 ^ 3 ≤ 4 ^ n
    exact Nat.pow_le_pow_right (by omega) hn
  have hcardV : Nat.card V = 2 ^ 6 := le_antisymm hcardUpper hlower
  have hfixed : Nat.card V =
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) := by
    have hmul := involution_card_eq_fixed_mul_commutator (V := V) x hx
    rw [hcardUx] at hmul
    simpa [mul_comm] using hmul
  obtain ⟨rho, hrho⟩ := centerThree_fixed_action_to_slThreeFour
    F hFnorm hFne p hFp hFodd x hx hgen hcommFx hcardZ hcenterComm
      hcommZV hcardV hfaith
  obtain ⟨hextra, hcardF⟩ :=
    slThreeFour_involutionPGroup_classification
      F x p hx hFnorm hFne hFodd hFp hgen hcommFx hcenterComm rho hrho
  right; right
  exact ⟨hcardV, hfixed, hcenterComm, hextra, hcardF⟩

private theorem exists_noncommuting_inverted_elements
    {G : Type u} [Group G]
    (F : Subgroup G) (x : G) (hx : IsInvolution x)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hFnoncomm : ¬ IsMulCommutative F) :
    ∃ a b : G, a ∈ F ∧ b ∈ F ∧
      x * a * x⁻¹ = a⁻¹ ∧ x * b * x⁻¹ = b⁻¹ ∧
      ¬ Commute a b := by
  classical
  let R : Subgroup G := Subgroup.zpowers x
  let S : Set G := {d : G | ∃ f ∈ F, ∃ r ∈ R, ⁅f, r⁆ = d}
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two hxorder
  have hcardR : Nat.card R = 2 := by
    simpa [R, Nat.card_zpowers] using hxorder
  have hgenerator (d : G) (hd : d ∈ S) :
      d ∈ F ∧ x * d * x⁻¹ = d⁻¹ := by
    obtain ⟨f, hf, r, hr, rfl⟩ := hd
    have hmem : ⁅f, r⁆ ∈ ⁅F, R⁆ :=
      Subgroup.commutator_mem_commutator hf hr
    have hmemF : ⁅f, r⁆ ∈ F := by simpa [R, hcommFx] using hmem
    refine ⟨hmemF, ?_⟩
    by_cases hrone : r = 1
    · subst r
      simp
    · obtain ⟨z, hzne, hzuniq⟩ :=
        (Nat.card_eq_two_iff' (1 : R)).mp hcardR
      let rx : R := ⟨x, Subgroup.mem_zpowers x⟩
      have hrxne : rx ≠ 1 := by
        intro h
        exact hx.1 (congrArg Subtype.val h)
      have hre : r = x := by
        have : (⟨r, hr⟩ : R) = rx :=
          (hzuniq ⟨r, hr⟩ (by simpa using hrone)).trans
            (hzuniq rx hrxne).symm
        exact congrArg Subtype.val this
      subst r
      simp [commutatorElement_def, hxinv, mul_assoc]
      simpa [pow_two] using hx.2
  by_contra hno
  have hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a haS b hbS
    obtain ⟨haF, hainv⟩ := hgenerator a haS
    obtain ⟨hbF, hbinv⟩ := hgenerator b hbS
    by_contra hncomm
    exact hno ⟨a, b, haF, hbF, hainv, hbinv, hncomm⟩
  let hClosureComm : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure hScomm
  have hclosure : Subgroup.closure S = F := by
    calc
      Subgroup.closure S = ⁅F, R⁆ := by rfl
      _ = F := by simpa [R] using hcommFx
  apply hFnoncomm
  refine ⟨⟨?_⟩⟩
  intro a b
  let ac : Subgroup.closure S := ⟨(a : G), by rw [hclosure]; exact a.property⟩
  let bc : Subgroup.closure S := ⟨(b : G), by rw [hclosure]; exact b.property⟩
  apply Subtype.ext
  exact congrArg (fun y : Subgroup.closure S => (y : G))
    (hClosureComm.is_comm.comm ac bc)

private theorem centerFixedCase_of_two_inverted_generators
    {p : ℕ} [Fact p.Prime]
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFnorm : F.Normal) (hFne : F ≠ ⊥)
    (hFp : IsPGroup p F) (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcommFV : commutatorAction F V = ⊤)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcenterComm :
      ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥)
    (a b : G) (haF : a ∈ F) (hbF : b ∈ F)
    (hainv : x * a * x⁻¹ = a⁻¹)
    (hbinv : x * b * x⁻¹ = b⁻¹)
    (hncomm : ¬ Commute a b)
    (hFgen : Subgroup.zpowers a ⊔ Subgroup.zpowers b = F) :
    SmallIndexConclusion (V := V) F x := by
  let A : Subgroup G := Subgroup.zpowers a
  let B : Subgroup G := Subgroup.zpowers b
  let R : Subgroup G := Subgroup.zpowers x
  let Wa : Subgroup V := commutatorAction A V
  let Wb : Subgroup V := commutatorAction B V
  let U : Subgroup V := commutatorAction R V
  have hane : a ≠ 1 := by
    intro ha
    subst a
    exact hncomm (by simp)
  have hbne : b ≠ 1 := by
    intro hb
    subst b
    exact hncomm (by simp)
  have haorder : orderOf a ∣ Nat.card F := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨a, haF⟩ : F))
  have hborder : orderOf b ∣ Nat.card F := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨b, hbF⟩ : F))
  have haodd : Nat.Coprime 2 (orderOf a) :=
    Nat.Coprime.of_dvd_right haorder hFodd
  have hbodd : Nat.Coprime 2 (orderOf b) :=
    Nat.Coprime.of_dvd_right hborder hFodd
  obtain ⟨hcardU, hcardZ⟩ :=
    center_and_involution_commutator_card F hFne hFp hFodd x hx hgen
      hcommFx hcommFV hindex hfaith hcenterComm
  have hcommZV : commutatorAction (Subgroup.center F) V = ⊤ :=
    center_commutatorAction_eq_top_of_center_fixed
      F hFnorm x hgen hcommFx hcommFV hfaith hcenterComm hcardU hcardZ
  have hcardWa : Nat.card Wa = 2 ^ 4 := by
    simpa [Wa, A] using
      inverted_element_commutatorAction_card_sixteen_of_center_fixed
        F a x haF hane haodd hx hainv hindex hfaith hcenterComm hcardZ hcommZV
  have hcardWb : Nat.card Wb = 2 ^ 4 := by
    simpa [Wb, B] using
      inverted_element_commutatorAction_card_sixteen_of_center_fixed
        F b x hbF hbne hbodd hx hbinv hindex hfaith hcenterComm hcardZ hcommZV
  have hUleWa : U ≤ Wa := by
    simpa [U, Wa, R, A] using
      invertedOddElement_cardSixteen_commutatorAction_le
        a x hane haodd hx hainv hindex hfaith (by simpa [Wa, A] using hcardWa)
  have hUleWb : U ≤ Wb := by
    simpa [U, Wb, R, B] using
      invertedOddElement_cardSixteen_commutatorAction_le
        b x hbne hbodd hx hbinv hindex hfaith (by simpa [Wb, B] using hcardWb)
  have hWaWbTop : Wa ⊔ Wb = ⊤ := by
    calc
      Wa ⊔ Wb = commutatorAction (↑(A ⊔ B : Subgroup G)) V := by
        simpa [Wa, Wb] using (commutatorAction_sup_eq_sup A B).symm
      _ = commutatorAction F V := by rw [show A ⊔ B = F by simpa [A, B] using hFgen]
      _ = ⊤ := hcommFV
  have hupper : Nat.card V ≤ 2 ^ 6 :=
    card_le_sixty_four_of_card_sixteen_sup_and_common_four
      U Wa Wb hUleWa hUleWb (by simpa [U, R] using hcardU)
        hcardWa hcardWb hWaWbTop
  exact centerFixedCase_of_card_le_sixty_four
    F hFnorm hFne hFp hFodd x hx hgen hcommFx hcommFV hindex hfaith
      hcenterComm hupper

private theorem isMulCommutative_of_mulEquiv
    {H K : Type*} [Group H] [Group K] [IsMulCommutative K]
    (e : H ≃* K) : IsMulCommutative H := by
  refine ⟨⟨fun x y => e.injective ?_⟩⟩
  simp only [map_mul]
  exact (IsMulCommutative.is_comm (M := K)).comm (e x) (e y)

private theorem map_center_subgroupOf_eq_centerIn
    {G : Type*} [Group G] (H K : Subgroup G) (hHK : H ≤ K) :
    (Subgroup.center (H.subgroupOf K)).map
        (K.subtype.comp (H.subgroupOf K).subtype) = centerIn H := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [centerIn]
    refine ⟨y.property, ?_⟩
    change ∀ h ∈ H, h * (y : G) = (y : G) * h
    intro h hh
    let h' : H.subgroupOf K := ⟨⟨h, hHK hh⟩, hh⟩
    exact congrArg (fun w : H.subgroupOf K => ((w : K) : G))
      (Subgroup.mem_center_iff.mp hy h')
  · intro hz
    have hzF : z ∈ H := (show z ∈ centerIn H from hz).1
    let z' : H.subgroupOf K := ⟨⟨z, hHK hzF⟩, hzF⟩
    refine ⟨z', ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro h
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp
      (show z ∈ centerIn H from hz).2 (h : G) h.property

/-- Coprime conjugation is idempotent on the relative commutator subgroup. -/
public theorem commutator_double_eq_self_of_coprime
    {G : Type*} [Group G]
    (P K : Subgroup G) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card K)) :
    ⁅⁅K, P⁆, P⁆ = ⁅K, P⁆ := by
  classical
  let _ : Subgroup.Normalizes P K := ⟨hPK⟩
  let _ : MulDistribMulAction P K :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P K hPK
  let C : Subgroup K := commutatorAction (A := P) (G := K)
  have hCmap : C.map K.subtype = ⁅K, P⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator K P hPK
  have hC2eq : commutatorAction₂ (A := P) (G := K) = C :=
    commutatorAction₂_eq_commutatorAction_of_coprime hcop
  have hXle : ⁅⁅K, P⁆, P⁆ ≤ ⁅K, P⁆ :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp
      (Subgroup.normalizer_commutator_ge_right K P)
  have hcomm₂_le :
      (commutatorAction₂ (A := P) (G := K)).map K.subtype ≤
        ⁅⁅K, P⁆, P⁆ := by
    let X : Set K := {k : K | ∃ a : P, ∃ c : K,
      c ∈ C ∧ k = c⁻¹ * (a • c)}
    calc
      (commutatorAction₂ (A := P) (G := K)).map K.subtype =
          (Subgroup.closure X).map K.subtype := by rfl
      _ = Subgroup.closure (K.subtype '' X) := by
        simpa using (MonoidHom.map_closure (f := K.subtype) X)
      _ ≤ ⁅⁅K, P⁆, P⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅K, P⁆, P⁆)).2 ?_
        rintro _ ⟨c, hc, rfl⟩
        rcases hc with ⟨a, k, hkC, rfl⟩
        have hkX : (k : G) ∈ ⁅K, P⁆ := by
          rw [← hCmap]
          exact Subgroup.mem_map.mpr ⟨k, hkC, rfl⟩
        have hgen : ⁅((k : K) : G)⁻¹, (a : G)⁆ ∈ ⁅⁅K, P⁆, P⁆ :=
          Subgroup.commutator_mem_commutator
            (Subgroup.inv_mem (H := ⁅K, P⁆) hkX) a.2
        simpa [commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          mul_assoc] using hgen
  apply le_antisymm hXle
  calc
    ⁅K, P⁆ = C.map K.subtype := hCmap.symm
    _ = (commutatorAction₂ (A := P) (G := K)).map K.subtype := by
      rw [hC2eq]
    _ ≤ ⁅⁅K, P⁆, P⁆ := hcomm₂_le

private theorem proper_inverted_pair_recursive_conclusion
    {p : ℕ} [Fact p.Prime]
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFp : IsPGroup p F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (a b : G) (haF : a ∈ F) (hbF : b ∈ F)
    (hainv : x * a * x⁻¹ = a⁻¹)
    (hbinv : x * b * x⁻¹ = b⁻¹)
    (hncomm : ¬ Commute a b)
    (recurse : SmallIndexClassificationBelow.{u, v}
      (Nat.card F * Nat.card V))
    (hproper : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≠ F) :
    let R : Subgroup G := Subgroup.zpowers x
    let F0 : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b
    let E : Subgroup G := F0 ⊔ R
    let V0 : Subgroup V := commutatorAction F0 V
    let hRnormF0 : R ≤ Subgroup.normalizer (F0 : Set G) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mpr (by
        rw [commutator_two_inverted_generators_eq a b x (by
          exact Nat.Coprime.of_dvd_right (by
            simpa [Subgroup.orderOf_coe] using
              (orderOf_dvd_natCard (⟨a, haF⟩ : F))) hFodd) (by
          exact Nat.Coprime.of_dvd_right (by
            simpa [Subgroup.orderOf_coe] using
              (orderOf_dvd_natCard (⟨b, hbF⟩ : F))) hFodd) hx hainv hbinv])
    let hEnormF0 : E ≤ Subgroup.normalizer (F0 : Set G) :=
      sup_le Subgroup.le_normalizer hRnormF0
    let hV0inv : IsInvariant E V V0 := by
      simpa [V0] using
        commutatorAction_isInvariant_of_normalizing_actor E F0 hEnormF0
    letI : IsInvariant E V V0 := hV0inv
    let F0E : Subgroup E := F0.subgroupOf E
    let xE : E := ⟨x, (show R ≤ E from le_sup_right) (Subgroup.mem_zpowers x)⟩
    Nat.card V0 = 2 ^ 6 ∧
      ⁅(Subgroup.center F0E).map F0E.subtype, Subgroup.zpowers xE⁆ = ⊥ ∧
      IsExtraspecial 3 F0E ∧ Nat.card F0E = 3 ^ 3 := by
  classical
  let R : Subgroup G := Subgroup.zpowers x
  let F0 : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  let E : Subgroup G := F0 ⊔ R
  let V0 : Subgroup V := commutatorAction F0 V
  have haF0 : a ∈ F0 :=
    (show Subgroup.zpowers a ≤ F0 from le_sup_left) (Subgroup.mem_zpowers a)
  have hbF0 : b ∈ F0 :=
    (show Subgroup.zpowers b ≤ F0 from le_sup_right) (Subgroup.mem_zpowers b)
  have hF0F : F0 ≤ F := sup_le (Subgroup.zpowers_le.mpr haF) (Subgroup.zpowers_le.mpr hbF)
  have hF0noncomm : ¬ IsMulCommutative F0 := by
    intro hcomm
    let aa : F0 := ⟨a, haF0⟩
    let bb : F0 := ⟨b, hbF0⟩
    apply hncomm
    exact congrArg (fun z : F0 => (z : G)) ((hcomm.is_comm).comm aa bb)
  have hF0ne : F0 ≠ ⊥ := by
    intro hbot
    apply hF0noncomm
    rw [hbot]
    infer_instance
  have hcardF0lt : Nat.card F0 < Nat.card F := by
    apply Nat.lt_of_le_of_ne (Subgroup.card_le_of_le hF0F)
    intro heq
    apply hproper
    change F0 = F
    exact Subgroup.eq_of_le_of_card_ge hF0F (by omega)
  have haodd : Nat.Coprime 2 (orderOf a) :=
    Nat.Coprime.of_dvd_right (by
      simpa [Subgroup.orderOf_coe] using
        (orderOf_dvd_natCard (⟨a, haF⟩ : F))) hFodd
  have hbodd : Nat.Coprime 2 (orderOf b) :=
    Nat.Coprime.of_dvd_right (by
      simpa [Subgroup.orderOf_coe] using
        (orderOf_dvd_natCard (⟨b, hbF⟩ : F))) hFodd
  have hcommF0x : ⁅F0, R⁆ = F0 := by
    simpa [F0, R] using
      commutator_two_inverted_generators_eq a b x haodd hbodd hx hainv hbinv
  have hRnormF0 : R ≤ Subgroup.normalizer (F0 : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (by rw [hcommF0x])
  have hEnormF0 : E ≤ Subgroup.normalizer (F0 : Set G) :=
    sup_le Subgroup.le_normalizer hRnormF0
  have hF0leE : F0 ≤ E := le_sup_left
  let hV0inv : IsInvariant E V V0 := by
    simpa [V0] using
      commutatorAction_isInvariant_of_normalizing_actor E F0 hEnormF0
  let _ : IsInvariant E V V0 := hV0inv
  let hV0elem : IsElementaryAbelian 2 V0 := elementaryAbelian_subgroup V0
  let _ : IsElementaryAbelian 2 V0 := hV0elem
  let F0E : Subgroup E := F0.subgroupOf E
  let xE : E := ⟨x, (show R ≤ E from le_sup_right) (Subgroup.mem_zpowers x)⟩
  have hrec : SmallIndexConclusion (V := V0) F0E xE :=
    recursive_call_on_proper_x_commutator_subgroup
      F hFp hFodd x hx hfaith hindex recurse F0 hF0F hF0ne
        (Nat.mul_lt_mul_of_pos_right hcardF0lt Nat.card_pos)
        (by simpa [R] using hcommF0x)
  have hF0Enoncomm : ¬ IsMulCommutative F0E := by
    intro hcomm
    let aa : F0E := ⟨⟨a, hF0leE haF0⟩, haF0⟩
    let bb : F0E := ⟨⟨b, hF0leE hbF0⟩, hbF0⟩
    apply hncomm
    exact congrArg (fun z : F0E => (((z : E) : G))) ((hcomm.is_comm).comm aa bb)
  rcases hrec with hsmall | hsmall | hlarge
  · exact False.elim (hF0Enoncomm
      (isMulCommutative_of_mulEquiv hsmall.2.some))
  · rcases hsmall.2.2 with hthree | hfive | hnine
    · exact False.elim (hF0Enoncomm
        (isMulCommutative_of_mulEquiv hthree.some))
    · exact False.elim (hF0Enoncomm
        (isMulCommutative_of_mulEquiv hfive.some))
    · exact False.elim (hF0Enoncomm
        (isMulCommutative_of_mulEquiv hnine.some))
  · exact ⟨hlarge.1, hlarge.2.2.1, hlarge.2.2.2.1, hlarge.2.2.2.2⟩

private theorem proper_inverted_pair_center_data
    {p : ℕ} [Fact p.Prime]
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFp : IsPGroup p F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (a b : G) (haF : a ∈ F) (hbF : b ∈ F)
    (hainv : x * a * x⁻¹ = a⁻¹)
    (hbinv : x * b * x⁻¹ = b⁻¹)
    (hncomm : ¬ Commute a b)
    (recurse : SmallIndexClassificationBelow.{u, v}
      (Nat.card F * Nat.card V))
    (hproper : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≠ F) :
    let R : Subgroup G := Subgroup.zpowers x
    let F0 : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b
    let V0 : Subgroup V := commutatorAction F0 V
    Nat.card V0 = 2 ^ 6 ∧ Nat.card F0 = 3 ^ 3 ∧
      Nat.card (centerIn F0) = 3 ∧ ⁅centerIn F0, R⁆ = ⊥ := by
  classical
  let R : Subgroup G := Subgroup.zpowers x
  let F0 : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  let E : Subgroup G := F0 ⊔ R
  let V0 : Subgroup V := commutatorAction F0 V
  have hF0leE : F0 ≤ E := le_sup_left
  have hRleE : R ≤ E := le_sup_right
  let F0E : Subgroup E := F0.subgroupOf E
  let xE : E := ⟨x, hRleE (Subgroup.mem_zpowers x)⟩
  obtain ⟨hcardV0, hcenterComm, hextra, hcardF0E⟩ :=
    proper_inverted_pair_recursive_conclusion
      F hFp hFodd x hx hindex hfaith a b haF hbF hainv hbinv hncomm
        recurse hproper
  have hcardF0 : Nat.card F0 = 3 ^ 3 := by
    rw [← hcardF0E]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF0leE).toEquiv.symm
  let i0 : F0E →* G := E.subtype.comp F0E.subtype
  have hi0 : Function.Injective i0 :=
    E.subtype_injective.comp F0E.subtype_injective
  have hcenterEq : (Subgroup.center F0E).map i0 = centerIn F0 := by
    simpa [i0, F0E] using map_center_subgroupOf_eq_centerIn F0 E hF0leE
  have hcardZ0 : Nat.card (centerIn F0) = 3 := by
    rw [← hcenterEq, Subgroup.card_map_of_injective hi0]
    let _ : IsExtraspecial 3 F0E := hextra
    exact IsExtraspecial.center_order_p 3 F0E
  have hmapX : (Subgroup.zpowers xE).map E.subtype = R := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le]
      exact Subgroup.mem_zpowers x
    · rw [Subgroup.zpowers_le]
      exact ⟨xE, Subgroup.mem_zpowers xE, rfl⟩
  have hcenterCommG : ⁅centerIn F0, R⁆ = ⊥ := by
    have hmap := congrArg (Subgroup.map E.subtype) hcenterComm
    rw [Subgroup.map_commutator, Subgroup.map_map, hmapX,
      show (Subgroup.center F0E).map (E.subtype.comp F0E.subtype) =
          centerIn F0 by simpa [F0E] using hcenterEq,
      Subgroup.map_bot] at hmap
    exact hmap
  exact ⟨hcardV0, hcardF0, hcardZ0, hcenterCommG⟩

private theorem proper_commutatorAction_ne_top_of_center_fixed
    {p : ℕ} [Fact p.Prime]
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFnorm : F.Normal) (hFne : F ≠ ⊥)
    (hFp : IsPGroup p F) (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcommFV : commutatorAction F V = ⊤)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcenterComm :
      ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥)
    (hFnoncomm : ¬ IsMulCommutative F)
    (F0 : Subgroup G) (hF0F : F0 ≤ F) (hF0proper : F0 ≠ F)
    (hcardF0 : Nat.card F0 = 3 ^ 3)
    (hcardV0 : Nat.card (commutatorAction F0 V) = 2 ^ 6) :
    commutatorAction F0 V ≠ ⊤ := by
  intro hV0top
  have hcardV : Nat.card V = 2 ^ 6 := by
    calc
      Nat.card V = Nat.card (⊤ : Subgroup V) := by simp
      _ = Nat.card (commutatorAction F0 V) := by rw [hV0top]
      _ = 2 ^ 6 := hcardV0
  have hconcl := centerFixedCase_of_card_le_sixty_four
    F hFnorm hFne hFp hFodd x hx hgen hcommFx hcommFV hindex hfaith
      hcenterComm (by omega)
  have hcardF : Nat.card F = 3 ^ 3 := by
    rcases hconcl with hsmall | hsmall | hlarge
    · exact False.elim (hFnoncomm
        (isMulCommutative_of_mulEquiv hsmall.2.some))
    · rcases hsmall.2.2 with hthree | hfive | hnine
      · exact False.elim (hFnoncomm
          (isMulCommutative_of_mulEquiv hthree.some))
      · exact False.elim (hFnoncomm
          (isMulCommutative_of_mulEquiv hfive.some))
      · exact False.elim (hFnoncomm
          (isMulCommutative_of_mulEquiv hnine.some))
    · exact hlarge.2.2.2.2
  exact hF0proper (Subgroup.eq_of_le_of_card_ge hF0F (by
    rw [hcardF0, hcardF]))

private theorem center_centralizer_proper_of_proper_local_action
    {p : ℕ} [Fact p.Prime]
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFnorm : F.Normal) (hFne : F ≠ ⊥)
    (hFp : IsPGroup p F) (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcommFV : commutatorAction F V = ⊤)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcenterComm :
      ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥)
    (F0 : Subgroup G) (hF0F : F0 ≤ F)
    (hcardZ0 : Nat.card (centerIn F0) = 3)
    (hV0proper : commutatorAction F0 V ≠ ⊤) :
    let F1 : Subgroup G := F ⊓ Subgroup.centralizer (centerIn F0 : Set G)
    F0 ≤ F1 ∧ F1 < F := by
  classical
  let Z0 : Subgroup G := centerIn F0
  let F1 : Subgroup G := F ⊓ Subgroup.centralizer (Z0 : Set G)
  have hF0leC : F0 ≤ Subgroup.centralizer (Z0 : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp
      (show z ∈ centerIn F0 from hz).2 f hf).symm
  have hF0F1 : F0 ≤ F1 := fun f hf => ⟨hF0F hf, hF0leC hf⟩
  have hF1F : F1 ≤ F := inf_le_left
  refine ⟨hF0F1, lt_of_le_of_ne hF1F ?_⟩
  intro hF1eq
  have hF1eq' : F1 = F := by simpa [F1, Z0] using hF1eq
  have hFleC : F ≤ Subgroup.centralizer (Z0 : Set G) := by
    intro f hf
    exact (show f ∈ F1 by rw [hF1eq']; exact hf).2
  have hZ0leZF : Z0 ≤ centerIn F := by
    intro z hz
    refine ⟨hF0F hz.1, ?_⟩
    change ∀ f ∈ F, f * z = z * f
    intro f hf
    exact (Subgroup.mem_centralizer_iff.mp (hFleC hf) z hz).symm
  obtain ⟨hcardUx, hcardZF⟩ :=
    center_and_involution_commutator_card F hFne hFp hFodd x hx hgen
      hcommFx hcommFV hindex hfaith hcenterComm
  have hcardCenterInF : Nat.card (centerIn F) = 3 := by
    rw [centerIn_eq_map_center,
      Subgroup.card_map_of_injective F.subtype_injective]
    exact hcardZF
  have hZ0eq : Z0 = centerIn F :=
    Subgroup.eq_of_le_of_card_ge hZ0leZF (by
      rw [hcardZ0, hcardCenterInF])
  have hcommZFV : commutatorAction (Subgroup.center F) V = ⊤ :=
    center_commutatorAction_eq_top_of_center_fixed
      F hFnorm x hgen hcommFx hcommFV hfaith hcenterComm hcardUx hcardZF
  have hcommZ0V : commutatorAction Z0 V = ⊤ := by
    rw [hZ0eq, centerIn_eq_map_center, center_map_commutatorAction_eq]
    exact hcommZFV
  apply hV0proper
  apply le_antisymm le_top
  rw [← hcommZ0V]
  exact commutatorAction_subgroup_mono (show Z0 ≤ F0 from fun z hz => hz.1)

private theorem recursive_noncommutative_x_subgroup_card_twenty_seven
    {p : ℕ} [Fact p.Prime]
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFp : IsPGroup p F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (recurse : SmallIndexClassificationBelow.{u, v}
      (Nat.card F * Nat.card V))
    (H : Subgroup G) (hHF : H ≤ F) (hHne : H ≠ ⊥)
    (hcardHlt : Nat.card H < Nat.card F)
    (hcommHx : ⁅H, Subgroup.zpowers x⁆ = H)
    (hHnoncomm : ¬ IsMulCommutative H) :
    Nat.card H = 3 ^ 3 := by
  let R : Subgroup G := Subgroup.zpowers x
  let E : Subgroup G := H ⊔ R
  have hHE : H ≤ E := le_sup_left
  have hRnormH : R ≤ Subgroup.normalizer (H : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (by
      simp [R, hcommHx])
  have hEnormH : E ≤ Subgroup.normalizer (H : Set G) :=
    sup_le Subgroup.le_normalizer hRnormH
  let hVinv : IsInvariant E V (commutatorAction H V) := by
    simpa using
      commutatorAction_isInvariant_of_normalizing_actor E H hEnormH
  let _ : IsInvariant E V (commutatorAction H V) := hVinv
  let HE : Subgroup E := H.subgroupOf E
  let xE : E := ⟨x, (show R ≤ E from le_sup_right) (Subgroup.mem_zpowers x)⟩
  have hrec : SmallIndexConclusion (V := commutatorAction H V) HE xE :=
    recursive_call_on_proper_x_commutator_subgroup
      F hFp hFodd x hx hfaith hindex recurse H hHF hHne
        (Nat.mul_lt_mul_of_pos_right hcardHlt Nat.card_pos) hcommHx
  have hHEnoncomm : ¬ IsMulCommutative HE := by
    intro hcomm
    apply hHnoncomm
    exact isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hHE).symm
  have hcardHE : Nat.card HE = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHE).toEquiv
  rcases hrec with hsmall | hsmall | hlarge
  · exact False.elim (hHEnoncomm
      (isMulCommutative_of_mulEquiv hsmall.2.some))
  · rcases hsmall.2.2 with hthree | hfive | hnine
    · exact False.elim (hHEnoncomm
        (isMulCommutative_of_mulEquiv hthree.some))
    · exact False.elim (hHEnoncomm
        (isMulCommutative_of_mulEquiv hfive.some))
    · exact False.elim (hHEnoncomm
        (isMulCommutative_of_mulEquiv hnine.some))
  · rw [← hcardHE]
    exact hlarge.2.2.2.2

private theorem first_centralizer_commutator_eq_pair
    {p : ℕ} [Fact p.Prime]
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFp : IsPGroup p F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (recurse : SmallIndexClassificationBelow.{u, v}
      (Nat.card F * Nat.card V))
    (a b : G) (haF : a ∈ F) (hbF : b ∈ F)
    (hainv : x * a * x⁻¹ = a⁻¹)
    (hbinv : x * b * x⁻¹ = b⁻¹)
    (hncomm : ¬ Commute a b)
    (hcardF0 : Nat.card
      (↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G)) = 3 ^ 3)
    (hZ0commR :
      ⁅centerIn (Subgroup.zpowers a ⊔ Subgroup.zpowers b),
        Subgroup.zpowers x⁆ = ⊥)
    (hF0F1 : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤
      F ⊓ Subgroup.centralizer
        (centerIn (Subgroup.zpowers a ⊔ Subgroup.zpowers b) : Set G))
    (hF1lt : F ⊓ Subgroup.centralizer
        (centerIn (Subgroup.zpowers a ⊔ Subgroup.zpowers b) : Set G) < F) :
    ⁅F ⊓ Subgroup.centralizer
        (centerIn (Subgroup.zpowers a ⊔ Subgroup.zpowers b) : Set G),
      Subgroup.zpowers x⁆ =
        Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  classical
  let R : Subgroup G := Subgroup.zpowers x
  let F0 : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  let Z0 : Subgroup G := centerIn F0
  let F1 : Subgroup G := F ⊓ Subgroup.centralizer (Z0 : Set G)
  let H1 : Subgroup G := ⁅F1, R⁆
  have hF1F : F1 ≤ F := inf_le_left
  have hRleC : R ≤ Subgroup.centralizer (Z0 : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
      Subgroup.commutator_comm]
    simpa [R, Z0, F0] using hZ0commR
  have hH1leC : H1 ≤ Subgroup.centralizer (Z0 : Set G) := by
    calc
      H1 = ⁅F1, R⁆ := rfl
      _ ≤ F1 ⊔ R := Subgroup.commutator_le_sup F1 R
      _ ≤ Subgroup.centralizer (Z0 : Set G) := sup_le inf_le_right hRleC
  have hH1leF : H1 ≤ F := by
    calc
      H1 = ⁅F1, R⁆ := rfl
      _ ≤ ⁅F, R⁆ := Subgroup.commutator_mono hF1F le_rfl
      _ = F := by simpa [R] using hcommFx
  have hH1F1 : H1 ≤ F1 := fun h hh => ⟨hH1leF hh, hH1leC hh⟩
  have hRnormF1 : R ≤ Subgroup.normalizer (F1 : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hH1F1
  have hcardR : Nat.card R = 2 := by
    simpa [R, Nat.card_zpowers] using orderOf_eq_prime hx.2 hx.1
  have hcopRF1 : Nat.Coprime (Nat.card R) (Nat.card F1) := by
    rw [hcardR]
    exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hF1F) hFodd
  have hcommH1R : ⁅H1, R⁆ = H1 := by
    simpa [H1] using
      commutator_double_eq_self_of_coprime R F1 hRnormF1 hcopRF1
  have haodd : Nat.Coprime 2 (orderOf a) :=
    Nat.Coprime.of_dvd_right (by
      simpa [Subgroup.orderOf_coe] using
        (orderOf_dvd_natCard (⟨a, haF⟩ : F))) hFodd
  have hbodd : Nat.Coprime 2 (orderOf b) :=
    Nat.Coprime.of_dvd_right (by
      simpa [Subgroup.orderOf_coe] using
        (orderOf_dvd_natCard (⟨b, hbF⟩ : F))) hFodd
  have hcommF0R : ⁅F0, R⁆ = F0 := by
    simpa [F0, R] using
      commutator_two_inverted_generators_eq a b x haodd hbodd hx hainv hbinv
  have hF0leH1 : F0 ≤ H1 := by
    calc
      F0 = ⁅F0, R⁆ := hcommF0R.symm
      _ ≤ ⁅F1, R⁆ := Subgroup.commutator_mono
        (by simpa [F0, F1, Z0] using hF0F1) le_rfl
      _ = H1 := rfl
  have hH1ne : H1 ≠ ⊥ := by
    intro hbot
    have haH1 : a ∈ H1 := hF0leH1
      ((show Subgroup.zpowers a ≤ F0 from le_sup_left)
        (Subgroup.mem_zpowers a))
    have hbH1 : b ∈ H1 := hF0leH1
      ((show Subgroup.zpowers b ≤ F0 from le_sup_right)
        (Subgroup.mem_zpowers b))
    rw [hbot] at haH1 hbH1
    have haone : a = 1 := by simpa using haH1
    have hbone : b = 1 := by simpa using hbH1
    apply hncomm
    simp [haone, hbone]
  have hH1noncomm : ¬ IsMulCommutative H1 := by
    intro hcomm
    let aa : H1 := ⟨a, hF0leH1
      ((show Subgroup.zpowers a ≤ F0 from le_sup_left)
        (Subgroup.mem_zpowers a))⟩
    let bb : H1 := ⟨b, hF0leH1
      ((show Subgroup.zpowers b ≤ F0 from le_sup_right)
        (Subgroup.mem_zpowers b))⟩
    apply hncomm
    exact congrArg (fun z : H1 => (z : G)) ((hcomm.is_comm).comm aa bb)
  have hH1ltF : H1 < F := lt_of_le_of_lt hH1F1 (by
    simpa [F1, Z0, F0] using hF1lt)
  have hcardH1lt : Nat.card H1 < Nat.card F := by
    apply Nat.lt_of_le_of_ne (Subgroup.card_le_of_le hH1ltF.le)
    intro heq
    exact hH1ltF.ne (Subgroup.eq_of_le_of_card_ge hH1ltF.le (by omega))
  have hcardH1 : Nat.card H1 = 3 ^ 3 :=
    recursive_noncommutative_x_subgroup_card_twenty_seven
      F hFp hFodd x hx hindex hfaith recurse H1 hH1leF hH1ne
        hcardH1lt (by simpa [R] using hcommH1R) hH1noncomm
  have hEq : F0 = H1 :=
    Subgroup.eq_of_le_of_card_ge hF0leH1 (by
      simpa [F0] using (hcardF0.trans hcardH1.symm).ge)
  simpa [F1, Z0, F0, R, H1] using hEq.symm

private theorem first_centralizer_center_fixed
    {G : Type*} [Group G] [Finite G]
    (F F0 : Subgroup G)
    (x : G) (hx : IsInvolution x)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (hZ0commR : ⁅centerIn F0, Subgroup.zpowers x⁆ = ⊥)
    (hF0F1 : F0 ≤
      F ⊓ Subgroup.centralizer (centerIn F0 : Set G))
    (hcommF1R :
      ⁅F ⊓ Subgroup.centralizer (centerIn F0 : Set G),
        Subgroup.zpowers x⁆ = F0) :
    ⁅centerIn (F ⊓ Subgroup.centralizer (centerIn F0 : Set G)),
      Subgroup.zpowers x⁆ = ⊥ := by
  classical
  let R : Subgroup G := Subgroup.zpowers x
  let Z0 : Subgroup G := centerIn F0
  let F1 : Subgroup G := F ⊓ Subgroup.centralizer (Z0 : Set G)
  let Z1 : Subgroup G := centerIn F1
  have hF1F : F1 ≤ F := inf_le_left
  have hZ1F1 : Z1 ≤ F1 := fun z hz => hz.1
  have hF0F1' : F0 ≤ F1 := by simpa [F1, Z0] using hF0F1
  have hcommF1R' : ⁅F1, R⁆ = F0 := by
    simpa [F1, Z0, R] using hcommF1R
  have hF1centralZ1 : F1 ≤ Subgroup.centralizer (Z1 : Set G) := by
    intro f hf
    change ∀ z ∈ Z1, z * f = f * z
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 f hf).symm
  have hrotOne : ⁅⁅R, F1⁆, Z1⁆ = ⊥ := by
    rw [Subgroup.commutator_comm R F1, hcommF1R']
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hF0F1'.trans hF1centralZ1)
  have hrotTwo : ⁅⁅F1, Z1⁆, R⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hF1centralZ1]
    exact Subgroup.commutator_bot_left R
  have hcentral : ⁅⁅Z1, R⁆, F1⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hrotOne hrotTwo
  have hcommZ1RleZ1 : ⁅Z1, R⁆ ≤ Z1 := fun z hz =>
    ⟨(by
        apply hF0F1'
        rw [← hcommF1R']
        exact Subgroup.commutator_mono hZ1F1 le_rfl hz),
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentral) hz⟩
  have hRnormZ1 : R ≤ Subgroup.normalizer (Z1 : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hcommZ1RleZ1
  have hcopRZ1 : Nat.Coprime (Nat.card R) (Nat.card Z1) := by
    have hcardR : Nat.card R = 2 := by
      simpa [R, Nat.card_zpowers] using orderOf_eq_prime hx.2 hx.1
    rw [hcardR]
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_dvd_of_le (hZ1F1.trans hF1F)) hFodd
  have hdouble : ⁅⁅Z1, R⁆, R⁆ = ⁅Z1, R⁆ :=
    commutator_double_eq_self_of_coprime R Z1 hRnormZ1 hcopRZ1
  have hcommZ1RleZ0 : ⁅Z1, R⁆ ≤ Z0 := by
    intro z hz
    refine ⟨?_, ?_⟩
    · rw [← hcommF1R']
      exact Subgroup.commutator_mono hZ1F1 le_rfl hz
    · change ∀ f ∈ F0, f * z = z * f
      intro f hf
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentral hz
        f (hF0F1' hf)
  have hdoubleBot : ⁅⁅Z1, R⁆, R⁆ = ⊥ := by
    apply le_antisymm
    · calc
        ⁅⁅Z1, R⁆, R⁆ ≤ ⁅Z0, R⁆ :=
          Subgroup.commutator_mono hcommZ1RleZ0 le_rfl
        _ = ⊥ := by simpa [Z0, R] using hZ0commR
    · exact bot_le
  have hsingleBot : ⁅Z1, R⁆ = ⊥ := hdouble.symm.trans hdoubleBot
  simpa only [Z1, F1, Z0, R] using hsingleBot

private theorem normalizer_inf_normalizer_le_normalizer_commutator
    {G : Type*} [Group G] (H K : Subgroup G) :
    Subgroup.normalizer (H : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  intro g hg
  rcases hg with ⟨hgH, hgK⟩
  have hgH' := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (show g ∈ Subgroup.normalizer (H : Set G) from hgH)
  have hgK' := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (show g ∈ Subgroup.normalizer (K : Set G) from hgK)
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_commutator, hgH', hgK']

private theorem normalizer_le_normalizer_centerIn
    {G : Type*} [Group G] (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (centerIn H : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg z hz
  have hzH : z ∈ H := hz.1
  have hconjH : g * z * g⁻¹ ∈ H :=
    (Subgroup.mem_normalizer_iff.mp hg z).mp hzH
  refine ⟨hconjH, ?_⟩
  change ∀ h ∈ H, h * (g * z * g⁻¹) = (g * z * g⁻¹) * h
  intro h hh
  have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normalizer (H : Set G)).inv_mem hg
  have hpre : g⁻¹ * h * (g⁻¹)⁻¹ ∈ H :=
    (Subgroup.mem_normalizer_iff.mp hginv h).mp hh
  have hcomm := Subgroup.mem_centralizer_iff.mp hz.2
    (g⁻¹ * h * g) (by simpa using hpre)
  calc
    h * (g * z * g⁻¹) = g * ((g⁻¹ * h * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * z * g⁻¹) * h := by group

private theorem prime_eq_three_of_pgroup_subgroup_card_twenty_seven
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (F F0 : Subgroup G) (hFp : IsPGroup p F) (hF0F : F0 ≤ F)
    (hcardF0 : Nat.card F0 = 3 ^ 3) : p = 3 := by
  have hF0p : IsPGroup p F0 := by
    have hsub : IsPGroup p (F0.subgroupOf F) :=
      hFp.to_subgroup (F0.subgroupOf F)
    exact hsub.of_equiv (Subgroup.subgroupOfEquivOfLe hF0F)
  obtain ⟨n, hn⟩ := hF0p.exists_card_eq
  have hnne : n ≠ 0 := by
    intro hnzero
    rw [hnzero, pow_zero, hcardF0] at hn
    norm_num at hn
  have hpdiv : p ∣ 3 ^ 3 := by
    rw [← hcardF0, hn]
    exact dvd_pow_self p hnne
  have hpdiv3 : p ∣ 3 := (Fact.out : Nat.Prime p).dvd_of_dvd_pow hpdiv
  exact (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p)
    Nat.prime_three).mp hpdiv3

private theorem lt_ambient_normalizer_inter_of_isPGroup
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (F F1 : Subgroup G) (hFp : IsPGroup p F) (hF1lt : F1 < F) :
    F1 < F ⊓ Subgroup.normalizer (F1 : Set G) := by
  classical
  let K : Subgroup F := F1.subgroupOf F
  have hKlt : K < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro hKtop
    apply hF1lt.ne
    calc
      F1 = K.map F.subtype := by
        symm
        simpa [K] using Subgroup.map_subgroupOf_eq_of_le hF1lt.le
      _ = (⊤ : Subgroup F).map F.subtype := by rw [hKtop]
      _ = F.subtype.range := (MonoidHom.range_eq_map F.subtype).symm
      _ = F := F.range_subtype
  let hFnil : Group.IsNilpotent F := hFp.isNilpotent
  let _ : Group.IsNilpotent F := hFnil
  have hKnormlt : K < Subgroup.normalizer (K : Set F) :=
    Group.normalizerCondition_of_isNilpotent K hKlt
  obtain ⟨y, hynorm, hynotK⟩ := SetLike.exists_of_lt hKnormlt
  have hyMap : (y : G) ∈
      (Subgroup.normalizer (K : Set F)).map F.subtype :=
    ⟨y, hynorm, rfl⟩
  have hynormF1 : (y : G) ∈ Subgroup.normalizer (F1 : Set G) := by
    have hmap := Subgroup.le_normalizer_map F.subtype hyMap
    rw [show K.map F.subtype = F1 by
      simpa [K] using Subgroup.map_subgroupOf_eq_of_le hF1lt.le] at hmap
    exact hmap
  have hle : F1 ≤ F ⊓ Subgroup.normalizer (F1 : Set G) :=
    fun f hf => ⟨hF1lt.le hf, Subgroup.le_normalizer hf⟩
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hyF1 : (y : G) ∈ F1 := by
    rw [heq]
    exact ⟨y.property, hynormF1⟩
  exact hynotK hyF1

private theorem fixedPointSubgroup_map_le_first_centralizer
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (F F0 F1 F2 R : Subgroup G)
    (hFp : IsPGroup p F) (hpThree : p = 3)
    (hF2F : F2 ≤ F)
    (hF2normF1 : F2 ≤ Subgroup.normalizer (F1 : Set G))
    (hcommF1R : ⁅F1, R⁆ = F0)
    (hRnormF2 : R ≤ Subgroup.normalizer (F2 : Set G))
    (hcardZ0 : Nat.card (centerIn F0) = 3)
    (hF1def : F1 = F ⊓ Subgroup.centralizer (centerIn F0 : Set G)) :
    let _ : MulDistribMulAction R F2 :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer R F2 hRnormF2
    (fixedPointSubgroup R F2).map F2.subtype ≤ F1 := by
  classical
  dsimp only
  subst p
  let _ : MulDistribMulAction R F2 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer R F2 hRnormF2
  let C : Subgroup F2 := fixedPointSubgroup R F2
  intro c hc
  obtain ⟨c0, hc0C, rfl⟩ := Subgroup.mem_map.mp hc
  have hc0fix : ∀ r : R, r • c0 = c0 := by
    rw [FixedPoints.mem_subgroup] at hc0C
    exact hc0C
  have hcCentralR : (c0 : G) ∈ Subgroup.centralizer (R : Set G) := by
    change ∀ r ∈ R, r * (c0 : G) = (c0 : G) * r
    intro r hr
    let r0 : R := ⟨r, hr⟩
    have hfix := congrArg (fun y : F2 => ((y : F2) : G)) (hc0fix r0)
    change r * (c0 : G) * r⁻¹ = (c0 : G) at hfix
    calc
      r * (c0 : G) = (r * (c0 : G) * r⁻¹) * r := by group
      _ = (c0 : G) * r := by rw [hfix]
  have hcNormR : (c0 : G) ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.centralizer_le_normalizer (R : Set G) hcCentralR
  have hcNormF0 : (c0 : G) ∈ Subgroup.normalizer (F0 : Set G) := by
    have hcCommon : (c0 : G) ∈
        Subgroup.normalizer (F1 : Set G) ⊓
          Subgroup.normalizer (R : Set G) :=
      ⟨hF2normF1 c0.property, hcNormR⟩
    have hcCommNorm :=
      normalizer_inf_normalizer_le_normalizer_commutator F1 R hcCommon
    rwa [hcommF1R] at hcCommNorm
  have hcNormZ0 : (c0 : G) ∈
      Subgroup.normalizer (centerIn F0 : Set G) :=
    normalizer_le_normalizer_centerIn F0 hcNormF0
  let A : Subgroup G := Subgroup.zpowers (c0 : G)
  have hAnormZ0 : A ≤ Subgroup.normalizer (centerIn F0 : Set G) :=
    Subgroup.zpowers_le.mpr hcNormZ0
  let _ : Subgroup.Normalizes A (centerIn F0) := ⟨hAnormZ0⟩
  let _ : MulDistribMulAction A (centerIn F0) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A (centerIn F0) hAnormZ0
  have hAF : A ≤ F := Subgroup.zpowers_le.mpr (hF2F c0.property)
  have hAthree : IsPGroup 3 A := by
    have hsub : IsPGroup 3 (A.subgroupOf F) :=
      hFp.to_subgroup (A.subgroupOf F)
    exact hsub.of_equiv (Subgroup.subgroupOfEquivOfLe hAF)
  let hthreePrime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fact (Nat.Prime 3) := hthreePrime
  let hZ0cyclic : IsCyclic (centerIn F0) := isCyclic_of_prime_card hcardZ0
  have htriv : ActsTrivially (A := A) (G := centerIn F0) :=
    actsTrivially_of_isPGroup_on_cyclic_prime_order
      Nat.prime_three hAthree hZ0cyclic hcardZ0
  have hcCentralZ0 : (c0 : G) ∈
      Subgroup.centralizer (centerIn F0 : Set G) := by
    change ∀ z ∈ centerIn F0, z * (c0 : G) = (c0 : G) * z
    intro z hz
    let a0 : A := ⟨(c0 : G), Subgroup.mem_zpowers (c0 : G)⟩
    let z0 : centerIn F0 := ⟨z, hz⟩
    have hfix := congrArg (fun y : centerIn F0 => ((y : centerIn F0) : G))
      (htriv a0 z0)
    change (c0 : G) * z * (c0 : G)⁻¹ = z at hfix
    calc
      z * (c0 : G) = ((c0 : G) * z * (c0 : G)⁻¹) * (c0 : G) := by
        rw [hfix]
      _ = (c0 : G) * z := by group
  rw [hF1def]
  exact ⟨hF2F c0.property, hcCentralZ0⟩

private theorem second_normalizer_commutator_noncentral
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (F F0 F1 F2 R : Subgroup G)
    (hFp : IsPGroup p F) (hFodd : Nat.Coprime 2 (Nat.card F))
    (hF2F : F2 ≤ F) (hF0F1 : F0 ≤ F1)
    (hF1ltF2 : F1 < F2)
    (hcommFx : ⁅F, R⁆ = F)
    (hRnormF2 : R ≤ Subgroup.normalizer (F2 : Set G))
    (hcardR : Nat.card R = 2)
    (hF1def : F1 = F ⊓ Subgroup.centralizer (centerIn F0 : Set G))
    (hfixedLe :
      let _ : MulDistribMulAction R F2 :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer R F2 hRnormF2
      (fixedPointSubgroup R F2).map F2.subtype ≤ F1) :
    ⁅⁅F2, R⁆, centerIn F1⁆ ≠ ⊥ := by
  classical
  let _ : MulDistribMulAction R F2 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer R F2 hRnormF2
  let C : Subgroup F2 := fixedPointSubgroup R F2
  let D : Subgroup F2 := commutatorAction R F2
  have hF2p : IsPGroup p F2 := by
    have hsub : IsPGroup p (F2.subgroupOf F) :=
      hFp.to_subgroup (F2.subgroupOf F)
    exact hsub.of_equiv (Subgroup.subgroupOfEquivOfLe hF2F)
  let hF2nil : Group.IsNilpotent F2 := hF2p.isNilpotent
  let _ : Group.IsNilpotent F2 := hF2nil
  have hcopRF2 : Nat.Coprime (Nat.card R) (Nat.card F2) := by
    rw [hcardR]
    exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hF2F) hFodd
  have hsup : C ⊔ D = ⊤ := by
    simpa [C, D] using
      fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
        (G := F2) (A := R) (by infer_instance) hcopRF2
  have hDmap : D.map F2.subtype = ⁅F2, R⁆ := by
    simpa [D] using
      commutatorAction_subgroup_conj_map_eq_commutator F2 R hRnormF2
  intro hcentral
  have hcommLeZ1 : ⁅F2, R⁆ ≤
      Subgroup.centralizer (centerIn F1 : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentral
  have hZ0Z1 : centerIn F0 ≤ centerIn F1 := by
    intro z hz
    refine ⟨hF0F1 hz.1, ?_⟩
    change ∀ f ∈ F1, f * z = z * f
    intro f hf
    have hfC : f ∈ Subgroup.centralizer (centerIn F0 : Set G) := by
      rw [hF1def] at hf
      exact hf.2
    exact (Subgroup.mem_centralizer_iff.mp hfC z hz).symm
  have hcommLeF : ⁅F2, R⁆ ≤ F := by
    calc
      ⁅F2, R⁆ ≤ ⁅F, R⁆ := Subgroup.commutator_mono hF2F le_rfl
      _ = F := hcommFx
  have hcommLeF1 : ⁅F2, R⁆ ≤ F1 := by
    rw [hF1def]
    refine fun y hy => ⟨hcommLeF hy, ?_⟩
    change ∀ z ∈ centerIn F0, z * y = y * z
    intro z hz
    exact Subgroup.mem_centralizer_iff.mp (hcommLeZ1 hy) z (hZ0Z1 hz)
  have hDleF1 : D.map F2.subtype ≤ F1 := by
    rw [hDmap]
    exact hcommLeF1
  have hTopMapLe : (⊤ : Subgroup F2).map F2.subtype ≤ F1 := by
    rw [← hsup, Subgroup.map_sup]
    exact sup_le hfixedLe hDleF1
  have hF2F1 : F2 ≤ F1 := by
    intro y hy
    exact hTopMapLe ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
  exact hF1ltF2.2 hF2F1

private theorem second_normalizer_three_subgroup_contradiction
    {G : Type*} [Group G]
    (F1 F2 R : Subgroup G)
    (hF2normF1 : F2 ≤ Subgroup.normalizer (F1 : Set G))
    (hcenterFixed : ⁅centerIn F1, R⁆ = ⊥)
    (hnoncentral : ⁅⁅F2, R⁆, centerIn F1⁆ ≠ ⊥) : False := by
  let Z1 : Subgroup G := centerIn F1
  have hF2normZ1 : F2 ≤ Subgroup.normalizer (Z1 : Set G) :=
    hF2normF1.trans (normalizer_le_normalizer_centerIn F1)
  have hcommZ1F2le : ⁅Z1, F2⁆ ≤ Z1 :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hF2normZ1
  have hrotOne : ⁅⁅R, Z1⁆, F2⁆ = ⊥ := by
    rw [Subgroup.commutator_comm R Z1,
      show ⁅Z1, R⁆ = ⊥ by simpa [Z1] using hcenterFixed,
      Subgroup.commutator_bot_left]
  have hrotTwo : ⁅⁅Z1, F2⁆, R⁆ = ⊥ := by
    apply le_antisymm
    · calc
        ⁅⁅Z1, F2⁆, R⁆ ≤ ⁅Z1, R⁆ :=
          Subgroup.commutator_mono hcommZ1F2le le_rfl
        _ = ⊥ := by simpa [Z1] using hcenterFixed
    · exact bot_le
  apply hnoncentral
  simpa [Z1] using
    Subgroup.commutator_commutator_eq_bot_of_rotate hrotOne hrotTwo

private theorem centerFixedCases_complete : CenterFixedCases.{u, v} := by
  intro G V _ _ _ _ _ _ F hFnorm hFne p hpFact hFp hFodd x hx hgen
    hcommFx hcommFV hindex hfaith hcenterComm recurse
  let _ : Fact p.Prime := hpFact
  have hFnoncomm : ¬ IsMulCommutative F := by
    intro hFcomm
    let _ : IsMulCommutative F := hFcomm
    have hcenterMap : (Subgroup.center F).map F.subtype = F := by
      rw [Subgroup.center_eq_top]
      calc
        Subgroup.map F.subtype ⊤ = F.subtype.range :=
          (MonoidHom.range_eq_map F.subtype).symm
        _ = F := F.range_subtype
    have hcommBot : ⁅F, Subgroup.zpowers x⁆ = ⊥ := by
      simpa [hcenterMap] using hcenterComm
    exact hFne (hcommFx.symm.trans hcommBot)
  obtain ⟨a, b, haF, hbF, hainv, hbinv, hncomm⟩ :=
    exists_noncommuting_inverted_elements F x hx hcommFx hFnoncomm
  let F0 : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  by_cases hF0eq : F0 = F
  · exact centerFixedCase_of_two_inverted_generators
      F hFnorm hFne hFp hFodd x hx hgen hcommFx hcommFV hindex hfaith
        hcenterComm a b haF hbF hainv hbinv hncomm
          (by simpa [F0] using hF0eq)
  · let R : Subgroup G := Subgroup.zpowers x
    let V0 : Subgroup V := commutatorAction F0 V
    have hF0F : F0 ≤ F :=
      sup_le (Subgroup.zpowers_le.mpr haF) (Subgroup.zpowers_le.mpr hbF)
    obtain ⟨hcardV0, hcardF0, hcardZ0, hZ0commR⟩ :=
      proper_inverted_pair_center_data
        F hFp hFodd x hx hindex hfaith a b haF hbF hainv hbinv hncomm
          recurse (by simpa [F0] using hF0eq)
    have hV0proper : V0 ≠ ⊤ := by
      simpa [V0] using
        proper_commutatorAction_ne_top_of_center_fixed
          F hFnorm hFne hFp hFodd x hx hgen hcommFx hcommFV hindex
            hfaith hcenterComm hFnoncomm F0 hF0F hF0eq hcardF0 hcardV0
    let Z0 : Subgroup G := centerIn F0
    let F1 : Subgroup G := F ⊓ Subgroup.centralizer (Z0 : Set G)
    obtain ⟨hF0F1, hF1lt⟩ :=
      center_centralizer_proper_of_proper_local_action
        F hFnorm hFne hFp hFodd x hx hgen hcommFx hcommFV hindex
          hfaith hcenterComm F0 hF0F (by simpa [Z0] using hcardZ0)
            (by simpa [V0] using hV0proper)
    have hcommF1R : ⁅F1, R⁆ = F0 := by
      simpa [F1, Z0, F0, R] using
        first_centralizer_commutator_eq_pair
          F hFp hFodd x hx hcommFx hindex hfaith recurse a b haF hbF
            hainv hbinv hncomm (by simpa [F0] using hcardF0)
                (by simpa [F0, R, Z0] using hZ0commR)
                  (by simpa [F0, F1, Z0] using hF0F1)
                    (by simpa [F1, Z0] using hF1lt)
    have hcenterF1 : ⁅centerIn F1, R⁆ = ⊥ := by
      simpa [F1, Z0, R] using
        first_centralizer_center_fixed
          F F0 x hx hFodd (by simpa [Z0, R] using hZ0commR)
            (by simpa [F1, Z0] using hF0F1)
              (by simpa [F1, Z0, R] using hcommF1R)
    have hpThree : p = 3 :=
      prime_eq_three_of_pgroup_subgroup_card_twenty_seven
        F F0 hFp hF0F hcardF0
    let F2 : Subgroup G := F ⊓ Subgroup.normalizer (F1 : Set G)
    have hF1ltF2 : F1 < F2 := by
      simpa [F2] using
        lt_ambient_normalizer_inter_of_isPGroup F F1 hFp hF1lt
    have hF2F : F2 ≤ F := inf_le_left
    have hF2normF1 : F2 ≤ Subgroup.normalizer (F1 : Set G) := inf_le_right
    have hRnormF1 : R ≤ Subgroup.normalizer (F1 : Set G) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mpr (by
        rw [hcommF1R]
        exact hF0F1)
    have hcommF2RleF : ⁅F2, R⁆ ≤ F := by
      calc
        ⁅F2, R⁆ ≤ ⁅F, R⁆ := Subgroup.commutator_mono hF2F le_rfl
        _ = F := by simpa [R] using hcommFx
    have hcommF2RleNorm : ⁅F2, R⁆ ≤
        Subgroup.normalizer (F1 : Set G) := by
      calc
        ⁅F2, R⁆ ≤ F2 ⊔ R := Subgroup.commutator_le_sup F2 R
        _ ≤ Subgroup.normalizer (F1 : Set G) :=
          sup_le hF2normF1 hRnormF1
    have hRnormF2 : R ≤ Subgroup.normalizer (F2 : Set G) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mpr
        (fun y hy => ⟨hcommF2RleF hy, hcommF2RleNorm hy⟩)
    have hcardR : Nat.card R = 2 := by
      simpa [R, Nat.card_zpowers] using orderOf_eq_prime hx.2 hx.1
    have hfixedLe :
        let _ : MulDistribMulAction R F2 :=
          Subgroup.conjMulDistribMulActionOfLeNormalizer R F2 hRnormF2
        (fixedPointSubgroup R F2).map F2.subtype ≤ F1 :=
      fixedPointSubgroup_map_le_first_centralizer
        F F0 F1 F2 R hFp hpThree hF2F hF2normF1 hcommF1R
          hRnormF2 (by simpa [Z0] using hcardZ0) (by rfl)
    have hnoncentral : ⁅⁅F2, R⁆, centerIn F1⁆ ≠ ⊥ :=
      second_normalizer_commutator_noncentral
        F F0 F1 F2 R hFp hFodd hF2F hF0F1 hF1ltF2
          (by simpa [R] using hcommFx) hRnormF2 hcardR (by rfl) hfixedLe
    exact False.elim (second_normalizer_three_subgroup_contradiction
      F1 F2 R hF2normF1 hcenterF1 hnoncentral)

/-- The source-faithful reduced classification used in Stellmacher's Lemma (1.3). -/
public theorem involutionPGroup_smallIndex_classification
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFnorm : F.Normal) (hFne : F ≠ ⊥)
    (p : ℕ) [Fact p.Prime] (hFp : IsPGroup p F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hgen : F ⊔ Subgroup.zpowers x = ⊤)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hcommFV : commutatorAction F V = ⊤)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    (Nat.card V = 4 ∧
        Nonempty (F ≃* Multiplicative (ZMod 3))) ∨
      (Nat.card V = 2 ^ 4 ∧
        Nat.card V =
          4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) ∧
        (Nonempty (F ≃* Multiplicative (ZMod 3)) ∨
         Nonempty (F ≃* Multiplicative (ZMod 5)) ∨
         Nonempty
           (F ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))))) ∨
      (Nat.card V = 2 ^ 6 ∧
        Nat.card V =
          4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) ∧
        ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥ ∧
        IsExtraspecial 3 F ∧ Nat.card F = 3 ^ 3) :=
  smallIndexClassification_of_centerFixedCases centerFixedCases_complete
    G V F hFnorm hFne p inferInstance hFp hFodd x hx hgen hcommFx
      hcommFV hindex hfaith

private theorem extraspecial_of_mulEquiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsExtraspecial 3 A) : IsExtraspecial 3 B := by
  let _ : IsExtraspecial 3 A := h
  have hc : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (Subgroup.centerCongr e ⟨a, ha⟩).property
    · intro hb
      exact ⟨e.symm b, (Subgroup.centerCongr e.symm ⟨b, hb⟩).property,
        e.apply_symm_apply b⟩
  let q := QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e hc
  let _ : IsElementaryAbelian 3 (A ⧸ Subgroup.center A) := h.quotient_elementary_abelian
  let _ : Nontrivial (A ⧸ Subgroup.center A) := h.quotient_nontrivial
  refine ⟨?_, ?_, q.symm.toEquiv.nontrivial⟩
  · exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm.trans h.center_order_p
  · refine
      { toIsMulCommutative := isMulCommutative_of_mulEquiv q.symm
        exponent_dvd_p := ?_ }
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro b
    apply q.symm.injective
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 (A ⧸ Subgroup.center A)) (q.symm b)

/-- The reduced classification transported to a faithful ambient action,
without assuming that the odd subgroup generates the whole action space. -/
public theorem involutionPGroup_smallIndex_classification_on_commutator
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (F : Subgroup G) (hFne : F ≠ ⊥)
    (p : ℕ) [Fact p.Prime] (hFp : IsPGroup p F)
    (hFodd : Nat.Coprime 2 (Nat.card F))
    (x : G) (hx : IsInvolution x)
    (hcommFx : ⁅F, Subgroup.zpowers x⁆ = F)
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    (Nat.card (commutatorAction F V) = 4 ∧
        Nonempty (F ≃* Multiplicative (ZMod 3))) ∨
      (Nat.card (commutatorAction F V) = 2 ^ 4 ∧
        Nat.card V =
          4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) ∧
        (Nonempty (F ≃* Multiplicative (ZMod 3)) ∨
         Nonempty (F ≃* Multiplicative (ZMod 5)) ∨
         Nonempty (F ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))))) ∨
      (Nat.card (commutatorAction F V) = 2 ^ 6 ∧
        Nat.card V =
          4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V) ∧
        ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥ ∧
        IsExtraspecial 3 F ∧ Nat.card F = 3 ^ 3) := by
  classical
  let R : Subgroup G := Subgroup.zpowers x
  let E : Subgroup G := F ⊔ R
  let U : Subgroup V := commutatorAction F V
  have hFE : F ≤ E := le_sup_left
  have hRE : R ≤ E := le_sup_right
  have hRnorm : R ≤ Subgroup.normalizer (F : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (by
      rw [show ⁅F, R⁆ = F from hcommFx])
  have hEnorm : E ≤ Subgroup.normalizer (F : Set G) :=
    sup_le Subgroup.le_normalizer hRnorm
  let hUinv : IsInvariant E V U :=
    commutatorAction_isInvariant_of_normalizing_actor E F hEnorm
  let _ : IsInvariant E V U := hUinv
  let _ : IsElementaryAbelian 2 U := elementaryAbelian_subgroup U
  let FE : Subgroup E := F.subgroupOf E
  let xE : E := ⟨x, hRE (Subgroup.mem_zpowers x)⟩
  let e : FE ≃* F := Subgroup.subgroupOfEquivOfLe hFE
  have hxE : IsInvolution xE := by
    refine ⟨fun heq => hx.1 (congrArg Subtype.val heq), ?_⟩
    exact Subtype.ext hx.2
  have hmapX : (Subgroup.zpowers xE).map E.subtype = R := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le]
      exact Subgroup.mem_zpowers x
    · rw [Subgroup.zpowers_le]
      exact ⟨xE, Subgroup.mem_zpowers xE, rfl⟩
  have recurse : SmallIndexClassificationBelow.{u, v}
      (Nat.card F * Nat.card V + 1) := by
    intro G V _ _ _ _ _ _ F hFn hFne p hp hFp hFo x hx hg hc hv hi hf _
    let _ : Fact p.Prime := hp
    exact involutionPGroup_smallIndex_classification F hFn hFne p hFp hFo
      x hx hg hc hv hi hf
  have hrec : SmallIndexConclusion (V := U) FE xE :=
    recursive_call_on_proper_x_commutator_subgroup F hFp hFodd x hx hfaith
      hindex recurse F le_rfl hFne (Nat.lt_succ_self _) hcommFx
  have hliftIndex
      (heq : Nat.card U =
        4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers xE) U)) :
      Nat.card V = 4 * Nat.card (FixedPoints.subgroup R V) := by
    have hcardU := involution_card_eq_fixed_mul_commutator (V := U) xE hxE
    have hcommU : Nat.card (commutatorAction (Subgroup.zpowers xE) U) = 4 := by
      rw [hcardU, mul_comm 4] at heq
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos heq
    let _ : IsInvariant R V U := isInvariant_of_subgroup_local E R U hRE
    have hactorEq : R.subgroupOf E = Subgroup.zpowers xE := by
      apply Subgroup.map_injective E.subtype_injective
      rw [hmapX]
      exact Subgroup.map_subgroupOf_eq_of_le hRE
    have hlocalEq : commutatorAction (Subgroup.zpowers xE) U =
        commutatorAction R U := by
      rw [← hactorEq, commutatorAction_subgroupOf_eq_local E R U hRE]
    have hmapLe : (commutatorAction R U).map U.subtype ≤ commutatorAction R V := by
      rw [commutatorAction_eq_closure, MonoidHom.map_closure, commutatorAction_eq_closure]
      refine Subgroup.closure_mono ?_
      rintro z ⟨w, ⟨r, u, rfl⟩, rfl⟩
      exact ⟨r, (u : V), rfl⟩
    have hfourLe : 4 ≤ Nat.card (commutatorAction R V) := by
      calc
        4 = Nat.card (commutatorAction R U) := by rw [← hlocalEq, hcommU]
        _ = Nat.card ((commutatorAction R U).map U.subtype) :=
          (Subgroup.card_map_of_injective U.subtype_injective).symm
        _ ≤ Nat.card (commutatorAction R V) := Subgroup.card_le_of_le hmapLe
    have hleFour : Nat.card (commutatorAction R V) ≤ 4 :=
      involution_commutator_card_le_four x hx hindex
    have hcardV := involution_card_eq_fixed_mul_commutator (V := V) x hx
    rw [show Nat.card (commutatorAction R V) = 4 from le_antisymm hleFour hfourLe] at hcardV
    simpa only [mul_comm] using hcardV
  rcases hrec with hsmall | hsmall | hlarge
  · exact Or.inl ⟨hsmall.1, hsmall.2.map (fun f => e.symm.trans f)⟩
  · refine Or.inr (Or.inl ⟨hsmall.1, hliftIndex hsmall.2.1, ?_⟩)
    rcases hsmall.2.2 with h3 | h5 | h9
    · exact Or.inl (h3.map (fun f => e.symm.trans f))
    · exact Or.inr (Or.inl (h5.map (fun f => e.symm.trans f)))
    · exact Or.inr (Or.inr (h9.map (fun f => e.symm.trans f)))
  · refine Or.inr (Or.inr ⟨hlarge.1, hliftIndex hlarge.2.1, ?_,
      extraspecial_of_mulEquiv e hlarge.2.2.2.1,
      (Nat.card_congr e.toEquiv).symm.trans hlarge.2.2.2.2⟩)
    have hm := congrArg (Subgroup.map E.subtype) hlarge.2.2.1
    rw [Subgroup.map_commutator, Subgroup.map_map, hmapX,
      map_center_subgroupOf_eq_centerIn F E hFE, centerIn_eq_map_center,
      Subgroup.map_bot] at hm
    exact hm

end Stellmacher.SectionOne

module

public import FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import Stellmacher.SectionThree.LemmaThreeFour
public import Stellmacher.TwoResidualIdentification

/-!
# The reflected cyclic subgroup in the primitive quotient

This module contains the quotient-level core of Stellmacher's argument in
Lemma (3.6), Journal of Algebra 190 (1997), pp. 22--23. In `P / O₂(P)`,
Lemma (3.3) identifies an odd-prime residual and its Frattini quotient. We
lexicographically minimize first `|F₀[F₀,T]|` and then `|F₀|` among the
actor-invariant subgroups outside that Frattini subgroup. Fixed-point
generation for a noncyclic elementary abelian `2`-group then supplies a
coatom centralizing a reflected line. The two minimality conditions make
that line cyclic and prove that it lies in its commutator with `T`.

`QuotientExtractionData` is the interface to the ambient lifting module: it
records the cyclic odd rotation subgroup, the reflection, its centralizing
coatom, and the non-Frattini and commutator properties needed below.
-/

open scoped IsMulCommutative Pointwise commutatorElement

universe u

@[expose] public section

theorem isCoatom_of_elementaryAbelian_cyclic_quotient''
    {A : Type u} [Group A] [Finite A]
    (hA : IsElementaryAbelian 2 A)
    (Y : Subgroup A) (hYproper : Y ≠ ⊤) (hYcyclic : IsCyclic (A ⧸ Y)) :
    IsCoatom Y := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 A := hA
  let _ : Y.Normal := inferInstance
  have hYelem : IsElementaryAbelian 2 (A ⧸ Y) := by
    refine
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Y q
    have ha2 : a ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a
    simpa only [map_pow, map_one] using congrArg (QuotientGroup.mk' Y) ha2
  let _ : IsElementaryAbelian 2 (A ⧸ Y) := hYelem
  let _ : IsCyclic (A ⧸ Y) := hYcyclic
  let _ : Nontrivial (A ⧸ Y) := QuotientGroup.nontrivial_iff.mpr hYproper
  have hYcardQ : Nat.card (A ⧸ Y) = 2 := by
    rw [← hYcyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_eq_prime
  obtain ⟨M, hMcoat, hYM⟩ :=
    (eq_top_or_exists_le_coatom Y).resolve_left hYproper
  have hAp : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  let _ : Fact (IsPGroup 2 A) := ⟨hAp⟩
  have hMcardQ : Nat.card (A ⧸ M) = 2 :=
    card_quotient_coatom_eq_prime (p := 2) (K := M) hMcoat
  have hcardY : Nat.card A = 2 * Nat.card Y := by
    simpa [hYcardQ] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup Y)
  have hcardM : Nat.card A = 2 * Nat.card M := by
    simpa [hMcardQ] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup M)
  have hcards : Nat.card Y = Nat.card M := by omega
  have hYM_eq : Y = M := Subgroup.eq_of_le_of_card_ge hYM hcards.ge
  simpa [hYM_eq] using hMcoat

theorem odd_pGroup_element_eq_one_of_sq_eq_one
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (K : Subgroup G) (hKp : IsPGroup p K)
    (x : G) (hxK : x ∈ K) (hx2 : x ^ 2 = 1) : x = 1 := by
  have horder2 : orderOf x ∣ 2 := (orderOf_dvd_iff_pow_eq_one).2 hx2
  obtain ⟨n, hn⟩ := hKp.exists_card_eq
  have horderK : orderOf (⟨x, hxK⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
  have horderp : orderOf x ∣ p ^ n := by
    simpa [hn, Subgroup.orderOf_mk] using horderK
  have horder : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hpodd.pow.coprime_two_left horder2 horderp
  exact (orderOf_eq_one_iff).1 horder

theorem exists_fixed_reflection_outside_normal_subgroup
    {G : Type u} [Group G] [Finite G]
    (A K Phi : Subgroup G) [Phi.Normal]
    {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hKp : IsPGroup p K)
    (hAelem : IsElementaryAbelian 2 A)
    (hAnormK : A ≤ Subgroup.normalizer (K : Set G))
    (hKnotPhi : ¬ K ≤ Phi)
    (a : A) (_ha : a ≠ 1)
    (hinverts_mod : ∀ y : G, y ∈ K →
      QuotientGroup.mk' Phi ((a : G) * y * (a : G)⁻¹) =
        (QuotientGroup.mk' Phi y)⁻¹) :
    ∃ Y : Subgroup A, IsCoatom Y ∧ a ∉ Y ∧
      ∃ z : G, z ∈ K ∧ z ∉ Phi ∧
        (∀ b : Y, (b : G) * z * (b : G)⁻¹ = z) ∧
        (a : G) * z * (a : G)⁻¹ = z⁻¹ := by
  classical
  let _ : IsElementaryAbelian 2 A := hAelem
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  let _ : Fact (IsPGroup 2 A) :=
    ⟨IsElementaryAbelian.isPGroup 2 A⟩
  let _ : Subgroup.Normalizes A K := ⟨hAnormK⟩
  let _ : MulDistribMulAction A K :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A K hAnormK
  have hcop : Nat.Coprime 2 (Nat.card K) := by
    obtain ⟨n, hn⟩ := hKp.exists_card_eq
    rw [hn]
    exact hpodd.pow.coprime_two_left
  have hexY : ∃ Y : Subgroup A, IsCyclic (A ⧸ Y) ∧
      ¬ (fixedPointSubgroup Y K).map K.subtype ≤ Phi := by
    by_cases hAcyc : IsCyclic A
    · refine ⟨⊥, ?_, ?_⟩
      · exact (MulEquiv.isCyclic QuotientGroup.quotientBot).2 hAcyc
      · intro hle
        apply hKnotPhi
        intro x hx
        refine hle ⟨⟨x, hx⟩, ?_, rfl⟩
        have hfixbot : fixedPointSubgroup (⊥ : Subgroup A) K = ⊤ := by
          ext k
          simp [FixedPoints.mem_subgroup]
        rw [hfixbot]
        trivial
    · have htop :=
        iSup_fixedPointSubgroup_cyclicQuot_eq_top_of_noncyclic_abelian_pGroup_action
          (G := K) (A := A) (p := 2) hcop hAcyc
      by_contra hall
      push Not at hall
      have hle :
          (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)),
            fixedPointSubgroup Y K) ≤ Phi.comap K.subtype := by
        refine iSup₂_le ?_
        intro Y hY
        exact Subgroup.map_le_iff_le_comap.mp (hall Y hY)
      apply hKnotPhi
      intro x hx
      have hxTop : (⟨x, hx⟩ : K) ∈
          (⊤ : Subgroup K) := trivial
      rw [← htop] at hxTop
      exact hle hxTop
  obtain ⟨Y, hYcyc, hYnotPhi⟩ := hexY
  have haY : a ∉ Y := by
    intro haY
    apply hYnotPhi
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hax : (a : G) * (x : G) * (a : G)⁻¹ = (x : G) := by
      have hfix := (FixedPoints.mem_subgroup (M := Y) (a := x)).1 hx
        ⟨a, haY⟩
      exact congrArg Subtype.val hfix
    have hinv := hinverts_mod (x : G) x.property
    rw [hax] at hinv
    have hsq : (QuotientGroup.mk' Phi (x : G)) ^ 2 = 1 := by
      have hmul := congrArg
        (fun w => w * QuotientGroup.mk' Phi (x : G)) hinv
      calc
        (QuotientGroup.mk' Phi (x : G)) ^ 2 =
            QuotientGroup.mk' Phi (x : G) * QuotientGroup.mk' Phi (x : G) :=
          pow_two _
        _ = (QuotientGroup.mk' Phi (x : G))⁻¹ *
            QuotientGroup.mk' Phi (x : G) := hmul
        _ = 1 := by simp
    let Kbar : Subgroup (G ⧸ Phi) := K.map (QuotientGroup.mk' Phi)
    have hKbarp : IsPGroup p Kbar := IsPGroup.map hKp (QuotientGroup.mk' Phi)
    have hxbarK : QuotientGroup.mk' Phi (x : G) ∈ Kbar :=
      Subgroup.mem_map_of_mem (QuotientGroup.mk' Phi) x.property
    have hxbar1 : QuotientGroup.mk' Phi (x : G) = 1 :=
      odd_pGroup_element_eq_one_of_sq_eq_one hpodd Kbar hKbarp _ hxbarK hsq
    exact (QuotientGroup.eq_one_iff (N := Phi) (x : G)).1 hxbar1
  have hYproper : Y ≠ ⊤ := fun htop => haY (by rw [htop]; trivial)
  have hYcoat : IsCoatom Y :=
    isCoatom_of_elementaryAbelian_cyclic_quotient'' hAelem Y hYproper hYcyc
  obtain ⟨y, hyFix, hyNotPhi⟩ := Set.not_subset.mp hYnotPhi
  rcases hyFix with ⟨yK, hyKFix, rfl⟩
  let z : G := (a : G) * (yK : G) * (a : G)⁻¹ * (yK : G)⁻¹
  have hzK : z ∈ K := by
    exact K.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hAnormK a.property) (yK : G)).1 yK.property)
      (K.inv_mem yK.property)
  have hzNotPhi : z ∉ Phi := by
    intro hzPhi
    have hzbar1 : QuotientGroup.mk' Phi z = 1 :=
      (QuotientGroup.eq_one_iff (N := Phi) z).2 hzPhi
    have hinv := hinverts_mod (yK : G) yK.property
    have hsq : (QuotientGroup.mk' Phi (yK : G)) ^ 2 = 1 := by
      have hzbar : QuotientGroup.mk' Phi z =
          (QuotientGroup.mk' Phi (yK : G))⁻¹ *
            (QuotientGroup.mk' Phi (yK : G))⁻¹ := by
        simpa [z, map_mul, map_inv] using congrArg
          (fun w => w * (QuotientGroup.mk' Phi (yK : G))⁻¹) hinv
      rw [hzbar] at hzbar1
      have h := congrArg Inv.inv hzbar1
      simpa [pow_two] using h
    let Kbar : Subgroup (G ⧸ Phi) := K.map (QuotientGroup.mk' Phi)
    have hKbarp : IsPGroup p Kbar := IsPGroup.map hKp (QuotientGroup.mk' Phi)
    have hybarK : QuotientGroup.mk' Phi (yK : G) ∈ Kbar :=
      Subgroup.mem_map_of_mem (QuotientGroup.mk' Phi) yK.property
    have hybar1 : QuotientGroup.mk' Phi (yK : G) = 1 :=
      odd_pGroup_element_eq_one_of_sq_eq_one hpodd Kbar hKbarp _ hybarK hsq
    exact hyNotPhi ((QuotientGroup.eq_one_iff (N := Phi) (yK : G)).1 hybar1)
  have hzY : ∀ b : Y, (b : G) * z * (b : G)⁻¹ = z := by
    intro b
    have hby : (b : G) * (yK : G) * (b : G)⁻¹ = (yK : G) :=
      congrArg Subtype.val
        ((FixedPoints.mem_subgroup (M := Y) (a := yK)).1 hyKFix b)
    have hba : (b : G) * (a : G) = (a : G) * (b : G) :=
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm b ⟨a, a.property⟩)
    have hconja : (b : G) * (a : G) * (b : G)⁻¹ = (a : G) := by
      calc
        (b : G) * (a : G) * (b : G)⁻¹ =
            (a : G) * (b : G) * (b : G)⁻¹ := by rw [hba]
        _ = a := by simp [mul_assoc]
    have hconjaInv : (b : G) * (a : G)⁻¹ * (b : G)⁻¹ = (a : G)⁻¹ := by
      calc
        (b : G) * (a : G)⁻¹ * (b : G)⁻¹ =
            ((b : G) * (a : G) * (b : G)⁻¹)⁻¹ := by group
        _ = (a : G)⁻¹ := by rw [hconja]
    have hbyInv : (b : G) * (yK : G)⁻¹ * (b : G)⁻¹ = (yK : G)⁻¹ := by
      calc
        (b : G) * (yK : G)⁻¹ * (b : G)⁻¹ =
            ((b : G) * (yK : G) * (b : G)⁻¹)⁻¹ := by group
        _ = (yK : G)⁻¹ := by rw [hby]
    dsimp [z]
    calc
      (b : G) * ((a : G) * (yK : G) * (a : G)⁻¹ * (yK : G)⁻¹) *
          (b : G)⁻¹ =
          ((b : G) * (a : G) * (b : G)⁻¹) *
            ((b : G) * (yK : G) * (b : G)⁻¹) *
            ((b : G) * (a : G)⁻¹ * (b : G)⁻¹) *
            ((b : G) * (yK : G)⁻¹ * (b : G)⁻¹) := by group
      _ = (a : G) * (yK : G) * (a : G)⁻¹ * (yK : G)⁻¹ := by
        rw [hconja, hby, hconjaInv, hbyInv]
  have hza : (a : G) * z * (a : G)⁻¹ = z⁻¹ := by
    have ha2 : (a : G) * (a : G) = 1 := by
      have haPow : a ^ 2 = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A) a
      simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using
        congrArg Subtype.val haPow
    have hainv : (a : G)⁻¹ = (a : G) :=
      (eq_inv_of_mul_eq_one_left ha2).symm
    dsimp [z]
    rw [hainv]
    calc
      (a : G) * ((a : G) * (yK : G) * (a : G) * (yK : G)⁻¹) * (a : G) =
          ((a : G) * (a : G)) * (yK : G) * (a : G) * (yK : G)⁻¹ *
            (a : G) := by group
      _ = (yK : G) * (a : G) * (yK : G)⁻¹ * (a : G) := by rw [ha2, one_mul]
      _ = (yK : G) * (a : G)⁻¹ * (yK : G)⁻¹ * (a : G)⁻¹ := by
        rw [hainv]
      _ = ((a : G) * (yK : G) * (a : G) * (yK : G)⁻¹)⁻¹ := by group
  exact ⟨Y, hYcoat, haY, z, hzK, hzNotPhi, hzY, hza⟩

theorem exists_subgroup_lex_card_minimal'
    {G : Type u} [Group G] [Finite G]
    (Good : Subgroup G → Prop) (score : Subgroup G → ℕ)
    (K : Subgroup G) (hK : Good K) :
    ∃ M : Subgroup G,
      Good M ∧
      (∀ N : Subgroup G, Good N → score M ≤ score N) ∧
      (∀ N : Subgroup G, Good N → score N = score M →
        Nat.card M ≤ Nat.card N) := by
  classical
  have hex : ∃ n : ℕ, ∃ L : Subgroup G, Good L ∧ score L = n :=
    ⟨score K, K, hK, rfl⟩
  let m : ℕ := Nat.find hex
  obtain ⟨M₁, hM₁, hM₁score⟩ := Nat.find_spec hex
  have hexcard : ∃ n : ℕ, ∃ L : Subgroup G,
      Good L ∧ score L = m ∧ Nat.card L = n :=
    ⟨Nat.card M₁, M₁, hM₁, hM₁score, rfl⟩
  let c : ℕ := Nat.find hexcard
  obtain ⟨M, hM, hMscore, hMcard⟩ := Nat.find_spec hexcard
  refine ⟨M, hM, ?_, ?_⟩
  · intro N hN
    have hmle : m ≤ score N := Nat.find_min' hex ⟨N, hN, rfl⟩
    simpa [hMscore] using hmle
  · intro N hN hNscore
    have hcle : c ≤ Nat.card N := by
      apply Nat.find_min' hexcard
      exact ⟨N, hN, hNscore.trans hMscore, rfl⟩
    exact hMcard.le.trans hcle

theorem le_normalizer_commutator_of_le_normalizers'
    {G : Type u} [Group G] {H K N : Subgroup G}
    (hNH : N ≤ Subgroup.normalizer H)
    (hNK : N ≤ Subgroup.normalizer K) :
    N ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.commutator_def, Subgroup.le_normalizer_closure_iff]
  intro n hn x hx
  obtain ⟨h, hh, k, hk, rfl⟩ := hx
  rw [conjugate_commutatorElement]
  exact Subgroup.commutator_mem_commutator
    ((Subgroup.mem_normalizer_iff.mp (hNH hn) h).mp hh)
    ((Subgroup.mem_normalizer_iff.mp (hNK hn) k).mp hk)

theorem subgroup_natCard_mono
    {G : Type u} [Group G] [Finite G] {H K : Subgroup G} (hHK : H ≤ K) :
    Nat.card H ≤ Nat.card K := by
  exact Subgroup.card_le_of_le hHK

theorem coatom_factorization_by_outside_element'
    {G : Type u} [Group G] [Finite G]
    (A₀ : Subgroup G) (a : G)
    {p : ℕ} [Fact p.Prime]
    (hGp : IsPGroup p G) (hcoat : IsCoatom A₀) (ha : a ∉ A₀) :
    (Set.univ : Set G) = (Subgroup.zpowers a : Set G) * (A₀ : Set G) := by
  let _ : Fact (IsPGroup p G) := ⟨hGp⟩
  have hA₀normal : A₀.Normal := coatom_normal_of_isPGroup (p := p) (K := A₀) hcoat
  let _ : A₀.Normal := hA₀normal
  have hsup : Subgroup.zpowers a ⊔ A₀ = ⊤ := by
    rcases (hcoat.le_iff).mp le_sup_right with htop | heq
    · simpa [sup_comm] using htop
    · exfalso
      apply ha
      have : a ∈ Subgroup.zpowers a ⊔ A₀ :=
        (le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ A₀)
          (Subgroup.mem_zpowers a)
      rw [heq] at this
      exact this
  calc
    (Set.univ : Set G) = (↑(Subgroup.zpowers a ⊔ A₀) : Set G) := by rw [hsup]; rfl
    _ = (Subgroup.zpowers a : Set G) * (A₀ : Set G) := Subgroup.mul_normal _ _

theorem exists_lex_minimal_cyclic_reflection
    {G : Type u} [Group G] [Finite G]
    (V Phi A T : Subgroup G) [Phi.Normal]
    {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hVp : IsPGroup p V)
    (hAelem : IsElementaryAbelian 2 A)
    (hAnormV : A ≤ Subgroup.normalizer V)
    (_hAnormT : A ≤ Subgroup.normalizer T)
    (_hTnormV : T ≤ Subgroup.normalizer V)
    (a : A) (ha : a ≠ 1)
    (hFnotPhi : ¬ ⁅V, Subgroup.zpowers (a : G)⁆ ≤ Phi)
    (hinverts_mod : ∀ y : G, y ∈ ⁅V, Subgroup.zpowers (a : G)⁆ →
      QuotientGroup.mk' Phi ((a : G) * y * (a : G)⁻¹) =
        (QuotientGroup.mk' Phi y)⁻¹) :
    ∃ K : Subgroup G, ∃ Y : Subgroup A, ∃ z : G,
      K ≤ ⁅V, Subgroup.zpowers (a : G)⁆ ∧
      A ≤ Subgroup.normalizer K ∧
      ¬ K ≤ Phi ∧
      (∀ N : Subgroup G,
        N ≤ ⁅V, Subgroup.zpowers (a : G)⁆ →
        A ≤ Subgroup.normalizer N → ¬ N ≤ Phi →
        Nat.card (↑(K ⊔ ⁅K, T⁆)) ≤ Nat.card (↑(N ⊔ ⁅N, T⁆))) ∧
      IsCoatom Y ∧ a ∉ Y ∧
      (Set.univ : Set A) = (Subgroup.zpowers a : Set A) * (Y : Set A) ∧
      z ∈ V ∧ z ∉ Phi ∧
      (∀ b : Y, (b : G) * z * (b : G)⁻¹ = z) ∧
      (a : G) * z * (a : G)⁻¹ = z⁻¹ ∧
      K = Subgroup.zpowers z := by
  classical
  let _ : IsElementaryAbelian 2 A := hAelem
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  let F : Subgroup G := ⁅V, Subgroup.zpowers (a : G)⁆
  have hAnormZa : A ≤ Subgroup.normalizer (Subgroup.zpowers (a : G)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have hcomm : (b : G) * (a : G) = (a : G) * (b : G) :=
      congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := A)).comm ⟨b, hb⟩ a)
    change Subgroup.zpowers ((b : G) * (a : G) * (b : G)⁻¹) =
      Subgroup.zpowers (a : G)
    have hconj : (b : G) * (a : G) * (b : G)⁻¹ = (a : G) := by
      rw [hcomm]
      simp [mul_assoc]
    rw [hconj]
  have hAnormF : A ≤ Subgroup.normalizer F :=
    le_normalizer_commutator_of_le_normalizers' hAnormV hAnormZa
  have hFleV : F ≤ V := by
    exact (Subgroup.commutator_mono le_rfl
      (Subgroup.zpowers_le_of_mem a.property)).trans
        ((Subgroup.le_normalizer_iff_commutator_le_left).mp hAnormV)
  let Good : Subgroup G → Prop := fun K =>
    K ≤ F ∧ A ≤ Subgroup.normalizer K ∧ ¬ K ≤ Phi
  let score : Subgroup G → ℕ := fun K => Nat.card (↑(K ⊔ ⁅K, T⁆))
  have hFgood : Good F := ⟨le_rfl, hAnormF, hFnotPhi⟩
  obtain ⟨K, hKgood, hKscore, hKcard⟩ :=
    exists_subgroup_lex_card_minimal' Good score F hFgood
  have hKleV : K ≤ V := hKgood.1.trans hFleV
  have hKp : IsPGroup p K := IsPGroup.to_le hVp hKleV
  obtain ⟨Y, hYcoat, haY, z, hzK, hzPhi, hzY, hza⟩ :=
    exists_fixed_reflection_outside_normal_subgroup A K Phi hpodd hKp
      hAelem hKgood.2.1 hKgood.2.2 a ha
      (fun y hy => hinverts_mod y (hKgood.1 hy))
  let _ : Subgroup.Normalizes A K := ⟨hKgood.2.1⟩
  let C : Subgroup G := (fixedPointSubgroup Y K).map K.subtype
  have hCleK : C ≤ K := by
    intro c hc
    obtain ⟨k, _hk, rfl⟩ := hc
    exact k.property
  have hAnormC : A ≤ Subgroup.normalizer C := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg c hc
    obtain ⟨k, hkFix, rfl⟩ := hc
    have hgkK : (g : G) * (k : G) * (g : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hKgood.2.1 hg) (k : G)).mp k.property
    refine ⟨⟨(g : G) * (k : G) * (g : G)⁻¹, hgkK⟩, ?_, rfl⟩
    change ∀ y : Y, y •
      (⟨(g : G) * (k : G) * (g : G)⁻¹, hgkK⟩ : K) =
        ⟨(g : G) * (k : G) * (g : G)⁻¹, hgkK⟩
    intro y
    apply Subtype.ext
    have hyk := congrArg Subtype.val
      ((FixedPoints.mem_subgroup (M := Y) (a := k)).1 hkFix y)
    change (y : G) * (k : G) * (y : G)⁻¹ = (k : G) at hyk
    have hyg : (y : G) * (g : G) = (g : G) * (y : G) :=
      congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := A)).comm
          ⟨(y : G), (y : A).property⟩ ⟨g, hg⟩)
    have hinvComm : (g : G)⁻¹ * (y : G)⁻¹ =
        (y : G)⁻¹ * (g : G)⁻¹ := by
      simpa using congrArg Inv.inv hyg
    change (y : G) * ((g : G) * (k : G) * (g : G)⁻¹) * (y : G)⁻¹ =
      (g : G) * (k : G) * (g : G)⁻¹
    calc
      (y : G) * ((g : G) * (k : G) * (g : G)⁻¹) * (y : G)⁻¹ =
          ((y : G) * (g : G)) * (k : G) * ((g : G)⁻¹ * (y : G)⁻¹) := by
            group
      _ = ((g : G) * (y : G)) * (k : G) *
          ((y : G)⁻¹ * (g : G)⁻¹) := by rw [hyg, hinvComm]
      _ = (g : G) * ((y : G) * (k : G) * (y : G)⁻¹) * (g : G)⁻¹ := by
        group
      _ = (g : G) * (k : G) * (g : G)⁻¹ := by rw [hyk]
  have hzC : z ∈ C := by
    refine ⟨⟨z, hzK⟩, ?_, rfl⟩
    change ∀ b : Y, b • (⟨z, hzK⟩ : K) = ⟨z, hzK⟩
    intro b
    apply Subtype.ext
    change (b : G) * z * (b : G)⁻¹ = z
    exact hzY b
  have hCnotPhi : ¬ C ≤ Phi := fun h => hzPhi (h hzC)
  have hCgood : Good C :=
    ⟨hCleK.trans hKgood.1, hAnormC, hCnotPhi⟩
  have hCscoreLe : score C ≤ score K := by
    apply subgroup_natCard_mono
    exact sup_le_sup hCleK (Subgroup.commutator_mono hCleK le_rfl)
  have hscoreEq : score C = score K :=
    Nat.le_antisymm hCscoreLe (hKscore C hCgood)
  have hCKeq : C = K :=
    Subgroup.eq_of_le_of_card_ge hCleK (hKcard C hCgood hscoreEq)
  have hfactor : (Set.univ : Set A) =
      (Subgroup.zpowers a : Set A) * (Y : Set A) :=
    coatom_factorization_by_outside_element' Y a
      (IsElementaryAbelian.isPGroup 2 A) hYcoat haY
  have hAnormZ : A ≤ Subgroup.normalizer (Subgroup.zpowers z) := by
    intro g hg
    have hgUniv : (⟨g, hg⟩ : A) ∈ (Set.univ : Set A) := trivial
    rw [hfactor] at hgUniv
    obtain ⟨r, hr, b, hb, hrbg⟩ := hgUniv
    have haNorm : (a : G) ∈ Subgroup.normalizer (Subgroup.zpowers z) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      change Subgroup.zpowers ((a : G) * z * (a : G)⁻¹) = Subgroup.zpowers z
      rw [hza]
      exact Subgroup.zpowers_inv
    have hrNormA : r ∈ Subgroup.zpowers a := hr
    have hrNorm : (r : G) ∈ Subgroup.normalizer (Subgroup.zpowers z) := by
      have hrAmbient : (r : G) ∈ Subgroup.zpowers (a : G) := by
        have := Subgroup.mem_map_of_mem A.subtype hrNormA
        rw [MonoidHom.map_zpowers] at this
        change A.subtype r ∈ Subgroup.zpowers (A.subtype a)
        exact this
      exact (Subgroup.zpowers_le_of_mem haNorm) hrAmbient
    have hbNorm : (b : G) ∈ Subgroup.normalizer (Subgroup.zpowers z) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      change Subgroup.zpowers ((b : G) * z * (b : G)⁻¹) = Subgroup.zpowers z
      rw [hzY ⟨b, hb⟩]
    have hcoe : (g : G) = (r : G) * (b : G) := by
      exact congrArg Subtype.val hrbg.symm
    have hmulNorm : (r : G) * (b : G) ∈
        Subgroup.normalizer (Subgroup.zpowers z) :=
      @Subgroup.mul_mem G _
        (Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G))
        (r : G) (b : G) hrNorm hbNorm
    rw [hcoe]
    exact hmulNorm
  have hZleK : Subgroup.zpowers z ≤ K := Subgroup.zpowers_le_of_mem hzK
  have hZgood : Good (Subgroup.zpowers z) :=
    ⟨hZleK.trans hKgood.1, hAnormZ, fun h => hzPhi (h (Subgroup.mem_zpowers z))⟩
  have hZscoreLe : score (Subgroup.zpowers z) ≤ score K := by
    apply subgroup_natCard_mono
    exact sup_le_sup hZleK (Subgroup.commutator_mono hZleK le_rfl)
  have hZscoreEq : score (Subgroup.zpowers z) = score K :=
    Nat.le_antisymm hZscoreLe (hKscore (Subgroup.zpowers z) hZgood)
  have hZK : Subgroup.zpowers z = K :=
    Subgroup.eq_of_le_of_card_ge hZleK
      (hKcard (Subgroup.zpowers z) hZgood hZscoreEq)
  refine ⟨K, Y, z, hKgood.1, hKgood.2.1, hKgood.2.2, ?_, hYcoat,
    haY, hfactor, hKleV hzK, hzPhi, hzY, hza, hZK.symm⟩
  intro N hNF hAN hNPhi
  exact hKscore N ⟨hNF, hAN, hNPhi⟩

theorem reflected_commutator_not_le_normal_subgroup
    {G : Type u} [Group G] [Finite G]
    (K M Phi : Subgroup G) [Phi.Normal]
    {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hKp : IsPGroup p K)
    (a : G) (hKnotPhi : ¬ K ≤ Phi)
    (hinverts : ∀ k : G, k ∈ K →
      QuotientGroup.mk' Phi (a * k * a⁻¹) =
        (QuotientGroup.mk' Phi k)⁻¹)
    (hKM : K ≤ M ⊔ Phi) :
    ¬ ⁅M, Subgroup.zpowers a⁆ ≤ Phi := by
  classical
  let q : G →* G ⧸ Phi := QuotientGroup.mk' Phi
  intro hcommPhi
  have hmapKleM : K.map q ≤ M.map q := by
    calc
      K.map q ≤ (M ⊔ Phi).map q := Subgroup.map_mono hKM
      _ = M.map q ⊔ Phi.map q := Subgroup.map_sup M Phi q
      _ = M.map q := by rw [QuotientGroup.map_mk'_self, sup_bot_eq]
  have hcommMapBot : ⁅M.map q, Subgroup.zpowers (q a)⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator]
    exact (Subgroup.map_mono hcommPhi).trans (by simp [q])
  have haCentralM : q a ∈ Subgroup.centralizer (M.map q : Set (G ⧸ Phi)) := by
    have hswap : ⁅Subgroup.zpowers (q a), M.map q⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hcommMapBot
    have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hswap)
    exact hle (Subgroup.mem_zpowers (q a))
  apply hKnotPhi
  intro k hk
  have hqkM : q k ∈ M.map q := hmapKleM (Subgroup.mem_map_of_mem q hk)
  have hcommute : q a * q k = q k * q a :=
    (Subgroup.mem_centralizer_iff.mp haCentralM (q k) hqkM).symm
  have hfix : q a * q k * (q a)⁻¹ = q k := by
    rw [hcommute]
    simp [mul_assoc]
  have hinv : q a * q k * (q a)⁻¹ = (q k)⁻¹ := by
    simpa [q] using hinverts k hk
  have hselfInv : q k = (q k)⁻¹ := hfix.symm.trans hinv
  have hsq : (q k) ^ 2 = 1 := by
    have hmul := congrArg (fun w => w * q k) hselfInv
    calc
      (q k) ^ 2 = q k * q k := pow_two _
      _ = (q k)⁻¹ * q k := hmul
      _ = 1 := by simp
  let Kbar : Subgroup (G ⧸ Phi) := K.map q
  have hKbarp : IsPGroup p Kbar := IsPGroup.map hKp q
  have hqkKbar : q k ∈ Kbar := Subgroup.mem_map_of_mem q hk
  have hqk1 : q k = 1 :=
    odd_pGroup_element_eq_one_of_sq_eq_one hpodd Kbar hKbarp _ hqkKbar hsq
  exact (QuotientGroup.eq_one_iff (N := Phi) k).1 hqk1

theorem commutator_sup_commutator_le_self''
    {G : Type u} [Group G] (K T : Subgroup G) :
    ⁅K ⊔ ⁅K, T⁆, T⁆ ≤ ⁅K, T⁆ := by
  let C : Subgroup G := ⁅K, T⁆
  have hKnormC : K ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.normalizer_commutator_ge_left K T
  have hTnormC : T ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.normalizer_commutator_ge_right K T
  rw [Subgroup.commutator_le]
  intro x hx t ht
  have hcarrier : (↑(K ⊔ C) : Set G) = (K : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K C hKnormC
  change x ∈ (↑(K ⊔ C) : Set G) at hx
  rw [hcarrier] at hx
  obtain ⟨k, hk, c, hc, rfl⟩ := hx
  have hct : ⁅c, t⁆ ∈ C := by
    have htNorm : t ∈ Subgroup.normalizer (C : Set G) := hTnormC ht
    have hconj : t * c⁻¹ * t⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp htNorm c⁻¹).1 (C.inv_mem hc)
    simpa [C, commutatorElement_def, mul_assoc] using C.mul_mem hc hconj
  have hkct : k * ⁅c, t⁆ * k⁻¹ ∈ C :=
    (Subgroup.mem_normalizer_iff.mp (hKnormC hk) ⁅c, t⁆).1 hct
  have hkt : ⁅k, t⁆ ∈ C := Subgroup.commutator_mem_commutator hk ht
  have hprod : (k * ⁅c, t⁆ * k⁻¹) * ⁅k, t⁆ ∈ C := C.mul_mem hkct hkt
  have hid : ⁅k * c, t⁆ = (k * ⁅c, t⁆ * k⁻¹) * ⁅k, t⁆ := by
    simp only [commutatorElement_def]
    group
  simpa [C, hid] using hprod

theorem exists_lex_minimal_cyclic_reflection_commutator
    {G : Type u} [Group G] [Finite G]
    (V Phi A T : Subgroup G) [Phi.Normal]
    {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hVp : IsPGroup p V)
    (hAelem : IsElementaryAbelian 2 A)
    (hAnormV : A ≤ Subgroup.normalizer V)
    (hAnormT : A ≤ Subgroup.normalizer T)
    (hTnormV : T ≤ Subgroup.normalizer V)
    (a : A) (ha : a ≠ 1)
    (hFnotPhi : ¬ ⁅V, Subgroup.zpowers (a : G)⁆ ≤ Phi)
    (hinverts_mod : ∀ y : G, y ∈ ⁅V, Subgroup.zpowers (a : G)⁆ →
      QuotientGroup.mk' Phi ((a : G) * y * (a : G)⁻¹) =
        (QuotientGroup.mk' Phi y)⁻¹)
    (huniversal : ∀ K : Subgroup G, K ≤ V → K ≤ ⁅K, T⁆ ⊔ Phi) :
    ∃ K : Subgroup G, ∃ Y : Subgroup A, ∃ z : G,
      K ≤ ⁅V, Subgroup.zpowers (a : G)⁆ ∧
      A ≤ Subgroup.normalizer K ∧
      ¬ K ≤ Phi ∧
      IsCoatom Y ∧ a ∉ Y ∧
      (Set.univ : Set A) = (Subgroup.zpowers a : Set A) * (Y : Set A) ∧
      z ∈ V ∧ z ∉ Phi ∧
      (∀ b : Y, (b : G) * z * (b : G)⁻¹ = z) ∧
      (a : G) * z * (a : G)⁻¹ = z⁻¹ ∧
      K = Subgroup.zpowers z ∧ K ≤ ⁅K, T⁆ := by
  classical
  obtain ⟨K, Y, z, hKF, hAnormK, hKPhi, hKmin, hYcoat, haY,
      hfactor, hzV, hzPhi, hzY, hza, hKcyc⟩ :=
    exists_lex_minimal_cyclic_reflection V Phi A T hpodd hVp hAelem
      hAnormV hAnormT hTnormV a ha hFnotPhi hinverts_mod
  let M : Subgroup G := ⁅K, T⁆
  let F₁ : Subgroup G := ⁅M, Subgroup.zpowers (a : G)⁆
  have hKleV : K ≤ V := hKF.trans
    ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le_of_mem a.property)).trans
      ((Subgroup.le_normalizer_iff_commutator_le_left).mp hAnormV))
  have hKp : IsPGroup p K := IsPGroup.to_le hVp hKleV
  have hKMphi : K ≤ M ⊔ Phi := huniversal K hKleV
  have hF₁notPhi : ¬ F₁ ≤ Phi :=
    reflected_commutator_not_le_normal_subgroup K M Phi hpodd hKp (a : G)
      hKPhi (fun k hk => hinverts_mod k (hKF hk)) hKMphi
  have hMleV : M ≤ V := by
    exact (Subgroup.commutator_mono hKleV le_rfl).trans
      ((Subgroup.le_normalizer_iff_commutator_le_left).mp hTnormV)
  have hF₁leF : F₁ ≤ ⁅V, Subgroup.zpowers (a : G)⁆ :=
    Subgroup.commutator_mono hMleV le_rfl
  have hAnormM : A ≤ Subgroup.normalizer M :=
    le_normalizer_commutator_of_le_normalizers' hAnormK hAnormT
  have hAnormZa : A ≤ Subgroup.normalizer (Subgroup.zpowers (a : G)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have hcomm : (b : G) * (a : G) = (a : G) * (b : G) :=
      congrArg Subtype.val
        ((hAelem.toIsMulCommutative.is_comm).comm ⟨b, hb⟩ a)
    change Subgroup.zpowers ((b : G) * (a : G) * (b : G)⁻¹) =
      Subgroup.zpowers (a : G)
    rw [hcomm]
    simp [mul_assoc]
  have hAnormF₁ : A ≤ Subgroup.normalizer F₁ :=
    le_normalizer_commutator_of_le_normalizers' hAnormM hAnormZa
  have hZaNormM : Subgroup.zpowers (a : G) ≤ Subgroup.normalizer M :=
    (Subgroup.zpowers_le_of_mem (hAnormM a.property))
  have hF₁leM : F₁ ≤ M :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hZaNormM
  have hMTleM : ⁅M, T⁆ ≤ M := by
    exact (Subgroup.commutator_mono
      (le_sup_right : M ≤ K ⊔ M) le_rfl).trans
        (commutator_sup_commutator_le_self'' K T)
  have hF₁TleM : ⁅F₁, T⁆ ≤ M :=
    (Subgroup.commutator_mono hF₁leM le_rfl).trans hMTleM
  have hF₁scoreLeM : F₁ ⊔ ⁅F₁, T⁆ ≤ M := sup_le hF₁leM hF₁TleM
  have hfirst : Nat.card (↑(K ⊔ M)) ≤ Nat.card (↑(F₁ ⊔ ⁅F₁, T⁆)) :=
    hKmin F₁ hF₁leF hAnormF₁ hF₁notPhi
  have hsmall : F₁ ⊔ ⁅F₁, T⁆ ≤ K ⊔ M :=
    hF₁scoreLeM.trans le_sup_right
  have heq : F₁ ⊔ ⁅F₁, T⁆ = K ⊔ M :=
    Subgroup.eq_of_le_of_card_ge hsmall hfirst
  have hKleM : K ≤ M := by
    exact (le_sup_left : K ≤ K ⊔ M).trans (heq.ge.trans hF₁scoreLeM)
  exact ⟨K, Y, z, hKF, hAnormK, hKPhi, hYcoat, haY, hfactor,
    hzV, hzPhi, hzY, hza, hKcyc, hKleM⟩

theorem fixedPointSubgroup_eq_bot_of_commutator_eq_self
    {G : Type u} [Group G] [Finite G]
    (V T : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hVelem : IsElementaryAbelian p V)
    (hTtwo : IsPGroup 2 T)
    (hTnormV : T ≤ Subgroup.normalizer (V : Set G))
    (hcomm : ⁅V, T⁆ = V) :
    let _ : Subgroup.Normalizes T V := ⟨hTnormV⟩
    fixedPointSubgroup T V = ⊥ := by
  classical
  dsimp only
  let _ : Subgroup.Normalizes T V := ⟨hTnormV⟩
  let _ : IsMulCommutative V := hVelem.toIsMulCommutative
  have hVp : IsPGroup p V := IsElementaryAbelian.isPGroup p V
  have hpne : 2 ≠ p := by
    intro h
    subst p
    obtain ⟨n, hn⟩ := hpodd
    omega
  have hcop : Nat.Coprime (Nat.card T) (Nat.card V) := by
    simpa using
      IsPGroup.coprime_card_of_ne 2 p hpne
        (⊤ : Subgroup T) (⊤ : Subgroup V)
        (hTtwo.to_subgroup ⊤) (hVp.to_subgroup ⊤)
  have hVsolv : Group.IsSolvable V := by infer_instance
  have hcompl : IsCompl (fixedPointSubgroup T V)
      (commutatorAction (A := T) (G := V)) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      hVsolv hcop hVelem.toIsMulCommutative
  have hmapComm :
      (commutatorAction (A := T) (G := V)).map V.subtype = ⁅V, T⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator V T hTnormV
  have hcommTop : commutatorAction (A := T) (G := V) = ⊤ := by
    apply Subgroup.map_injective_of_ker_le V.subtype (by simp) (by simp)
    rw [hmapComm, hcomm]
    simp [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simpa [hcommTop] using hcompl.inf_eq_bot

theorem subgroup_le_commutator_sup_kernel_of_fixedPointSubgroup_eq_bot
    {G : Type u} [Group G] [Finite G]
    (V T K N : Subgroup G) [N.Normal]
    {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p)
    (hVbarElem : IsElementaryAbelian p (V.map (QuotientGroup.mk' N)))
    (hTtwo : IsPGroup 2 T)
    (hTnormV : T ≤ Subgroup.normalizer (V : Set G))
    (hfixed :
      let Vbar : Subgroup (G ⧸ N) := V.map (QuotientGroup.mk' N)
      let Tbar : Subgroup (G ⧸ N) := T.map (QuotientGroup.mk' N)
      let hTbarNormVbar : Tbar ≤ Subgroup.normalizer (Vbar : Set (G ⧸ N)) := by
        rw [Subgroup.le_normalizer_iff_commutator_le_left]
        rw [← Subgroup.map_commutator]
        exact Subgroup.map_mono
          ((Subgroup.le_normalizer_iff_commutator_le_left).1 hTnormV)
      let _ : Subgroup.Normalizes Tbar Vbar := ⟨hTbarNormVbar⟩
      fixedPointSubgroup Tbar Vbar = ⊥)
    (hKV : K ≤ V) :
    K ≤ ⁅K, T⁆ ⊔ N := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Vbar : Subgroup (G ⧸ N) := V.map q
  let Tbar : Subgroup (G ⧸ N) := T.map q
  let Kbar : Subgroup (G ⧸ N) := K.map q
  have hTbarTwo : IsPGroup 2 Tbar := IsPGroup.map hTtwo q
  have hTbarNormVbar : Tbar ≤ Subgroup.normalizer (Vbar : Set (G ⧸ N)) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono
      ((Subgroup.le_normalizer_iff_commutator_le_left).1 hTnormV)
  have hKbarVbar : Kbar ≤ Vbar := Subgroup.map_mono hKV
  have hbar : Kbar ≤ ⁅Kbar, Tbar⁆ := by
    let _ : Subgroup.Normalizes Tbar Vbar := ⟨hTbarNormVbar⟩
    let C : Subgroup (G ⧸ N) := ⁅Kbar, Tbar⁆
    let W : Subgroup (G ⧸ N) := Kbar ⊔ C
    have hcommWT : ⁅W, Tbar⁆ ≤ C := by
      simpa [W, C] using commutator_sup_commutator_le_self'' Kbar Tbar
    have hTnormW : Tbar ≤ Subgroup.normalizer (W : Set (G ⧸ N)) :=
      (Subgroup.le_normalizer_iff_commutator_le_left).2
        (hcommWT.trans (le_sup_right : C ≤ W))
    have hCleV : C ≤ Vbar :=
      (Subgroup.commutator_mono hKbarVbar le_rfl).trans
        ((Subgroup.le_normalizer_iff_commutator_le_left).1 hTbarNormVbar)
    have hWleV : W ≤ Vbar := sup_le hKbarVbar hCleV
    have hWp : IsPGroup p W :=
      IsPGroup.to_le (IsElementaryAbelian.isPGroup p Vbar) hWleV
    have hWcomm : IsMulCommutative W := by
      let _ : IsMulCommutative Vbar := hVbarElem.toIsMulCommutative
      exact ⟨⟨fun x y => by
        apply W.subtype_injective
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := Vbar)).comm
            (⟨x, hWleV x.property⟩ : Vbar)
            (⟨y, hWleV y.property⟩ : Vbar))⟩⟩
    have hpne : 2 ≠ p := by
      intro h
      subst p
      obtain ⟨n, hn⟩ := hpodd
      omega
    have hcop : Nat.Coprime (Nat.card Tbar) (Nat.card W) := by
      simpa using
        IsPGroup.coprime_card_of_ne 2 p hpne
          (⊤ : Subgroup Tbar) (⊤ : Subgroup W)
          (hTbarTwo.to_subgroup ⊤) (hWp.to_subgroup ⊤)
    let _ : Subgroup.Normalizes Tbar W := ⟨hTnormW⟩
    have hfixedW : fixedPointSubgroup Tbar W = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxV : (⟨(x : G ⧸ N), hWleV x.property⟩ : Vbar) ∈
          fixedPointSubgroup Tbar Vbar := by
        rw [FixedPoints.mem_subgroup]
        intro t
        have hxt := (FixedPoints.mem_subgroup (M := Tbar) (a := x)).1 hx t
        apply Subtype.ext
        have hcoe := congrArg Subtype.val hxt
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hTbarNormVbar, hTnormW] using hcoe
      rw [hfixed] at hxV
      have hxone : (⟨(x : G ⧸ N), hWleV x.property⟩ : Vbar) = 1 := by
        simpa using hxV
      have hxQ : (x : G ⧸ N) = 1 := congrArg Subtype.val hxone
      have hxW : x = 1 := Subtype.ext hxQ
      simpa using hxW
    have hWsolv : Group.IsSolvable W := by
      let _ : IsMulCommutative W := hWcomm
      infer_instance
    have hcompl : IsCompl (fixedPointSubgroup Tbar W)
        (commutatorAction (A := Tbar) (G := W)) :=
      isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        hWsolv hcop hWcomm
    have hcommTop : commutatorAction (A := Tbar) (G := W) = ⊤ := by
      have hsup := hcompl.sup_eq_top
      simpa [hfixedW] using hsup
    have hmapComm :
        (commutatorAction (A := Tbar) (G := W)).map W.subtype = ⁅W, Tbar⁆ :=
      commutatorAction_subgroup_conj_map_eq_commutator W Tbar hTnormW
    have hWeq : W = ⁅W, Tbar⁆ := by
      rw [hcommTop] at hmapComm
      simpa [← MonoidHom.range_eq_map, Subgroup.range_subtype] using hmapComm
    exact (le_sup_left : Kbar ≤ W).trans (hWeq.le.trans hcommWT)
  have hbar' : K.map q ≤ (⁅K, T⁆).map q := by
    simpa [Kbar, Tbar, q, Subgroup.map_commutator] using hbar
  have hcomap : K ≤ ((⁅K, T⁆).map q).comap q :=
    (Subgroup.map_le_iff_le_comap).1 hbar'
  simpa [q, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] using hcomap

theorem elementaryAbelian_range_of_frattini_le_ker
    {X Y : Type*} [Group X] [Finite X] [Group Y]
    {p : ℕ} [Fact p.Prime]
    (f : X →* Y) (hXp : IsPGroup p X)
    (hPhi : frattini X ≤ f.ker) :
    IsElementaryAbelian p f.range := by
  classical
  let _ : Fact (IsPGroup p X) := ⟨hXp⟩
  let fbar : X ⧸ frattini X →* Y :=
    QuotientGroup.lift (frattini X) f hPhi
  have hsource : IsElementaryAbelian p (X ⧸ frattini X) :=
    isElementaryAbelian_quotient_frattini (R := X) (p := p)
  let _ : IsElementaryAbelian p (X ⧸ frattini X) := hsource
  have htop : IsElementaryAbelian p (⊤ : Subgroup (X ⧸ frattini X)) := by
    refine
      { toIsMulCommutative := ⟨⟨?_⟩⟩
        exponent_dvd_p := ?_ }
    · intro a b
      apply Subtype.ext
      exact (IsMulCommutative.is_comm (M := X ⧸ frattini X)).comm
        (a : X ⧸ frattini X) (b : X ⧸ frattini X)
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro x
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p (X ⧸ frattini X)) x
  let _ : IsElementaryAbelian p (⊤ : Subgroup (X ⧸ frattini X)) := htop
  have himage : IsElementaryAbelian p
      ((⊤ : Subgroup (X ⧸ frattini X)).map fbar) :=
    IsElementaryAbelian.map fbar
  have hrange : (⊤ : Subgroup (X ⧸ frattini X)).map fbar = f.range := by
    ext y
    constructor
    · rintro ⟨z, _hz, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini X) z
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨QuotientGroup.mk' (frattini X) x, trivial, by simp [fbar]⟩
  rw [hrange] at himage
  exact himage

theorem image_of_subgroup_eq_range_comp_subtype
    {X Y : Type*} [Group X] [Group Y]
    (H : Subgroup X) (f : X →* Y) :
    H.map f = (f.comp H.subtype).range := by
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range, MonoidHom.comp_apply,
    Subgroup.subtype_apply, Subtype.exists, exists_prop]

theorem zpowers_mem_cases_of_isInvolution'
    {G : Type u} [Group G] [Finite G] {a b : G}
    (ha : IsInvolution a) (hb : b ∈ Subgroup.zpowers a) :
    b = 1 ∨ b = a := by
  have haOrder : orderOf a = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using ha.2) ha.1
  let H : Subgroup G := Subgroup.zpowers a
  have hcard : Nat.card H = 2 := by rw [Nat.card_zpowers, haOrder]
  rcases (Nat.card_eq_two_iff' (1 : H)).mp hcard with ⟨y, hyne, hyuniq⟩
  let bH : H := ⟨b, hb⟩
  let aH : H := ⟨a, Subgroup.mem_zpowers a⟩
  have haHne : aH ≠ 1 := fun h => ha.1 (congrArg Subtype.val h)
  have haHy : aH = y := hyuniq aH haHne
  by_cases hbHone : bH = 1
  · exact Or.inl (congrArg Subtype.val hbHone)
  · exact Or.inr (congrArg Subtype.val ((hyuniq bH hbHone).trans haHy.symm))

theorem involution_inverts_commutator_with_zpowers'
    {G : Type u} [Group G] [Finite G]
    (V : Subgroup G) {a : G}
    (ha : IsInvolution a)
    (hanormV : a ∈ Subgroup.normalizer (V : Set G))
    (hVcomm : IsMulCommutative V) :
    ∀ x : G, x ∈ ⁅V, Subgroup.zpowers a⁆ →
      a * x * a⁻¹ = x⁻¹ := by
  let I : Subgroup G :=
    { carrier := {x : G | x ∈ V ∧ a * x * a⁻¹ = x⁻¹}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        refine ⟨V.mul_mem hx.1 hy.1, ?_⟩
        have hxy : x * y = y * x :=
          congrArg Subtype.val
            ((hVcomm.is_comm).comm (⟨x, hx.1⟩ : V) (⟨y, hy.1⟩ : V))
        calc
          a * (x * y) * a⁻¹ =
              (a * x * a⁻¹) * (a * y * a⁻¹) := by group
          _ = x⁻¹ * y⁻¹ := by rw [hx.2, hy.2]
          _ = (x * y)⁻¹ := by simp [hxy]
      inv_mem' := by
        intro x hx
        refine ⟨V.inv_mem hx.1, ?_⟩
        have h := congrArg Inv.inv hx.2
        simpa [mul_assoc] using h }
  have hcommI : ⁅V, Subgroup.zpowers a⁆ ≤ I := by
    rw [Subgroup.commutator_le]
    intro v hv b hb
    rcases zpowers_mem_cases_of_isInvolution' ha hb with hb1 | hba
    · subst b
      simp [I]
    · subst b
      have hava : a * v * a⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp hanormV v).1 hv
      refine ⟨?_, ?_⟩
      · have hconj : a * v⁻¹ * a⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp hanormV v⁻¹).1 (V.inv_mem hv)
        simpa [commutatorElement_def, mul_assoc] using V.mul_mem hv hconj
      · have ha2 : a * a = 1 := by simpa [pow_two] using ha.2
        have hainv : a⁻¹ = a := (eq_inv_of_mul_eq_one_left ha2).symm
        simp only [commutatorElement_def]
        calc
          a * (v * a * v⁻¹ * a⁻¹) * a⁻¹ =
              (a * v * a⁻¹) * v⁻¹ * (a * a) := by rw [hainv]; group
          _ = (a * v * a⁻¹) * v⁻¹ := by rw [ha2, mul_one]
          _ = (v * a * v⁻¹ * a⁻¹)⁻¹ := by
            simp only [mul_inv_rev, inv_inv]
            rw [hainv]
            group
  intro x hx
  exact (hcommI hx).2

end

namespace Stellmacher.SectionThree

@[expose] public section


structure QuotientExtractionData
    {G : Type u} [Group G] [Finite G]
    (P T A : Subgroup G) (P₀ : Subgroup P)
    (hTP : T ≤ P) (hAP : A ≤ P)
    (a : G) (haA : a ∈ A) where
  p : ℕ
  prime_p : p.Prime
  odd_p : Odd p
  K : Subgroup (P ⧸ pCore 2 P)
  Y : Subgroup ((A.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)))
  z : P ⧸ pCore 2 P
  z_mem_residual : z ∈
    twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P))
  z_not_residual_frattini :
    (⟨z, z_mem_residual⟩ :
      twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P))) ∉
        frattini (twoResidualAmbient
          (⊤ : Subgroup (P ⧸ pCore 2 P)))
  residual_pgroup : IsPGroup p
    (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)))
  K_cyclic : K = Subgroup.zpowers z
  K_pgroup : IsPGroup p K
  actor_two : IsPGroup 2
    ((A.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)))
  actor_elementary : IsElementaryAbelian 2
    ((A.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)))
  actor_normalizes_K :
    (A.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)) ≤
      Subgroup.normalizer K
  K_not_phi : ¬ K ≤ P₀.map (QuotientGroup.mk' (pCore 2 P))
  K_not_residual_frattini : ¬ K ≤
    frattiniAmbient
      (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)))
  Y_coatom : IsCoatom Y
  reflection_not_Y :
    (⟨QuotientGroup.mk' (pCore 2 P) ⟨a, hAP haA⟩,
      Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 P))
        (show ⟨a, hAP haA⟩ ∈ A.subgroupOf P from haA)⟩ :
      (A.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P))) ∉ Y
  actor_factor :
    (Set.univ : Set ((A.subgroupOf P).map
      (QuotientGroup.mk' (pCore 2 P)))) =
      (Subgroup.zpowers
        (⟨QuotientGroup.mk' (pCore 2 P) ⟨a, hAP haA⟩,
          Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 P))
            (show ⟨a, hAP haA⟩ ∈ A.subgroupOf P from haA)⟩ :
          (A.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P))) : Set _) *
        (Y : Set _)
  reflected : ∀ r : P ⧸ pCore 2 P, r ∈ K →
    QuotientGroup.mk' (pCore 2 P) ⟨a, hAP haA⟩ * r *
      (QuotientGroup.mk' (pCore 2 P) ⟨a, hAP haA⟩)⁻¹ = r⁻¹
  reflection_involution : IsInvolution
    (QuotientGroup.mk' (pCore 2 P) ⟨a, hAP haA⟩)
  Y_centralizes : ∀ b : Y,
    (b : P ⧸ pCore 2 P) * z * (b : P ⧸ pCore 2 P)⁻¹ = z
  K_commutator : K ≤ ⁅K,
    (T.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P))⁆

noncomputable def quotientExtractionData_of_not_central
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hSP : S ≤ P)
    (B : Subgroup P)
    (hB : IsCoatom B ∧ S.subgroupOf P ≤ B ∧
      ∀ B' : Subgroup P, IsCoatom B' → S.subgroupOf P ≤ B' → B' = B)
    (T : Subgroup G) (hT : T ≤ S ∧ (T.subgroupOf S).Normal)
    (A : Subgroup G) (hA : A ≤ S)
    (a : G) (haA : a ∈ A) (haCore : a ∉ twoCoreAmbient P)
    (hPhiA : frattiniAmbient A ≤ twoCoreAmbient P)
    (hsolv : Group.IsSolvable P)
    (hTcore : ¬ T ≤ twoCoreAmbient P)
    (hnoncentral :
      let q₀ : P →* P ⧸ B.normalCore := QuotientGroup.mk' B.normalCore
      q₀ ⟨a, hSP (hA haA)⟩ ∉
        Subgroup.centralizer
          (twoResidualAmbient (⊤ : Subgroup (P ⧸ B.normalCore)) :
            Set (P ⧸ B.normalCore))) :
    QuotientExtractionData P T A B.normalCore
      (hT.1.trans hSP) (hA.trans hSP) a haA := by
  classical
  have hTP : T ≤ P := hT.1.trans hSP
  have hAP : A ≤ P := hA.trans hSP
  let SP : Subgroup P := S.subgroupOf P
  let TP : Subgroup P := T.subgroupOf P
  let AP : Subgroup P := A.subgroupOf P
  let P₀ : Subgroup P := B.normalCore
  have hP₀data : P₀ ≤ B ∧ P₀.Normal ∧
      ∀ N : Subgroup P, N.Normal → N ≤ B → N ≤ P₀ := by
    refine ⟨B.normalCore_le, inferInstance, ?_⟩
    intro N hN hNB
    exact @Subgroup.normal_le_normalCore P _ B N hN |>.mpr hNB
  have h33 := lemma_three_three S h P hP B P₀ hB hP₀data hsolv
  let O : Subgroup P := pCore 2 P
  let qO : P →* P ⧸ O := QuotientGroup.mk' O
  let R : Subgroup (P ⧸ O) :=
    twoResidualAmbient (⊤ : Subgroup (P ⧸ O))
  let Abar : Subgroup (P ⧸ O) := AP.map qO
  let Tbar : Subgroup (P ⧸ O) := TP.map qO
  let Phi : Subgroup (P ⧸ O) := P₀.map qO
  have hPhiEq : Phi = frattiniAmbient R := by
    simpa [Phi, R, O, qO] using h33.part_c
  have hPhiNormal : Phi.Normal :=
    hP₀data.2.1.map qO (QuotientGroup.mk'_surjective O)
  let _ : Phi.Normal := hPhiNormal
  have hpdata : Nonempty {p : ℕ // p.Prime ∧ Odd p ∧ IsPGroup p R} := by
    rcases h33.part_a with ⟨p, hp, hpodd, hRp⟩
    exact ⟨⟨p, hp, hpodd, by simpa [R, O] using hRp⟩⟩
  let pdata := Classical.choice hpdata
  let p : ℕ := pdata.1
  have hp : p.Prime := pdata.2.1
  have hpodd : Odd p := pdata.2.2.1
  have hRp : IsPGroup p R := pdata.2.2.2
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := h.nontrivial_two_subgroup.2
  have hA2 : IsPGroup 2 A := IsPGroup.to_le hS2 hA
  have hT2 : IsPGroup 2 T := IsPGroup.to_le hS2 hT.1
  let fA : A →* P ⧸ O := qO.comp (Subgroup.inclusion hAP)
  have hPhiKerA : frattini A ≤ fA.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change qO (Subgroup.inclusion hAP x) = 1
    change QuotientGroup.mk' O (Subgroup.inclusion hAP x) = 1
    apply (QuotientGroup.eq_one_iff (N := O) (Subgroup.inclusion hAP x)).2
    have hxamb : (x : G) ∈ frattiniAmbient A :=
      Subgroup.mem_map_of_mem A.subtype hx
    rcases hPhiA hxamb with ⟨y, hy, hyx⟩
    have hxy : (⟨(x : G), hAP x.property⟩ : P) = y :=
      Subtype.ext hyx.symm
    simpa [Subgroup.inclusion, hxy] using hy
  have hAbarElem : IsElementaryAbelian 2 Abar := by
    have hrange := elementaryAbelian_range_of_frattini_le_ker fA hA2 hPhiKerA
    have hAbarRange : Abar = fA.range := by
      ext y
      constructor
      · rintro ⟨x, hxAP, rfl⟩
        exact ⟨(⟨(x : G), hxAP⟩ : A), rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨(⟨(x : G), hAP x.property⟩ : P), x.property, rfl⟩
    rw [hAbarRange]
    exact hrange
  let aP : P := ⟨a, hAP haA⟩
  have haPAP : aP ∈ AP := haA
  let abar : Abar := ⟨qO aP, Subgroup.mem_map_of_mem qO haPAP⟩
  have habarNe : abar ≠ 1 := by
    intro haone
    have hqone : qO aP = 1 := congrArg Subtype.val haone
    have haO : aP ∈ O := (QuotientGroup.eq_one_iff (N := O) aP).1 hqone
    exact haCore (Subgroup.mem_map_of_mem P.subtype haO)
  have hRnormal : R.Normal := by
    dsimp [R]
    rw [twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_normal
  let _ : R.Normal := hRnormal
  have hAnormR : Abar ≤ Subgroup.normalizer R :=
    Subgroup.le_normalizer_of_normal
  have hTnormR : Tbar ≤ Subgroup.normalizer R :=
    Subgroup.le_normalizer_of_normal
  have hSPnormTP : SP ≤ Subgroup.normalizer TP := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs t ht
    have hSnormT : S ≤ Subgroup.normalizer (T : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hT.1).mp hT.2
    exact (Subgroup.mem_normalizer_iff.mp (hSnormT hs) (t : G)).mp ht
  have hAPleSP : AP ≤ SP := fun _ hx => hA hx
  have hAPnormTP : AP ≤ Subgroup.normalizer TP := hAPleSP.trans hSPnormTP
  have hAbarnormTbar : Abar ≤ Subgroup.normalizer Tbar := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono
      ((Subgroup.le_normalizer_iff_commutator_le_left).mp hAPnormTP)
  have hSPtwo : IsPGroup 2 SP := by
    obtain ⟨S₂, hS₂map⟩ := hP.1.2.1
    have hS₂eq : (S₂ : Subgroup P) = SP := by
      apply Subgroup.map_injective_of_ker_le P.subtype (by simp) (by simp)
      rw [hS₂map]
      exact (Subgroup.map_subgroupOf_eq_of_le hSP).symm
    rw [← hS₂eq]
    exact S₂.isPGroup'
  have hOleSP : O ≤ SP := by
    obtain ⟨S₂, hS₂map⟩ := hP.1.2.1
    have hS₂eq : (S₂ : Subgroup P) = SP := by
      apply Subgroup.map_injective_of_ker_le P.subtype (by simp) (by simp)
      rw [hS₂map]
      exact (Subgroup.map_subgroupOf_eq_of_le hSP).symm
    rw [← hS₂eq]
    exact IsPGroup.le_sylow_of_normal (pCore_isPGroup (G := P) (p := 2)) S₂
  have hOleP₀ : O ≤ P₀ := by
    apply hP₀data.2.2 O inferInstance
    exact hOleSP.trans hB.2.1
  let q₀ : P →* P ⧸ P₀ := QuotientGroup.mk' P₀
  let e : P ⧸ O →* P ⧸ P₀ :=
    QuotientGroup.map O P₀ (MonoidHom.id P) hOleP₀
  have heq : e.comp qO = q₀ := by
    ext x
    rfl
  let RP : Subgroup P := twoResidualAmbient (⊤ : Subgroup P)
  let R₀ : Subgroup (P ⧸ P₀) :=
    twoResidualAmbient (⊤ : Subgroup (P ⧸ P₀))
  have hRPqO : RP.map qO = R := by
    dsimp [RP, R]
    rw [twoResidualAmbient_top_eq_hktPResidual,
      map_hktPResidual_quotient 2 O,
      ← twoResidualAmbient_top_eq_hktPResidual]
  have hRPq₀ : RP.map q₀ = R₀ := by
    dsimp [RP, R₀]
    rw [twoResidualAmbient_top_eq_hktPResidual,
      map_hktPResidual_quotient 2 P₀,
      ← twoResidualAmbient_top_eq_hktPResidual]
  have hRe : R.map e = R₀ := by
    calc
      R.map e = (RP.map qO).map e := by rw [hRPqO]
      _ = RP.map (e.comp qO) := Subgroup.map_map (K := RP) e qO
      _ = RP.map q₀ := by rw [heq]
      _ = R₀ := hRPq₀
  let F : Subgroup (P ⧸ O) := ⁅R, Subgroup.zpowers (abar : P ⧸ O)⁆
  have hFnotPhi : ¬ F ≤ Phi := by
    intro hFPhi
    have hPhiMapBot : Phi.map e = ⊥ := by
      apply (Subgroup.map_eq_bot_iff Phi).2
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      change q₀ y = 1
      exact (QuotientGroup.eq_one_iff (N := P₀) y).2 hy
    have hFMapBot : F.map e = ⊥ := by
      apply le_bot_iff.mp
      exact (Subgroup.map_mono hFPhi).trans_eq hPhiMapBot
    have hcomm₀ : ⁅R₀, Subgroup.zpowers (q₀ aP)⁆ = ⊥ := by
      have hea : e (abar : P ⧸ O) = q₀ aP := by rfl
      rw [← hRe, ← hea, ← MonoidHom.map_zpowers,
        ← Subgroup.map_commutator]
      exact hFMapBot
    have hswap : ⁅Subgroup.zpowers (q₀ aP), R₀⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hcomm₀
    have hcent : q₀ aP ∈ Subgroup.centralizer (R₀ : Set (P ⧸ P₀)) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hswap)
        (Subgroup.mem_zpowers (q₀ aP))
    exact hnoncentral hcent
  have habarInv : IsInvolution (abar : P ⧸ O) := by
    refine ⟨(fun h => habarNe (Subtype.ext h)), ?_⟩
    have haAsq : (⟨a, haA⟩ : A) ^ 2 ∈ frattini A := by
      let _ : Fact (IsPGroup 2 A) := ⟨hA2⟩
      exact pth_power_mem_frattini_of_isPGroup _
    have haGsq : a ^ 2 ∈ frattiniAmbient A :=
      Subgroup.mem_map_of_mem A.subtype haAsq
    rcases hPhiA haGsq with ⟨y, hy, hya⟩
    have haPsq : aP ^ 2 ∈ O := by
      have he : aP ^ 2 = y := Subtype.ext hya.symm
      simpa [he] using hy
    change (qO aP) ^ 2 = 1
    have hq := (QuotientGroup.eq_one_iff (N := O) (aP ^ 2)).2 haPsq
    change qO (aP ^ 2) = 1 at hq
    simpa only [map_pow] using hq
  let qPhi : P ⧸ O →* (P ⧸ O) ⧸ Phi := QuotientGroup.mk' Phi
  let Vbar : Subgroup ((P ⧸ O) ⧸ Phi) := R.map qPhi
  let Tphi : Subgroup ((P ⧸ O) ⧸ Phi) := Tbar.map qPhi
  have hVbarNormal : Vbar.Normal := by
    exact hRnormal.map qPhi (QuotientGroup.mk'_surjective Phi)
  have hVbarElem : IsElementaryAbelian p Vbar := by
    let fR : R →* (P ⧸ O) ⧸ Phi := qPhi.comp R.subtype
    have hfrKer : frattini R ≤ fR.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      apply (QuotientGroup.eq_one_iff (N := Phi) (x : P ⧸ O)).2
      rw [hPhiEq]
      exact Subgroup.mem_map_of_mem R.subtype hx
    have hrange := elementaryAbelian_range_of_frattini_le_ker fR hRp hfrKer
    have hEq : Vbar = fR.range := image_of_subgroup_eq_range_comp_subtype R qPhi
    rw [hEq]
    exact hrange
  have hinvertsF : ∀ y : P ⧸ O, y ∈ F →
      qPhi ((abar : P ⧸ O) * y * (abar : P ⧸ O)⁻¹) =
        (qPhi y)⁻¹ := by
    intro y hy
    have haPhiInv : IsInvolution (qPhi (abar : P ⧸ O)) := by
      refine ⟨?_, by simpa using congrArg qPhi habarInv.2⟩
      intro hone
      have habaPhi : (abar : P ⧸ O) ∈ Phi :=
        (QuotientGroup.eq_one_iff (N := Phi) (abar : P ⧸ O)).1 hone
      have hq₀one : q₀ aP = 1 := by
        rcases habaPhi with ⟨v, hvP₀, hvEq⟩
        have hev : e (qO v) = 1 := by
          change q₀ v = 1
          exact (QuotientGroup.eq_one_iff (N := P₀) v).2 hvP₀
        have heabar : e (abar : P ⧸ O) = 1 := by
          rw [← hvEq]
          exact hev
        exact heabar
      apply hnoncentral
      have hcentR₀ : q₀ aP ∈
          Subgroup.centralizer (R₀ : Set (P ⧸ P₀)) := by
        rw [hq₀one]
        exact Subgroup.one_mem _
      simpa [q₀, P₀, R₀] using hcentR₀
    have haNormVbar : qPhi (abar : P ⧸ O) ∈
        Subgroup.normalizer (Vbar : Set ((P ⧸ O) ⧸ Phi)) :=
      Subgroup.le_normalizer_of_normal (show qPhi (abar : P ⧸ O) ∈ (⊤ : Subgroup _) from trivial)
    have hmapF : F.map qPhi =
        ⁅Vbar, Subgroup.zpowers (qPhi (abar : P ⧸ O))⁆ := by
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    have hqy : qPhi y ∈
        ⁅Vbar, Subgroup.zpowers (qPhi (abar : P ⧸ O))⁆ := by
      rw [← hmapF]
      exact Subgroup.mem_map_of_mem qPhi hy
    simpa using involution_inverts_commutator_with_zpowers'
      Vbar haPhiInv haNormVbar hVbarElem.toIsMulCommutative (qPhi y) hqy
  have hcommRT : ⁅R, Tbar⁆ = R := by
    have hcommG := (lemma_three_four S h P hP T hT hsolv).resolve_left hTcore
    let RG : Subgroup G := twoResidualAmbient P
    let RP' : Subgroup P := RG.subgroupOf P
    have hRGleP : RG ≤ P := Subgroup.map_subtype_le (twoResidualSubgroup P)
    have hRP'map : RP'.map P.subtype = RG :=
      Subgroup.map_subgroupOf_eq_of_le hRGleP
    have hTPmap : TP.map P.subtype = T :=
      Subgroup.map_subgroupOf_eq_of_le hTP
    have hcommP : ⁅RP', TP⁆ = RP' := by
      apply Subgroup.map_injective_of_ker_le P.subtype (by simp) (by simp)
      rw [Subgroup.map_commutator, hRP'map, hTPmap]
      simpa [RG] using hcommG
    have hRP'eq : RP' = RP := by
      have hleft : RP' = twoResidualSubgroup P := by
        dsimp [RP', RG, twoResidualAmbient]
        exact subgroupOf_map_subtype_eq (twoResidualSubgroup P)
      calc
        RP' = twoResidualSubgroup P := hleft
        _ = BenderSuzuki.External.hktPResidual 2 P :=
          twoResidualSubgroup_eq_hktPResidual' P
        _ = twoResidualAmbient (⊤ : Subgroup P) :=
          twoResidualAmbient_top_eq_hktPResidual.symm
        _ = RP := rfl
    rw [← hRPqO, ← hRP'eq, ← Subgroup.map_commutator, hcommP]
  have hcommVbar : ⁅Vbar, Tphi⁆ = Vbar := by
    rw [← Subgroup.map_commutator, hcommRT]
  have hTbarTwo : IsPGroup 2 Tbar := by
    have hTPtwo : IsPGroup 2 TP := IsPGroup.to_le hSPtwo (fun _ ht => hT.1 ht)
    exact IsPGroup.map hTPtwo qO
  have hTphiTwo : IsPGroup 2 Tphi := IsPGroup.map hTbarTwo qPhi
  have hTphiNormVbar : Tphi ≤ Subgroup.normalizer Vbar :=
    Subgroup.le_normalizer_of_normal
  have hfixed :
      let _ : Subgroup.Normalizes Tphi Vbar := ⟨hTphiNormVbar⟩
      fixedPointSubgroup Tphi Vbar = ⊥ :=
    fixedPointSubgroup_eq_bot_of_commutator_eq_self
      Vbar Tphi hpodd hVbarElem hTphiTwo hTphiNormVbar hcommVbar
  have huniversal : ∀ K : Subgroup (P ⧸ O), K ≤ R →
      K ≤ ⁅K, Tbar⁆ ⊔ Phi := by
    intro K hKR
    exact subgroup_le_commutator_sup_kernel_of_fixedPointSubgroup_eq_bot
      R Tbar K Phi hpodd hVbarElem hTbarTwo hTnormR hfixed hKR
  have hex := exists_lex_minimal_cyclic_reflection_commutator
    R Phi Abar Tbar hpodd hRp hAbarElem hAnormR hAbarnormTbar hTnormR
      abar habarNe hFnotPhi hinvertsF huniversal
  let K := Exists.choose hex
  have hexK := Exists.choose_spec hex
  let Y := Exists.choose hexK
  have hexY := Exists.choose_spec hexK
  let z := Exists.choose hexY
  have hw := Exists.choose_spec hexY
  have hKF : K ≤ F := hw.1
  have hAnormK : Abar ≤ Subgroup.normalizer K := hw.2.1
  have hKPhi : ¬ K ≤ Phi := hw.2.2.1
  have hYcoat : IsCoatom Y := hw.2.2.2.1
  have habarY : abar ∉ Y := hw.2.2.2.2.1
  have hfactor : (Set.univ : Set Abar) =
      (Subgroup.zpowers abar : Set Abar) * (Y : Set Abar) :=
    hw.2.2.2.2.2.1
  have hzR : z ∈ R := hw.2.2.2.2.2.2.1
  have hzPhi : z ∉ Phi := hw.2.2.2.2.2.2.2.1
  have hzY : ∀ b : Y, (b : P ⧸ O) * z * (b : P ⧸ O)⁻¹ = z :=
    hw.2.2.2.2.2.2.2.2.1
  have hza : (abar : P ⧸ O) * z * (abar : P ⧸ O)⁻¹ = z⁻¹ :=
    hw.2.2.2.2.2.2.2.2.2.1
  have hKcyc : K = Subgroup.zpowers z := hw.2.2.2.2.2.2.2.2.2.2.1
  have hKcomm : K ≤ ⁅K, Tbar⁆ := hw.2.2.2.2.2.2.2.2.2.2.2
  exact
    { p := p
      prime_p := hp
      odd_p := hpodd
      K := K
      Y := Y
      z := z
      z_mem_residual := hzR
      z_not_residual_frattini := by
        intro hzfr
        apply hzPhi
        rw [hPhiEq]
        exact Subgroup.mem_map_of_mem R.subtype hzfr
      residual_pgroup := hRp
      K_cyclic := hKcyc
      K_pgroup := IsPGroup.to_le hRp
        (hKF.trans (Subgroup.commutator_le_left R _))
      actor_two := IsPGroup.map
        (IsPGroup.to_le hSPtwo (fun _ hx => hA hx)) qO
      actor_elementary := hAbarElem
      actor_normalizes_K := hAnormK
      K_not_phi := hKPhi
      K_not_residual_frattini := by
        intro hKfr
        apply hKPhi
        rw [hPhiEq]
        exact hKfr
      Y_coatom := hYcoat
      reflection_not_Y := habarY
      actor_factor := hfactor
      reflected := by
        intro r hr
        rw [hKcyc, Subgroup.mem_zpowers_iff] at hr
        obtain ⟨n, rfl⟩ := hr
        have hactor :
            QuotientGroup.mk' (pCore 2 P) ⟨a, hAP haA⟩ =
              (abar : P ⧸ O) := rfl
        rw [hactor]
        rw [← conj_zpow]
        rw [hza]
        simp
      reflection_involution := habarInv
      Y_centralizes := hzY
      K_commutator := hKcomm }

end

end Stellmacher.SectionThree

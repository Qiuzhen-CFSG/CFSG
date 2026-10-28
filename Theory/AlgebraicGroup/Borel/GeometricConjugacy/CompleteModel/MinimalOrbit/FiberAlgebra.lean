module

public import Theory.AlgebraicGroup.Dimension.Fiber
-- Internal continuation of the commutative-algebra part of the affine fibre proof.
-- Its implementation helpers remain private; the new public statement is ring theoretic.
import all Theory.AlgebraicGroup.Dimension.Fiber

/-!
# Constant fibre-component dimension on affine charts

For an inclusion of finite-type domains over an algebraically closed field,
if every component of each closed fibre through a closed point has dimension
`d`, the source transcendence degree is the sum of the target transcendence
degree and `d`. The proof chooses a finite transcendence basis and a closed
point in its quasi-finite locus. The generalized principal ideal theorem gives
one inequality and the local height inequality gives the other. No smoothness,
separability, reducedness of fibres, or group law on the target is required.

This is the commutative-algebra step of the orbit dimension argument used in
Borel, *Linear Algebraic Groups*, §11.1 (`refs/KGroup/Bor1/Chapter4.tex`).
-/

open scoped nonZeroDivisors
open Cardinal

universe u

namespace Theory.AlgebraicGroup.Variety.Geometric.MinimalOrbit

set_option backward.isDefEq.respectTransparency false in
public theorem trdeg_eq_add_of_constant_fiber_components
    {k B A : Type u} [Field k] [IsAlgClosed k]
    [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
    [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
    [Algebra.FiniteType k B] [Algebra.FiniteType k A] [FaithfulSMul B A]
    (d : Cardinal) (hd : d < ℵ₀)
    (hfiber : ∀ (M : Ideal A), M.IsMaximal →
      ∀ q ∈ (M.under B |>.map (algebraMap B A)).minimalPrimes,
        q ≤ M → Algebra.trdeg k (A ⧸ q) = d) :
    Algebra.trdeg k A = Algebra.trdeg k B + d := by
  let : Algebra.FiniteType B A :=
    Algebra.FiniteType.of_restrictScalars_finiteType k B A
  obtain ⟨t, htfin, htb⟩ :=
    exists_finite_isTranscendenceBasis_subset (R := B) (A := A)
  let x : t → A := fun i => i.1
  let C := Algebra.adjoin B (Set.range x)
  let hCA : Algebra C A := inferInstance
  let : Algebra C A := hCA
  let : Algebra.FiniteType C A :=
    Algebra.FiniteType.of_restrictScalars_finiteType B C A
  have hqf0 : Algebra.QuasiFiniteAt C (⊥ : Ideal A) :=
    quasiFiniteAt_bot_adjoin_of_isTranscendenceBasis htb
  let : Algebra.QuasiFiniteAt C (⊥ : Ideal A) := hqf0
  have hzm : Algebra.ZariskisMainProperty C (⊥ : Ideal A) :=
    Algebra.ZariskisMainProperty.of_finiteType (R := C) (S := A) (⊥ : Ideal A)
  obtain ⟨S', hS', r, hr0, hrbij⟩ :=
    hzm.exists_fg_and_exists_notMem_and_awayMap_bijective (⊥ : Ideal A)
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hbotjac : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out' (⊥ : Ideal A) Ideal.isRadical_bot
  obtain ⟨M, ⟨hbotM, hMmax⟩, hrM⟩ :=
    (Ideal.eq_jacobson_iff_notMem (I := (⊥ : Ideal A))).mp hbotjac r.1 hr0
  let : M.IsMaximal := hMmax
  let : M.IsPrime := hMmax.isPrime
  have hqfM : Algebra.QuasiFiniteAt C M :=
    quasiFiniteAt_of_fg_and_awayMap_bijective S' hS' r hrM hrbij
  let : Algebra.QuasiFiniteAt C M := hqfM
  let : Field (A ⧸ M) := Ideal.Quotient.field M
  let : Module.Finite k (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ M)
  have hksurj : Function.Surjective (algebraMap k (A ⧸ M)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  let N := M.under B
  let J := N.map (algebraMap B A)
  have hNmax : N.IsMaximal := by
    let f : B →+* A ⧸ M := (Ideal.Quotient.mk M).comp (algebraMap B A)
    have hf : Function.Surjective f := by
      intro z
      obtain ⟨c, hc⟩ := hksurj z
      refine ⟨algebraMap k B c, ?_⟩
      change Ideal.Quotient.mk M (algebraMap B A (algebraMap k B c)) = z
      rw [← IsScalarTower.algebraMap_apply k B A]
      exact hc
    have hker : RingHom.ker f = N := by
      ext a
      change Ideal.Quotient.mk M (algebraMap B A a) = 0 ↔ algebraMap B A a ∈ M
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [← hker]
    exact RingHom.ker_isMaximal_of_surjective f hf
  let : N.IsMaximal := hNmax
  let : N.IsPrime := hNmax.isPrime
  have hJM : J ≤ M := Ideal.map_le_iff_le_comap.mpr le_rfl
  obtain ⟨q, hq, hqM⟩ := Ideal.exists_minimalPrimes_le hJM
  let : q.IsPrime := hq.isPrime
  choose rK hrK using fun i : t => hksurj (Ideal.Quotient.mk M (x i))
  let rB : t → B := fun i => algebraMap k B (rK i)
  have hdiffM (i : t) : x i - algebraMap B A (rB i) ∈ M := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    change Ideal.Quotient.mk M (x i) -
      Ideal.Quotient.mk M (algebraMap B A (algebraMap k B (rK i))) = 0
    rw [← IsScalarTower.algebraMap_apply k B A]
    exact sub_eq_zero.mpr (hrK i).symm
  let I : Ideal A :=
    Ideal.span (Set.range fun i : t => x i - algebraMap B A (rB i))
  have hIM : I ≤ M := by
    change Ideal.span (Set.range fun i : t =>
      x i - algebraMap B A (rB i)) ≤ M
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hdiffM i
  obtain ⟨p, hp, hpM⟩ :=
    Ideal.exists_minimalPrimes_le (show q ⊔ I ≤ M from sup_le hqM hIM)
  let : p.IsPrime := hp.isPrime
  have hMN : M.under B = N := rfl
  have hJq : J ≤ q := hq.le
  have hNp : N ≤ p.under B := by
    change N ≤ p.comap (algebraMap B A)
    rw [← Ideal.map_le_iff_le_comap]
    simpa [J] using hJq.trans (le_sup_left.trans hp.le)
  have hpunder : p.under B = M.under B := by
    have hMp : M.under B ≤ p.under B := by
      rw [hMN]
      exact hNp
    exact le_antisymm (Ideal.comap_mono hpM) hMp
  have hdiffp (i : t) : x i - algebraMap B A (rB i) ∈ p :=
    (le_sup_right.trans hp.le) (Ideal.subset_span ⟨i, rfl⟩)
  have hpunderC : p.under C = M.under C := by
    simpa [C] using under_adjoin_eq_of_under_eq_of_sub_mem
      htb.1 hpM hpunder rB hdiffp
  have hpEqM : p = M :=
    Algebra.QuasiFiniteAt.eq_of_le_of_under_eq (R := C) hpM hpunderC
  have hMmin : M ∈ (q ⊔ I).minimalPrimes := by
    rw [← hpEqM]
    exact hp
  let π : A →+* A ⧸ q := Ideal.Quotient.mk q
  let s : Set (A ⧸ q) :=
    Set.range fun i : t => π (x i - algebraMap B A (rB i))
  let : Fintype t := htfin.fintype
  have hsfin : s.Finite := Set.finite_range _
  have hMqmin : M.map π ∈ (Ideal.span s).minimalPrimes := by
    have hmap : M.map π ∈ (I.map π).minimalPrimes := by
      rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective I]
      refine ⟨M, ?_, rfl⟩
      rw [Ideal.mk_ker, sup_comm]
      exact hMmin
    have hIs : I.map π = Ideal.span s := by
      change Ideal.map π (Ideal.span (Set.range fun i : t =>
        x i - algebraMap B A (rB i))) = Ideal.span s
      rw [Ideal.map_span]
      congr 1
      ext z
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨_, ⟨i, rfl⟩, rfl⟩
    rwa [hIs] at hmap
  have hMqmax : (M.map π).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective <| by
      rw [Ideal.mk_ker]
      exact hqM
  let : (M.map π).IsMaximal := hMqmax
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hheight : (M.map π).height ≤ s.ncard :=
    Ideal.height_le_card_of_mem_minimalPrimes_span hsfin hMqmin
  have hncard : s.ncard ≤ Fintype.card t := by
    simpa [s] using Set.ncard_image_le
      (f := fun i : t => π (x i - algebraMap B A (rB i)))
      (s := Set.univ)
  have htrNat : Cardinal.toNat (Algebra.trdeg k (A ⧸ q)) ≤ Fintype.card t := by
    have hheight' : (Cardinal.toNat (Algebra.trdeg k (A ⧸ q)) : ℕ∞) ≤
        (Fintype.card t : ℕ∞) := by
      rw [← domain_maximal_height_eq_trdeg (A ⧸ q) (M.map π)]
      exact hheight.trans (by exact_mod_cast hncard)
    exact_mod_cast hheight'
  have htrqfin : Algebra.trdeg k (A ⧸ q) < ℵ₀ :=
    trdeg_lt_aleph0_of_finiteType
  have htfin' : (#t : Cardinal) < ℵ₀ := Cardinal.mk_lt_aleph0
  have htrq : Algebra.trdeg k (A ⧸ q) ≤ Algebra.trdeg B A := by
    rw [← htb.cardinalMk_eq_trdeg]
    exact (Cardinal.toNat_le_iff_le_of_lt_aleph0 htrqfin htfin').mp <| by
      simpa using htrNat
  have hdimq : d = Algebra.trdeg k (A ⧸ q) :=
    (hfiber M hMmax q hq hqM).symm
  have hKle : d ≤
      Algebra.trdeg B A := by
    rw [hdimq]
    exact htrq
  have hNJ : N.map (algebraMap B A) = J := by
    rfl
  let πJ : A →+* A ⧸ J := Ideal.Quotient.mk J
  let Mbar : Ideal (A ⧸ J) := M.map πJ
  have hcomapBotJ : (⊥ : Ideal (A ⧸ J)).comap πJ = J := by
    change RingHom.ker πJ = J
    dsimp only [πJ]
    exact Ideal.mk_ker
  have hMbarmax : Mbar.IsMaximal := by
    dsimp only [Mbar]
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    exact hJM
  let : Mbar.IsMaximal := hMbarmax
  let : Mbar.IsPrime := hMbarmax.isPrime
  have hfiberheight : Mbar.height ≤
      (Cardinal.toNat
        (d) : ℕ∞) := by
    apply height_le_of_minimalPrimes_quotient_height_le
    intro qbar hqbar hqbarM
    let : qbar.IsPrime := hqbar.isPrime
    let q0 : Ideal A := qbar.comap πJ
    have hq0prime : q0.IsPrime := Ideal.comap_isPrime πJ qbar
    let : q0.IsPrime := hq0prime
    have hJq0 : J ≤ q0 := by
      change J ≤ qbar.comap πJ
      intro a ha
      change πJ a ∈ qbar
      have hzero : πJ a = 0 := by
        dsimp only [πJ]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
      rw [hzero]
      exact qbar.zero_mem
    have hq0min : q0 ∈ J.minimalPrimes := by
      change qbar.comap πJ ∈ J.minimalPrimes
      have hmin : qbar.comap πJ ∈
          ((⊥ : Ideal (A ⧸ J)).comap πJ).minimalPrimes :=
        Ideal.minimalPrimes_comap_of_surjective
        (f := πJ) Ideal.Quotient.mk_surjective hqbar
      exact Eq.mp
        (congrArg (fun I : Ideal A => qbar.comap πJ ∈ I.minimalPrimes)
          hcomapBotJ)
        hmin
    have hq0M : q0 ≤ M := by
      have hcomapM : (M.map πJ).comap πJ = M := by
        rw [Ideal.comap_map_of_surjective πJ Ideal.Quotient.mk_surjective,
          hcomapBotJ]
        exact sup_eq_left.mpr hJM
      exact (Ideal.comap_mono (f := πJ) hqbarM).trans_eq hcomapM
    have hdimq0 : d = Algebra.trdeg k (A ⧸ q0) :=
      (hfiber M hMmax q0 hq0min hq0M).symm
    have hmapq0 : q0.map πJ = qbar := by
      exact Ideal.map_comap_of_surjective πJ Ideal.Quotient.mk_surjective qbar
    let e0 : ((A ⧸ J) ⧸ qbar) ≃ₐ[k]
        ((A ⧸ J) ⧸ q0.map (Ideal.Quotient.mkₐ k J)) :=
      Ideal.quotientEquivAlgOfEq k hmapq0.symm
    let e1 : ((A ⧸ J) ⧸ q0.map (Ideal.Quotient.mkₐ k J)) ≃ₐ[k]
        A ⧸ q0 := DoubleQuot.quotQuotEquivQuotOfLEₐ k hJq0
    let e := e0.trans e1
    have htrnested : Algebra.trdeg k ((A ⧸ J) ⧸ qbar) =
        Algebra.trdeg k (A ⧸ q0) := e.trdeg_eq
    have hqbarMmax :
        (Mbar.map (Ideal.Quotient.mk qbar)).IsMaximal := by
      apply Ideal.IsMaximal.map_of_surjective_of_ker_le
        Ideal.Quotient.mk_surjective
      rw [Ideal.mk_ker]
      exact hqbarM
    let : (Mbar.map (Ideal.Quotient.mk qbar)).IsMaximal := hqbarMmax
    let : Algebra.FiniteType k (A ⧸ J) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J)
        Ideal.Quotient.mk_surjective
    let : Algebra.FiniteType k ((A ⧸ J) ⧸ qbar) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k qbar)
        Ideal.Quotient.mk_surjective
    rw [domain_maximal_height_eq_trdeg (k := k) ((A ⧸ J) ⧸ qbar)
      (Mbar.map (Ideal.Quotient.mk qbar)), htrnested, ← hdimq0]
  have hMNlies : M.LiesOver N := ⟨hMN.symm⟩
  let : M.LiesOver N := hMNlies
  have hheightMain : M.height ≤ N.height + Mbar.height := by
    have h := Ideal.height_le_height_add_of_liesOver N M
    rw [hNJ] at h
    simpa only [Mbar, πJ] using h
  have hheightTotal : M.height ≤ N.height +
      (Cardinal.toNat
        (d) : ℕ∞) :=
    hheightMain.trans (add_le_add_right hfiberheight N.height)
  have hNatTotal : Cardinal.toNat (Algebra.trdeg k A) ≤
      Cardinal.toNat (Algebra.trdeg k B) +
        Cardinal.toNat
          (d) := by
    have h' : (Cardinal.toNat (Algebra.trdeg k A) : ℕ∞) ≤
        (Cardinal.toNat (Algebra.trdeg k B) : ℕ∞) +
          (Cardinal.toNat
            (d) : ℕ∞) := by
      rw [← domain_maximal_height_eq_trdeg A M,
        ← domain_maximal_height_eq_trdeg B N]
      exact hheightTotal
    exact_mod_cast h'
  have hAfin : Algebra.trdeg k A < ℵ₀ := trdeg_lt_aleph0_of_finiteType
  have hBfin : Algebra.trdeg k B < ℵ₀ := trdeg_lt_aleph0_of_finiteType
  have hrelfin : Algebra.trdeg B A < ℵ₀ := trdeg_lt_aleph0_of_finiteType
  have hKfin : d < ℵ₀ := hd
  have htower : Algebra.trdeg k A =
      Algebra.trdeg k B + Algebra.trdeg B A :=
    (trdeg_add_eq (R := k) (S := B) (A := A)).symm
  have htowerNat : Cardinal.toNat (Algebra.trdeg k A) =
      Cardinal.toNat (Algebra.trdeg k B) +
        Cardinal.toNat (Algebra.trdeg B A) := by
    rw [htower, Cardinal.toNat_add hBfin hrelfin]
  have hrelNat : Cardinal.toNat (Algebra.trdeg B A) ≤
      Cardinal.toNat
        (d) := by
    rw [htowerNat] at hNatTotal
    exact Nat.le_of_add_le_add_left hNatTotal
  have hrelle : Algebra.trdeg B A ≤
      d :=
    (Cardinal.toNat_le_iff_le_of_lt_aleph0 hrelfin hKfin).mp hrelNat
  have hKrel : d =
      Algebra.trdeg B A := le_antisymm hKle hrelle
  rw [hKrel]
  exact htower

end Theory.AlgebraicGroup.Variety.Geometric.MinimalOrbit

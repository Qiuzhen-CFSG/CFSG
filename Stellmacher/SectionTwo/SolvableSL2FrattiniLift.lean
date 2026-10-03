module

public import Stellmacher.SectionsOneToFourDefs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Theory.GroupAction.MinimalNormal
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# A Sylow-preserving `SL₂(2)` lift through the 2-core and Frattini subgroup

This module supplies the minimal-lift argument used implicitly in the proof of
Stellmacher (2.4), on journal page 20. Given a surjection from a finite
solvable group onto `SL₂(2)` and a fixed Sylow 2-subgroup, the main theorem
finds a subgroup containing that Sylow subgroup whose quotient first by its
2-core and then by its Frattini subgroup is again `SL₂(2)`. The nested
Frattini quotient is essential: the corresponding quotient by the 2-core alone
need not be `SL₂(2)`.

The construction theorem also records that the chosen subgroup still maps
onto the prescribed target.  This image equality is needed when a family of
coordinate lifts is used to generate an ambient group in (2.4).  The original
caller-facing theorem remains as a wrapper for consumers that need only the
nested quotient.

The proof chooses an inclusion-minimal Sylow overgroup mapping onto the target.
After factoring its 2-core, a Frattini normalizer argument shows that the
kernel meets the distinguished Sylow subgroup trivially and therefore has odd
order. A maximal subgroup missing the kernel would then be an odd-index
supplement; Sylow conjugacy would turn it into a smaller surjective overgroup
of the distinguished Sylow subgroup, contradicting minimality. Thus the
kernel is exactly the Frattini subgroup, and the induced quotient is the
required copy of `SL₂(2)`. Private supporting lemmas verify that both the
2-core and Frattini subgroup of `SL₂(2)` are trivial.
-/

open scoped Pointwise

namespace Stellmacher.SectionTwo

universe u v

private theorem pCore_map_le_pCore_of_surjective'
    {G : Type u} {H : Type v} [Group G] [Finite G] [Group H] [Finite H]
    (p : ℕ) (f : G →* H) (hf : Function.Surjective f) :
    (pCore p G).map f ≤ pCore p H := by
  exact le_sSup ⟨
    Subgroup.Normal.map (H := pCore p G) inferInstance f hf,
    (pCore_isPGroup (G := G) (p := p)).map f⟩

private theorem pCore_quotient_pCore_eq_bot'
    {G : Type u} [Group G] [Finite G] (p : ℕ) :
    pCore p (G ⧸ pCore p G) = ⊥ := by
  let q : G →* G ⧸ pCore p G := QuotientGroup.mk' (pCore p G)
  have hmap : (pCore p G).map q = pCore p (G ⧸ pCore p G) :=
    pCore_map_mk'_eq_of_normal_isPGroup (G := G) (p := p) (pCore p G)
      (pCore_isPGroup (G := G) (p := p))
  have hmap_bot : (pCore p G).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (f := q) (H := pCore p G)).2
    simp [q, QuotientGroup.ker_mk']
  exact hmap.symm.trans hmap_bot

private theorem index_dvd_card_of_normal_sup_eq_top
    {G : Type u} [Group G] [Finite G]
    {N M : Subgroup G} [N.Normal] (hNM : N ⊔ M = ⊤) :
    M.index ∣ Nat.card N := by
  have hrel_eq : M.relIndex (M ⊔ N) = (M ⊓ N).relIndex N := by
    have hNrel : N.relIndex (M ⊔ N) = (M ⊓ N).relIndex M := by
      calc
        N.relIndex (M ⊔ N) = N.relIndex M := by simp
        _ = (M ⊓ N).relIndex M := by
          symm
          simpa [inf_comm] using
            (Subgroup.inf_relIndex_left (H := M) (K := N))
    have hmul :
        (M ⊓ N).relIndex M * M.relIndex (M ⊔ N) =
          (M ⊓ N).relIndex N * (M ⊓ N).relIndex M := by
      calc
        (M ⊓ N).relIndex M * M.relIndex (M ⊔ N) =
            (M ⊓ N).relIndex (M ⊔ N) :=
          Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
        _ = (M ⊓ N).relIndex N * N.relIndex (M ⊔ N) := by
          symm
          exact Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
        _ = (M ⊓ N).relIndex N * (M ⊓ N).relIndex M := by rw [hNrel]
    have hpos : 0 < (M ⊓ N).relIndex M := by
      exact Nat.pos_of_ne_zero (by
        dsimp [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite)
    exact Nat.eq_of_mul_eq_mul_left hpos (by
      simpa [Nat.mul_comm] using hmul)
  have hidx : M.relIndex (M ⊔ N) = M.index := by
    rw [show M ⊔ N = ⊤ by simpa [sup_comm] using hNM]
    exact Subgroup.relIndex_top_right (H := M)
  rw [← hidx, hrel_eq]
  exact Subgroup.relIndex_dvd_card (H := M ⊓ N) (K := N)

private theorem center_eq_bot_of_isSL2Two'
    {D : Type u} [Group D] [Finite D] (hD : IsSL2Two D) :
    Subgroup.center D = ⊥ := by
  obtain ⟨e⟩ := hD
  ext x
  constructor
  · intro hx
    have hex : e x ∈ Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      simpa using congrArg e (Subgroup.mem_center_iff.mp hx z)
    have hcenter : Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro A hA
      revert hA
      decide +kernel +revert
    rw [hcenter] at hex
    exact e.injective (by simpa using (show e x = 1 from hex))
  · intro hx
    rw [hx]
    exact Subgroup.one_mem _

private theorem isSL2Two_frattini_eq_bot
    {D : Type u} [Group D] [Finite D] (hD : IsSL2Two D) :
    frattini D = ⊥ := by
  let P : Sylow 2 D := default
  let R : Sylow 3 D := default
  have hfactor2 : Nat.factorization 6 2 = 1 := by
    have hzero : padicValNat 2 3 = 0 :=
      padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
    rw [Nat.factorization_def 6 Nat.prime_two,
      show (6 : Nat) = 2 ^ 1 * 3 by norm_num,
      padicValNat_base_pow_mul (by norm_num) (by norm_num) 1, hzero]
  have hfactor3 : Nat.factorization 6 3 = 1 := by
    have hzero : padicValNat 3 2 = 0 :=
      padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
    rw [Nat.factorization_def 6 Nat.prime_three,
      show (6 : Nat) = 3 ^ 1 * 2 by norm_num,
      padicValNat_base_pow_mul (by norm_num) (by norm_num) 1, hzero]
  have hDcard : Nat.card D = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hD
  have hPcard : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity, hDcard, hfactor2]
    norm_num
  have hRcard : Nat.card R = 3 := by
    rw [R.card_eq_multiplicity, hDcard, hfactor3]
    norm_num
  have hPcoat : IsCoatom (P : Subgroup D) := by
    constructor
    · intro htop
      have hcard := congrArg (fun L : Subgroup D => Nat.card L) htop
      simp only [Subgroup.card_top, hDcard] at hcard
      omega
    · intro L hPL
      have hPdL : Nat.card P ∣ Nat.card L := Subgroup.card_dvd_of_le hPL.le
      have hLdD : Nat.card L ∣ Nat.card D := Subgroup.card_subgroup_dvd_card L
      have hLpos : 0 < Nat.card L := Nat.card_pos
      have hPcardLt : Nat.card P < Nat.card L := by
        apply lt_of_le_of_ne (Subgroup.card_le_of_le hPL.le)
        intro hEq
        exact hPL.ne (Subgroup.eq_of_le_of_card_ge hPL.le hEq.symm.le)
      have hLcard : Nat.card L = Nat.card D := by
        have hLle : Nat.card L ≤ 6 :=
          Nat.le_of_dvd (by omega) (by simpa [hDcard] using hLdD)
        rw [hPcard] at hPdL hPcardLt
        rw [hDcard] at hLdD ⊢
        interval_cases hcard : Nat.card L <;> norm_num [hcard] at *
      exact Subgroup.eq_top_of_card_eq L hLcard
  have hRcoat : IsCoatom (R : Subgroup D) := by
    constructor
    · intro htop
      have hcard := congrArg (fun L : Subgroup D => Nat.card L) htop
      simp only [Subgroup.card_top, hDcard] at hcard
      omega
    · intro L hRL
      have hRdL : Nat.card R ∣ Nat.card L := Subgroup.card_dvd_of_le hRL.le
      have hLdD : Nat.card L ∣ Nat.card D := Subgroup.card_subgroup_dvd_card L
      have hLpos : 0 < Nat.card L := Nat.card_pos
      have hRcardLt : Nat.card R < Nat.card L := by
        apply lt_of_le_of_ne (Subgroup.card_le_of_le hRL.le)
        intro hEq
        exact hRL.ne (Subgroup.eq_of_le_of_card_ge hRL.le hEq.symm.le)
      have hLcard : Nat.card L = Nat.card D := by
        have hLle : Nat.card L ≤ 6 :=
          Nat.le_of_dvd (by omega) (by simpa [hDcard] using hLdD)
        rw [hRcard] at hRdL hRcardLt
        rw [hDcard] at hLdD ⊢
        interval_cases hcard : Nat.card L <;> norm_num [hcard] at *
      exact Subgroup.eq_top_of_card_eq L hLcard
  have hdisj : Disjoint (P : Subgroup D) (R : Subgroup D) :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hPcard, hRcard]; decide)
  apply le_antisymm
  · rw [← hdisj.eq_bot]
    exact le_inf (frattini_le_coatom hPcoat) (frattini_le_coatom hRcoat)
  · exact bot_le

private theorem isSL2Two_twoCore_eq_bot
    {D : Type u} [Group D] [Finite D] (hD : IsSL2Two D) :
    pCore 2 D = ⊥ := by
  let P : Sylow 2 D := default
  have hfactor : Nat.factorization 6 2 = 1 := by
    have hzero : padicValNat 2 3 = 0 :=
      padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
    rw [Nat.factorization_def 6 Nat.prime_two,
      show (6 : Nat) = 2 ^ 1 * 3 by norm_num,
      padicValNat_base_pow_mul (by norm_num) (by norm_num) 1, hzero]
  have hPcard : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity,
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hD, hfactor]
    norm_num
  have hcoreP : pCore 2 D ≤ (P : Subgroup D) :=
    pCore_isPGroup.le_sylow_of_normal P
  by_contra hne
  have hcoreCard : Nat.card (pCore 2 D) = 2 := by
    have hlo := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    have hhi : Nat.card (pCore 2 D) ≤ 2 := by
      simpa only [hPcard] using Subgroup.card_le_of_le hcoreP
    omega
  have hcoreEq : pCore 2 D = (P : Subgroup D) :=
    Subgroup.eq_of_le_of_card_ge hcoreP (by omega)
  have hPnormal : (P : Subgroup D).Normal := hcoreEq ▸ inferInstance
  have hPcenter : (P : Subgroup D) ≤ Subgroup.center D := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hxconj : g * x * g⁻¹ ∈ (P : Subgroup D) :=
      hPnormal.conj_mem x hx g
    obtain ⟨t, ht_ne, ht_unique⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hPcard
    by_cases hxone : x = 1
    · simp [hxone]
    have hxEq : (⟨x, hx⟩ : P) = t := ht_unique ⟨x, hx⟩ (by
      intro heq
      exact hxone (congrArg Subtype.val heq))
    have hconjNe : g * x * g⁻¹ ≠ 1 := by
      intro heq
      have := congrArg (fun y : D => g⁻¹ * y * g) heq
      exact hxone (by simpa [mul_assoc] using this)
    have hconjEq : (⟨g * x * g⁻¹, hxconj⟩ : P) = t :=
      ht_unique _ (by
        intro heq
        exact hconjNe (congrArg Subtype.val heq))
    have hgx : g * x * g⁻¹ = x :=
      congrArg Subtype.val (hconjEq.trans hxEq.symm)
    have := congrArg (fun y : D => y * g) hgx
    simpa [mul_assoc] using this
  have hcenterBot := center_eq_bot_of_isSL2Two' hD
  have hPbot : (P : Subgroup D) = ⊥ := by
    apply le_antisymm
    · simpa only [hcenterBot] using hPcenter
    · exact bot_le
  have : Nat.card P = 1 := (Subgroup.eq_bot_iff_card _).mp hPbot
  omega

private theorem ker_le_frattini_of_sylow_minimal
    {Q : Type u} {D : Type v} [Group Q] [Finite Q] [Group D] [Finite D]
    (U : Sylow 2 Q) (f : Q →* D) (hf : Function.Surjective f)
    (hmin : ∀ M : Subgroup Q, (U : Subgroup Q) ≤ M → M.map f = ⊤ → M = ⊤)
    (hcore : pCore 2 Q = ⊥) :
    f.ker ≤ frattini Q := by
  classical
  let N : Subgroup Q := f.ker
  let _ : N.Normal := inferInstance
  obtain ⟨T, hT⟩ := U.exists_subgroupOf_eq_of_normal N
  let TQ : Subgroup Q := (T : Subgroup N).map N.subtype
  have hTQ : TQ = (U : Subgroup Q) ⊓ N := by
    change (T : Subgroup N).map N.subtype = (U : Subgroup Q) ⊓ N
    rw [hT]
    ext x
    simp
  have hUnormTQ : (U : Subgroup Q) ≤ Subgroup.normalizer (TQ : Set Q) := by
    rw [hTQ, Subgroup.le_normalizer_iff]
    intro u hu x hx
    exact ⟨
      (U : Subgroup Q).mul_mem ((U : Subgroup Q).mul_mem hu hx.1)
        ((U : Subgroup Q).inv_mem hu),
      (inferInstance : N.Normal).conj_mem x hx.2 u⟩
  have hfrattini : Subgroup.normalizer (TQ : Set Q) ⊔ N = ⊤ := by
    simpa [TQ] using Sylow.normalizer_sup_eq_top (G := Q) (N := N) T
  have hnormMap : (Subgroup.normalizer (TQ : Set Q)).map f = ⊤ := by
    have hNmap : N.map f = ⊥ := by
      exact (Subgroup.map_eq_bot_iff (f := f) (H := N)).2 le_rfl
    calc
      (Subgroup.normalizer (TQ : Set Q)).map f =
          (Subgroup.normalizer (TQ : Set Q)).map f ⊔ N.map f := by rw [hNmap, sup_bot_eq]
      _ = (Subgroup.normalizer (TQ : Set Q) ⊔ N).map f := by rw [Subgroup.map_sup]
      _ = ⊤ := by rw [hfrattini, Subgroup.map_top_of_surjective f hf]
  have hnormTop : Subgroup.normalizer (TQ : Set Q) = ⊤ :=
    hmin _ hUnormTQ hnormMap
  have hTQnormal : TQ.Normal := Subgroup.normalizer_eq_top_iff.mp hnormTop
  have hTQcore : TQ ≤ pCore 2 Q := by
    exact le_sSup ⟨hTQnormal, T.isPGroup'.map N.subtype⟩
  have hTQbot : TQ = ⊥ := by
    apply le_antisymm
    · simpa [hcore] using hTQcore
    · exact bot_le
  have hTbot : (T : Subgroup N) = ⊥ := by
    apply Subgroup.map_injective N.subtype_injective
    simpa [TQ] using hTQbot
  have hNodd : Odd (Nat.card N) := by
    apply Nat.not_even_iff_odd.mp
    simpa [even_iff_two_dvd, hTbot] using T.not_dvd_index
  intro x hxN
  by_contra hxPhi
  rw [frattini, Order.radical] at hxPhi
  simp only [Subgroup.mem_iInf] at hxPhi
  push Not at hxPhi
  obtain ⟨M, hMcoat, hxM⟩ := hxPhi
  have hNM : ¬ N ≤ M := fun h => hxM (h hxN)
  have hMNtop : N ⊔ M = ⊤ := by
    rcases (hMcoat.le_iff).mp le_sup_right with htop | heq
    · exact htop
    · exact False.elim (hNM (le_sup_left.trans (le_of_eq heq)))
  have hMmap : M.map f = ⊤ := by
    have hNmap : N.map f = ⊥ :=
      (Subgroup.map_eq_bot_iff (f := f) (H := N)).2 le_rfl
    calc
      M.map f = M.map f ⊔ N.map f := by rw [hNmap, sup_bot_eq]
      _ = (M ⊔ N).map f := by rw [Subgroup.map_sup]
      _ = ⊤ := by rw [show M ⊔ N = ⊤ by simpa [sup_comm] using hMNtop,
        Subgroup.map_top_of_surjective f hf]
  have hMindexOdd : Odd M.index :=
    Odd.of_dvd_nat hNodd (index_dvd_card_of_normal_sup_eq_top hMNtop)
  let PM : Sylow 2 M := default
  let PMQ : Subgroup Q := (PM : Subgroup M).map M.subtype
  have hPMQp : IsPGroup 2 PMQ := PM.isPGroup'.map M.subtype
  have hPMQindex : PMQ.index = (PM : Subgroup M).index * M.index := by
    simpa [PMQ] using Subgroup.index_map_subtype (K := (PM : Subgroup M))
  have htwoNotPMQ : ¬ 2 ∣ PMQ.index := by
    rw [hPMQindex]
    exact Nat.Prime.not_dvd_mul Nat.prime_two PM.not_dvd_index hMindexOdd.not_two_dvd_nat
  let V : Sylow 2 Q := IsPGroup.toSylow hPMQp htwoNotPMQ
  have hVleM : (V : Subgroup Q) ≤ M := by
    intro y hy
    change y ∈ PMQ at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact z.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q V U
  let e : Q ≃* Q := MulAut.conj g
  let M' : Subgroup Q := M.map e.toMonoidHom
  have hM'coat : IsCoatom M' := (OrderIso.isCoatom_iff e.mapSubgroup M).2 hMcoat
  have hmapV : (V : Subgroup Q).map e.toMonoidHom = (U : Subgroup Q) := by
    have h := congrArg (fun W : Sylow 2 Q => (W : Subgroup Q)) hg
    have he :
        MulDistribMulAction.toMonoidEnd (MulAut Q) Q (MulAut.conj g) =
          e.toMonoidHom := by
      ext y
      rfl
    simpa only [e, Sylow.coe_subgroup_smul,
      Subgroup.pointwise_smul_def, he] using h
  have hUM' : (U : Subgroup Q) ≤ M' := by
    rw [← hmapV]
    exact Subgroup.map_mono hVleM
  have hM'map : M'.map f = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro d
    have hd : f g⁻¹ * d * f g ∈ M.map f := by rw [hMmap]; trivial
    obtain ⟨m, hm, hmm⟩ := hd
    let m' : Q := e m
    have hm'M' : m' ∈ M' := ⟨m, hm, rfl⟩
    have hfm' : f m' = d := by
      have hmm' : f m = (f g)⁻¹ * d * f g := by
        calc
          f m = f g⁻¹ * d * f g := hmm
          _ = (f g)⁻¹ * d * f g := by rw [map_inv]
      calc
        f m' = f g * f m * (f g)⁻¹ := by
          simp [m', e, MulAut.conj_apply]
        _ = d := by rw [hmm']; group
    exact ⟨m', hm'M', hfm'⟩
  have hM'top : M' = ⊤ := hmin M' hUM' hM'map
  exact hM'coat.ne_top hM'top

public theorem exists_sylow_overgroup_with_sl2Frattini_quotient_and_map_eq_top
    {H : Type u} [Group H] [Finite H]
    {D : Type v} [Group D] [Finite D]
    (_hsolv : Group.IsSolvable H) (P : Sylow 2 H)
    (f : H →* D) (hf : Function.Surjective f) (hD : IsSL2Two D) :
    ∃ K : Subgroup H, (P : Subgroup H) ≤ K ∧ K.map f = ⊤ ∧
      IsSL2Two ((K ⧸ pCore 2 K) ⧸ frattini (K ⧸ pCore 2 K)) := by
  classical
  let Good : Subgroup H → Prop := fun K =>
    (P : Subgroup H) ≤ K ∧ K.map f = ⊤
  have htopGood : Good ⊤ := by
    refine ⟨le_top, Subgroup.map_top_of_surjective f hf⟩
  obtain ⟨K, hKgood, hKmin⟩ :=
    exists_minimal_subgroup_of_mem_top Good htopGood
  have hPK : (P : Subgroup H) ≤ K := hKgood.1
  have hKmap : K.map f = ⊤ := hKgood.2
  let fK : K →* D := f.comp K.subtype
  have hfK : Function.Surjective fK := by
    intro d
    have hd : d ∈ K.map f := by rw [hKmap]; trivial
    obtain ⟨k, hk, hkd⟩ := hd
    exact ⟨⟨k, hk⟩, hkd⟩
  let O : Subgroup K := pCore 2 K
  have hOleKer : O ≤ fK.ker := by
    apply (Subgroup.map_eq_bot_iff (f := fK) (H := O)).1
    apply le_antisymm
    · have hmap := pCore_map_le_pCore_of_surjective' 2 fK hfK
      simpa [O, isSL2Two_twoCore_eq_bot hD] using hmap
    · exact bot_le
  let Q := K ⧸ O
  let q : K →* Q := QuotientGroup.mk' O
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective O
  let PK : Sylow 2 K := P.subtype hPK
  let U : Sylow 2 Q := PK.mapSurjective hq
  let fbar : Q →* D := QuotientGroup.lift O fK hOleKer
  have hfbar : Function.Surjective fbar :=
    QuotientGroup.lift_surjective_of_surjective O fK hfK hOleKer
  have hfbarComp : fbar.comp q = fK := by
    ext k
    exact QuotientGroup.lift_mk' O hOleKer k
  have hminQ : ∀ A : Subgroup Q,
      (U : Subgroup Q) ≤ A → A.map fbar = ⊤ → A = ⊤ := by
    intro A hUA hAmap
    let Apre : Subgroup K := A.comap q
    let L : Subgroup H := Apre.map K.subtype
    have hPKApre : (PK : Subgroup K) ≤ Apre := by
      apply (Subgroup.map_le_iff_le_comap).1
      simpa [U] using hUA
    have hPKmap : (PK : Subgroup K).map K.subtype = (P : Subgroup H) := by
      change (P.subtype hPK : Sylow 2 K).toSubgroup.map K.subtype =
        (P : Subgroup H)
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPK]
    have hPL : (P : Subgroup H) ≤ L := by
      rw [← hPKmap]
      exact Subgroup.map_mono hPKApre
    have hLleK : L ≤ K := by
      exact Subgroup.map_subtype_le Apre
    have hApreMap : Apre.map q = A := by
      exact Subgroup.map_comap_eq_self_of_surjective hq A
    have hLmap : L.map f = ⊤ := by
      calc
        L.map f = Apre.map fK := by
          simp [L, fK, Subgroup.map_map]
        _ = Apre.map (fbar.comp q) := by rw [hfbarComp]
        _ = (Apre.map q).map fbar := by rw [Subgroup.map_map]
        _ = ⊤ := by rw [hApreMap, hAmap]
    have hLtop : L = K := hKmin L ⟨hPL, hLmap⟩ hLleK
    have hApreTop : Apre = ⊤ := by
      apply top_unique
      intro x _
      have hxL : (x : H) ∈ L := by
        rw [hLtop]
        exact x.property
      obtain ⟨y, hy, hyx⟩ := hxL
      have hyEq : y = x := K.subtype_injective hyx
      simpa [hyEq] using hy
    calc
      A = Apre.map q := hApreMap.symm
      _ = ⊤ := by rw [hApreTop, Subgroup.map_top_of_surjective q hq]
  have hcoreQ : pCore 2 Q = ⊥ := by
    simpa [Q, O] using pCore_quotient_pCore_eq_bot' (G := K) 2
  have hkerLe : fbar.ker ≤ frattini Q :=
    ker_le_frattini_of_sylow_minimal U fbar hfbar hminQ hcoreQ
  have hPhiLe : frattini Q ≤ fbar.ker := by
    have hle := frattini_le_comap_frattini_of_surjective hfbar
    simpa [isSL2Two_frattini_eq_bot hD] using hle
  have hker : fbar.ker = frattini Q := le_antisymm hkerLe hPhiLe
  refine ⟨K, hPK, hKmap, ?_⟩
  change IsSL2Two (Q ⧸ frattini Q)
  obtain ⟨eD⟩ := hD
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective fbar hfbar).trans eD)⟩

/-- A Sylow-preserving `SL₂(2)` Frattini lift, with the construction's image
equality omitted from the conclusion. -/
public theorem exists_sylow_overgroup_with_sl2Frattini_quotient
    {H : Type u} [Group H] [Finite H]
    {D : Type v} [Group D] [Finite D]
    (_hsolv : Group.IsSolvable H) (P : Sylow 2 H)
    (f : H →* D) (hf : Function.Surjective f) (hD : IsSL2Two D) :
    ∃ K : Subgroup H, (P : Subgroup H) ≤ K ∧
      IsSL2Two ((K ⧸ pCore 2 K) ⧸ frattini (K ⧸ pCore 2 K)) := by
  obtain ⟨K, hPK, _hKmap, hK⟩ :=
    exists_sylow_overgroup_with_sl2Frattini_quotient_and_map_eq_top
      _hsolv P f hf hD
  exact ⟨K, hPK, hK⟩

end Stellmacher.SectionTwo

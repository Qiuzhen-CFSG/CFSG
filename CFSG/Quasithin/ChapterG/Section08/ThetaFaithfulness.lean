module

public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import CFSG.Quasithin.ChapterG.Section08.Basic
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.GroupTheory.PGroup.OddOmegaAutomorphisms
public import Theory.GroupTheory.PGroup.SubnormalCore
public import FeitThompson.FinalTheorem

/-!
# Faithfulness on generalized-Fitting and Θ-subgroups

This proves both assertions of Aschbacher–Smith, *The Classification of
Quasithin Groups*, G.8.9, printed pp.350–351 (combined manuscript,
1 March 2004), and the existence and characteristicity of the actual Θ family.
The hypothesis in (1) uses C_{F*(H)}(X), as in the proof on p.351 and the
consumer A.4.4(b), p.58. The displayed F*(X) subscript on p.350 would make
that hypothesis vacuous and the assertion false. Subnormality remains
relative to F*(H).

The component dichotomy absorbs E(H) into X. In the present O₂(H)=1 setting,
each component has trivial two-core. The proved odd-order theorem supplies
an involution, which cannot be central; quasisimplicity therefore makes the
prime-order elements generate the component. After layer absorption, apply
the nilpotent G.8.4 kernel identity in F(H), and detect the remaining action
on prime-order elements using odd-prime omega detection. Generalized-Fitting
self-centralization is used through the explicit intrinsic-definition bridge
in Chapter B's `QuasisimpleSections.Group`.

For Θ, the supercritical factors retain their literal embeddings from O_p(H).
Their characteristicity gives ambient characteristicity. Centralizing E(H)
inside F*(H) puts an element in F(H); a prime-order element there lies in its
corresponding p-core, where the supercritical centralizer condition applies.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section08
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSections
variable {H : Type*} [Group H]

private theorem layer_characteristic : (componentLayer H).Characteristic := by
  apply characteristic_iff_map_le.mpr
  intro e
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro L hL
  exact map_le_iff_le_comap.mp (le_sSup (hL.map_equiv e))

/-- Every member of Θ(H) is characteristic in the ambient group. -/
theorem IsThetaSubgroup.characteristic {θ : Subgroup H} (hθ : IsThetaSubgroup θ) :
    θ.Characteristic := by
  obtain ⟨D, hD, rfl⟩ := hθ
  let : (componentLayer H).Characteristic := layer_characteristic
  have (p : FittingPrimes H) : ((D p).map (pCore p.val H).subtype).Characteristic := by
    let : (D p).Characteristic := (hD p).characteristic
    infer_instance
  infer_instance

/-- Every member of Θ(H) is normal in the ambient group. -/
theorem IsThetaSubgroup.normal {θ : Subgroup H} (hθ : IsThetaSubgroup θ) :
    θ.Normal := by
  let := hθ.characteristic
  infer_instance

/-- The actual ambient layer is contained in each member of Θ(H). -/
theorem IsThetaSubgroup.layer_le {θ : Subgroup H} (hθ : IsThetaSubgroup θ) :
    componentLayer H ≤ θ := by
  obtain ⟨D, _, rfl⟩ := hθ
  exact le_sup_left

variable [Finite H]

/-- The embedded supercritical factors and the layer lie in F*(H). -/
theorem IsThetaSubgroup.le_generalizedFitting {θ : Subgroup H}
    (hθ : IsThetaSubgroup θ) : θ ≤ generalizedFitting H := by
  obtain ⟨D, hD, rfl⟩ := hθ
  apply sup_le le_sup_right
  refine iSup_le fun p => ?_
  let : Fact p.val.Prime := ⟨p.property.1⟩
  exact (map_subtype_le (D p)).trans ((pCore_le_fitting H p.val).trans le_sup_left)

omit [Finite H] in
/-- A Θ-subgroup is subnormal relative to the actual F*(H). -/
theorem IsThetaSubgroup.subnormal {θ : Subgroup H} (hθ : IsThetaSubgroup θ) :
    (θ.subgroupOf (generalizedFitting H)).IsSubnormal := by
  let := hθ.normal
  exact (inferInstance : (θ.subgroupOf (generalizedFitting H)).Normal).isSubnormal

private theorem pSubgroup_le_core_of_nilpotent_normal (p : ℕ) [Fact p.Prime]
    (N Q : Subgroup H) [N.Normal] (hN : Group.IsNilpotent N)
    (hQ : IsPGroup p Q) (hQN : Q ≤ N) : Q ≤ pCore p H := by
  have hQNp : IsPGroup p (Q.subgroupOf N) := hQ.comap_subtype
  obtain ⟨S, hS⟩ := hQNp.exists_le_sylow
  have hm := map_mono (f := N.subtype) hS
  rw [map_subgroupOf_eq_of_le hQN] at hm
  exact hm.trans (S.map_le_pCore inferInstance hN p)

/-- The Fitting subgroup has odd order when the ambient two-core is trivial. -/
theorem fitting_odd_of_twoCore_eq_bot (hcore : pCore 2 H = ⊥) :
    Odd (Nat.card (fittingSubgroup H)) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro hd
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 (fittingSubgroup H) := default
  have hb : S.map (fittingSubgroup H).subtype = ⊥ :=
    bot_unique ((S.map_le_pCore inferInstance inferInstance 2).trans hcore.le)
  have hb' : (S : Subgroup (fittingSubgroup H)) = ⊥ :=
    (map_eq_bot_iff_of_injective _ (fittingSubgroup H).subtype_injective).mp hb
  exact S.ne_bot_of_dvd_card hd hb'

/-- The family Θ(H) is nonempty when O₂(H)=1, by supercritical existence. -/
theorem exists_thetaSubgroup (hcore : pCore 2 H = ⊥) :
    ∃ θ : Subgroup H, IsThetaSubgroup θ := by
  have hex (p : FittingPrimes H) :
      ∃ D : Subgroup (pCore p.val H), IsSupercriticalPSubgroup p.val D := by
    let : Fact p.val.Prime := ⟨p.property.1⟩
    apply IsPGroup.exists_supercriticalPSubgroup pCore_isPGroup
    intro he
    have hd := p.property.2
    rw [he] at hd
    exact (fitting_odd_of_twoCore_eq_bot hcore).not_two_dvd_nat hd
  choose D hD using hex
  exact ⟨componentLayer H ⊔ ⨆ p, (D p).map (pCore p.val H).subtype, D, hD, rfl⟩

private theorem layer_centralizes_fitting :
    componentLayer H ≤ centralizer (fittingSubgroup H : Set H) := by
  apply sSup_le
  intro L hL
  exact commutator_eq_bot_iff_le_centralizer.mp
    (GorensteinWalter.component_centralizes_internal_fitting ((component_iff_legacy L).mp hL))

omit [Finite H] in
private theorem center_layer_le_fitting :
    (center (componentLayer H)).map (componentLayer H).subtype ≤ fittingSubgroup H := by
  let : (componentLayer H).Characteristic := layer_characteristic
  refine le_sSup ⟨inferInstance, ?_⟩
  have : Group.IsNilpotent (center (componentLayer H)) := by
    refine ⟨1, ?_⟩
    rw [Subgroup.upperCentralSeries_one_eq_top_iff]
    infer_instance
  exact Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _
    (componentLayer H).subtype_injective)

/-- The centralizer of E(H) inside F*(H) lies in F(H). -/
theorem generalizedFitting_inf_centralizer_layer_le_fitting :
    generalizedFitting H ⊓ centralizer (componentLayer H : Set H) ≤ fittingSubgroup H := by
  intro x hx
  obtain ⟨f, hf, e, he, hxe⟩ :=
    GorensteinWalter.mem_sup_decompose_of_centralizes hx.1 layer_centralizes_fitting
  have hfc : f ∈ centralizer (componentLayer H : Set H) :=
    le_centralizer_iff.mp layer_centralizes_fitting hf
  have heq : e = f⁻¹ * x := by rw [hxe]; group
  have hec : e ∈ centralizer (componentLayer H : Set H) := by
    rw [heq]
    exact (centralizer _).mul_mem ((centralizer _).inv_mem hfc) hx.2
  have heF : e ∈ fittingSubgroup H := center_layer_le_fitting
    ⟨⟨e, he⟩, mem_center_iff.mpr (fun y => Subtype.ext (hec y y.property)), rfl⟩
  rw [hxe]
  exact (fittingSubgroup H).mul_mem hf heF

/-- A Θ-subgroup contains every prime-order element of its centralizer in F*(H). -/
theorem IsThetaSubgroup.primeOrderGenerated_centralizer_le {θ : Subgroup H}
    (hθ : IsThetaSubgroup θ) :
    primeOrderGenerated (generalizedFitting H ⊓ centralizer (θ : Set H)) ≤ θ := by
  obtain ⟨D, hD, rfl⟩ := hθ
  have hDθ (p : FittingPrimes H) : (D p).map (pCore p.val H).subtype ≤
      componentLayer H ⊔ ⨆ p, (D p).map (pCore p.val H).subtype :=
    (le_iSup (fun p : FittingPrimes H => (D p).map (pCore p.val H).subtype) p).trans
      le_sup_right
  apply (closure_le _).mpr
  rintro x ⟨hx, hp⟩
  have hxF : x ∈ fittingSubgroup H := generalizedFitting_inf_centralizer_layer_le_fitting
    ⟨hx.1, centralizer_le (show componentLayer H ≤ componentLayer H ⊔
      ⨆ p, (D p).map (pCore p.val H).subtype from le_sup_left) hx.2⟩
  let p : FittingPrimes H := ⟨orderOf x, hp, by
    exact (orderOf_coe (⟨x, hxF⟩ : fittingSubgroup H)).symm ▸
      orderOf_dvd_natCard (⟨x, hxF⟩ : fittingSubgroup H)⟩
  let : Fact p.val.Prime := ⟨hp⟩
  have hxP : x ∈ pCore p.val H := by
    apply pSubgroup_le_core_of_nilpotent_normal p.val (fittingSubgroup H) (zpowers x)
      inferInstance (IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, p]))
      (zpowers_le.mpr hxF)
    exact mem_zpowers x
  have hxD : (⟨x, hxP⟩ : pCore p.val H) ∈ D p := by
    apply (hD p).order_p_mem
    · intro y hy
      exact Subtype.ext (hx.2 y (hDθ p ⟨y, hy, rfl⟩))
    · exact (orderOf_coe (⟨x, hxP⟩ : pCore p.val H)).symm
  exact hDθ p ⟨⟨x, hxP⟩, hxD, rfl⟩

private theorem twoSubgroup_centralizes_of_primeOrderGenerated
    (U Q : Subgroup H) (hU : IsPGroup 2 U) (hQ : Group.IsNilpotent Q)
    (hodd : Odd (Nat.card Q)) (hnorm : U ≤ normalizer (Q : Set H))
    (hfix : U ≤ centralizer (primeOrderGenerated Q : Set H)) :
    U ≤ centralizer (Q : Set H) := by
  let : Group.IsNilpotent Q := hQ
  let ρ : U →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion hnorm)
  intro a ha
  let a₀ : U := ⟨a, ha⟩
  have hpfix (p : (Nat.card Q).primeFactors.attach) :
      MulAut.characteristic (pCore p.val.val Q) (ρ a₀) = 1 := by
    have hp : p.val.val.Prime := Nat.prime_of_mem_primeFactors p.val.property
    let : Fact p.val.val.Prime := ⟨hp⟩
    have hp2 : p.val.val ≠ 2 := by
      intro he
      have hd := Nat.dvd_of_mem_primeFactors p.val.property
      rw [he] at hd
      exact hodd.not_two_dvd_nat hd
    apply MulAut.eq_one_of_coprime_of_fixes_prime_roots pCore_isPGroup hp2
    · obtain ⟨n, hn⟩ := hU.exists_orderOf_dvd_pow a₀
      exact (((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right n).of_dvd_right
        ((orderOf_map_dvd (MulAut.characteristic (pCore p.val.val Q)) (ρ a₀)).trans
          ((orderOf_map_dvd ρ a₀).trans hn))
    · intro x hx
      apply Subtype.ext
      apply Subtype.ext
      have hxpow : (x.val.val : H) ^ p.val.val = 1 :=
        congrArg (fun y : pCore p.val.val Q => (y.val.val : H)) hx
      by_cases he : (x.val.val : H) = 1
      · change a * (x.val.val : H) * a⁻¹ = (x.val.val : H)
        simp [he]
      · have hxprime : (orderOf (x.val.val : H)).Prime := by
          rw [orderOf_eq_prime_iff.mpr ⟨hxpow, he⟩]
          exact hp
        have hc := hfix ha _ (Subgroup.subset_closure ⟨x.val.property, hxprime⟩)
        change a * (x.val.val : H) * a⁻¹ = (x.val.val : H)
        rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have hρ : ρ a₀ = 1 := by
    have ht : (⊤ : Subgroup Q) ≤ (ρ a₀).toMonoidHom.eqLocus (MonoidHom.id Q) := by
      rw [← fitting_eq_top_of_nilpotent Q, fitting_eq_sup_pCore]
      apply iSup_le
      intro p x hx
      have hh := DFunLike.congr_fun (hpfix p) (⟨x, hx⟩ : pCore p.val.val Q)
      exact congrArg Subtype.val hh
    apply MulEquiv.ext
    intro x
    exact ht (mem_top x)
  intro x hx
  have hh := congrArg (fun b : MulAut Q => (b ⟨x, hx⟩ : H)) hρ
  change a * x * a⁻¹ = x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The faithful-centralizer argument after absorption of the ambient layer.
Only the kernel inside U is used, so no normalization premise on U is needed
for this intersection formulation. -/
theorem faithful_of_layer_le (hcore : pCore 2 H = ⊥) (X U : Subgroup H)
    (hXF : X ≤ generalizedFitting H) (hEX : componentLayer H ≤ X)
    (hprime : primeOrderGenerated (generalizedFitting H ⊓ centralizer (X : Set H)) ≤ X)
    (hU : IsPGroup 2 U) : U ⊓ centralizer (X : Set H) = ⊥ := by
  let F := fittingSubgroup H
  let Y := F ⊓ X
  let K := F ⊓ centralizer (Y : Set H)
  let C := U ⊓ centralizer (X : Set H)
  have hC2 : IsPGroup 2 C := hU.to_le inf_le_left
  have hCY : C ≤ centralizer (Y : Set H) :=
    inf_le_right.trans (centralizer_le (show Y ≤ X from inf_le_right))
  have hCFnorm : C ≤ normalizer (F : Set H) := le_normalizer_of_normal
  have hCnorm : C ≤ normalizer (K : Set H) :=
    (le_inf hCFnorm (hCY.trans (centralizer (Y : Set H)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hKX : K ≤ centralizer (X : Set H) := by
    intro k hk x hx
    obtain ⟨f, hf, e, he, hxe⟩ :=
      GorensteinWalter.mem_sup_decompose_of_centralizes (hXF hx) layer_centralizes_fitting
    have hfX : f ∈ X := by
      have heq : f = x * e⁻¹ := by rw [hxe]; group
      rw [heq]
      exact X.mul_mem hx (X.inv_mem (hEX he))
    have hkf : f * k = k * f := hk.2 f ⟨hf, hfX⟩
    have hke : e * k = k * e :=
      le_centralizer_iff.mp layer_centralizes_fitting hk.1 e he
    rw [hxe]
    calc
      (f * e) * k = f * (e * k) := mul_assoc _ _ _
      _ = f * (k * e) := by rw [hke]
      _ = (k * f) * e := by rw [← mul_assoc, hkf]
      _ = k * (f * e) := mul_assoc _ _ _
  have hprimeK : primeOrderGenerated K ≤ X := by
    apply le_trans _ hprime
    apply Subgroup.closure_mono
    intro x hx
    exact ⟨⟨fitting_le_generalizedFitting H hx.1.1, hKX hx.1⟩, hx.2⟩
  have hKnil : Group.IsNilpotent K := by
    apply Subgroup.isNilpotent_of_ker_le_center (inclusion (show K ≤ F from inf_le_left))
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (inclusion_injective _)]
    exact bot_le
  have hoddF := fitting_odd_of_twoCore_eq_bot hcore
  have hoddK : Odd (Nat.card K) := hoddF.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hCK : C ≤ centralizer (K : Set H) :=
    twoSubgroup_centralizes_of_primeOrderGenerated C K hC2 hKnil hoddK hCnorm
      (inf_le_right.trans (centralizer_le hprimeK))
  have hCF : C ≤ centralizer (F : Set H) := by
    have hcop : Nat.Coprime (Nat.card C) (Nat.card F) := by
      obtain ⟨n, hn⟩ := hC2.exists_card_eq
      rw [hn]
      exact hoddF.coprime_two_left.pow_left n
    have hh := nilpotent_centralizer_restriction_kernel F Y C inferInstance
      inf_le_left hCFnorm hCY hcop
    have hle : C ≤ C ⊓ centralizer (K : Set H) := le_inf le_rfl hCK
    change C ⊓ centralizer (K : Set H) = C ⊓ centralizer (F : Set H) at hh
    rw [hh] at hle
    exact hle.trans inf_le_right
  have hCE : C ≤ centralizer (componentLayer H : Set H) :=
    inf_le_right.trans (centralizer_le hEX)
  have hCstar : C ≤ centralizer (generalizedFitting H : Set H) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hCF) (le_centralizer_iff.mp hCE)
  exact (disjoint_centralizer_fitting hcore C hC2).eq_bot_of_le hCstar

/-- In an ambient group with trivial two-core, each component is generated by
its prime-order elements. The odd-order theorem supplies a noncentral involution. -/
theorem component_primeOrderGenerated_eq (hcore : pCore 2 H = ⊥)
    (L : Subgroup H) (hL : IsComponent H L) : primeOrderGenerated L = L := by
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hcoreL : pCore 2 L = ⊥ := by
    have hh := pCoreAmbient_mono_of_isSubnormalIn L ⊤ 2 le_top hL.1.subgroupOf
    change (pCore 2 L).map L.subtype ≤ (pCore 2 (⊤ : Subgroup H)).map
      (topEquiv : (⊤ : Subgroup H) ≃* H).toMonoidHom at hh
    rw [pCore_map_iso, hcore] at hh
    exact (map_eq_bot_iff_of_injective _ L.subtype_injective).mp (bot_unique hh)
  have heven : 2 ∣ Nat.card L := by
    by_contra hn
    have hodd : Odd (Nat.card L) := by rwa [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact Group.IsPerfect.not_isSolvable L (odd_order_theorem L hodd)
  let N : Subgroup L := closure {x : L | (orderOf x).Prime}
  have hN : N.Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro e
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    intro x hx
    change e x ∈ N
    apply Subgroup.subset_closure
    simpa only [Set.mem_ofPred_eq, e.orderOf_eq] using hx
  let := hN
  have hNt : N = ⊤ := by
    rcases IsQuasisimple.normal_le_center_or_eq_top N with hc | ht
    · let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨i, hi⟩ := exists_prime_orderOf_dvd_card' 2 heven
      have hiN : i ∈ N := Subgroup.subset_closure
        (by simpa only [Set.mem_ofPred_eq, hi] using Nat.prime_two)
      have hiZ : i ∈ center L := hc hiN
      have hZ : (zpowers i).Normal := by
        refine ⟨fun n hn g => ?_⟩
        have hc := mem_center_iff.mp (zpowers_le.mpr hiZ hn) g
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]
        exact hn
      have hP : IsPGroup 2 (zpowers i) :=
        IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hi)
      have hle : zpowers i ≤ pCore 2 L := le_sSup ⟨hZ, hP⟩
      have hiC : i ∈ pCore 2 L := hle (mem_zpowers i)
      rw [hcoreL, mem_bot] at hiC
      simp only [hiC, orderOf_one] at hi
      exact (by omega : False).elim
    · exact ht
  apply le_antisymm
  · exact (closure_le _).mpr (fun _ hx => hx.1)
  · have hNL : N ≤ (primeOrderGenerated L).comap L.subtype := by
      apply (closure_le _).mpr
      intro x hx
      exact Subgroup.subset_closure ⟨x.property, (orderOf_coe x).symm ▸ hx⟩
    intro x hx
    exact hNL (hNt ▸ mem_top (⟨x, hx⟩ : L))

/-- The prime-order centralizer condition absorbs the whole layer.
Subnormality is relative to the actual F*(H). -/
theorem layer_le_of_subnormal_prime_centralizer (hcore : pCore 2 H = ⊥)
    (X : Subgroup H)
    (hXF : X ≤ generalizedFitting H)
    (hsub : (X.subgroupOf (generalizedFitting H)).IsSubnormal)
    (hprime : primeOrderGenerated (generalizedFitting H ⊓ centralizer (X : Set H)) ≤ X) :
    componentLayer H ≤ X := by
  have hXsub : X.IsSubnormal := hsub.trans hXF
    (inferInstance : (generalizedFitting H).Normal).isSubnormal
  apply sSup_le
  intro L hL
  rcases hL.subnormal_dichotomy X hXsub with hLX | hc
  · exact hLX
  · rw [← component_primeOrderGenerated_eq hcore L hL]
    apply le_trans _ hprime
    apply Subgroup.closure_mono
    intro x hx
    exact ⟨⟨component_le_generalizedFitting H L hL hx.1,
      commutator_eq_bot_iff_le_centralizer.mp hc hx.1⟩, hx.2⟩

/-- G.8.9(1), with the intended ambient-H centralizer hypothesis from the
proof and A.4.4(b). Relative subnormality is retained exactly. -/
theorem lemma_G_8_9_1 (hcore : pCore 2 H = ⊥)
    (X U : Subgroup H) (hXF : X ≤ generalizedFitting H)
    (hsub : (X.subgroupOf (generalizedFitting H)).IsSubnormal)
    (hprime : primeOrderGenerated (generalizedFitting H ⊓ centralizer (X : Set H)) ≤ X)
    (hU : IsPGroup 2 U) (_hnorm : U ≤ normalizer (X : Set H)) :
    U ⊓ centralizer (X : Set H) = ⊥ :=
  faithful_of_layer_le hcore X U hXF
    (layer_le_of_subnormal_prime_centralizer hcore X hXF hsub hprime) hprime hU

/-- G.8.9(2): every two-subgroup acts faithfully on each actual Θ-subgroup. -/
theorem lemma_G_8_9_2 (hcore : pCore 2 H = ⊥) {θ : Subgroup H}
    (hθ : IsThetaSubgroup θ) (U : Subgroup H) (hU : IsPGroup 2 U) :
    U ⊓ centralizer (θ : Set H) = ⊥ :=
  faithful_of_layer_le hcore θ U hθ.le_generalizedFitting hθ.layer_le
    hθ.primeOrderGenerated_centralizer_le hU

end CFSG.Quasithin.ChapterG.Section08

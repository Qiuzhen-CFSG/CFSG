module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Terminal.Conjugacy
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Terminal.MuSylow

/-!
# Held's twelve-element lambda orbit

Let K contain the displayed D, have order 384, and normalize the actual S.
Under the source fusion assumptions, the orbit of lambda under K has order
exactly twelve. The construction of K remains with the terminal assembly.

The six local D-orbits in S have sizes 1, 1, 2, 4, 4, 4, represented by
1, pi, mu, tau, lambda, pi*lambda. Their conjugators are checked in the actual
model. Pi--mu fusion and pi--lambda separation therefore make the lambda
orbit size divisible by four. Its local centralizer has order 32, bounding
the full orbit by twelve.

An element v of order three in K cycles the nonidentity elements of
`terminalFour`, namely pi, mu and pi*mu: fixing pi would put v in the displayed
two-group. If v also fixed lambda, the relative centralizer order would be
divisible by 96, bounding its orbit by four. But v sends the local conjugate
mu*lambda to pi*lambda or pi*mu*lambda, both outside the four local conjugates.
This excludes three from the relative centralizer order. Orbit sizes four
and eight are consequently impossible, leaving twelve.

Conjugation here is g*x*g^-1; the two cycle orientations cover the source's
convention g^-1*x*g. The local orbit coordinates follow the checked six-orbit
calculation in Fusion/LambdaSeparation/NormalizerAction, with narrow imports.
All finite calculations are checked by kernel reduction.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.6, printed p.229.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

private abbrev OrbitConjCode := Fin 2 × Fin 2 × Fin 2
private def orbitConjugator (b : OrbitConjCode) : H :=
  mup ^ b.1.val * taup ^ b.2.1.val * xi ^ b.2.2.val
private def orbitRepresentative : Fin 6 → H := ![1, pi, mu, tau, lam, pi * lam]
private def terminalOrbitLabel (a : BaseCode) : Fin 6 :=
  if a.2.2.2 = 1 then (if a.1 = a.2.1 * a.2.2.1 then 4 else 5)
  else if a.2.2.1 = 1 then 3 else if a.2.1 = 1 then 2 else if a.1 = 1 then 1 else 0

private theorem orbitConjugator_mem (b : OrbitConjCode) : orbitConjugator b ∈ modelD := by
  have h (i : Fin 7) : (![pi, mu, mup, tau, taup, lam, xi] : Fin 7 → H) i ∈ modelD :=
    subset_closure ⟨i, rfl⟩
  exact modelD.mul_mem (modelD.mul_mem (modelD.pow_mem (h 2) _)
    (modelD.pow_mem (h 4) _)) (modelD.pow_mem (h 6) _)

private theorem terminalOrbitLabel_conjugate : ∀ a : BaseCode, ∃ b : OrbitConjCode,
    orbitConjugator b * orbitRepresentative (terminalOrbitLabel a) * (orbitConjugator b)⁻¹ =
      elementaryWord 1 a := by decide +kernel

private theorem terminalWord_inj : Function.Injective (elementaryWord 1) := by decide +kernel

private def orbitSelected (b : Fin 3 → Bool) (a : BaseCode) : Prop :=
  (terminalOrbitLabel a = 3 ∧ b 0 = true) ∨
    (terminalOrbitLabel a = 4 ∧ b 1 = true) ∨ (terminalOrbitLabel a = 5 ∧ b 2 = true)
private instance (b : Fin 3 → Bool) (a : BaseCode) : Decidable (orbitSelected b a) := by
  unfold orbitSelected
  infer_instance
private theorem orbitSelected_card : ∀ b : Fin 3 → Bool,
    Fintype.card {a : BaseCode // orbitSelected b a} % 4 = 0 := by decide +kernel

private theorem terminal_code_card_mod_four (p : H → Prop)
    (hconj : ∀ g ∈ modelD, ∀ x, p (g * x * g⁻¹) ↔ p x)
    (hone : ¬ p 1) (hpi : ¬ p pi) (hmu : ¬ p mu) :
    Nat.card {a : BaseCode // p (elementaryWord 1 a)} % 4 = 0 := by
  classical
  let b : Fin 3 → Bool := ![decide (p tau), decide (p lam), decide (p (pi * lam))]
  have hp (a : BaseCode) : p (elementaryWord 1 a) ↔ p (orbitRepresentative (terminalOrbitLabel a)) := by
    obtain ⟨c, hc⟩ := terminalOrbitLabel_conjugate a
    rw [← hc]
    exact hconj _ (orbitConjugator_mem c) _
  have hs (a : BaseCode) : p (elementaryWord 1 a) ↔ orbitSelected b a := by
    rw [hp]
    unfold orbitSelected
    generalize terminalOrbitLabel a = i
    fin_cases i <;> simp [orbitRepresentative, b, hone, hpi, hmu]
  rw [Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl BaseCode) hs), Nat.card_eq_fintype_card]
  exact orbitSelected_card b

private def localLambdaWord : Fin 4 → H := ![lam, mu * lam, tau * lam, pi * mu * tau * lam]
private theorem localLambdaWord_inj : Function.Injective localLambdaWord := by decide +kernel
private theorem localLambdaWord_conj : ∀ i : Fin 4, ∃ b : OrbitConjCode,
    orbitConjugator b * lam * (orbitConjugator b)⁻¹ = localLambdaWord i := by decide +kernel
private theorem localLambdaWord_separate : ∀ i : Fin 4,
    localLambdaWord i ≠ pi * lam ∧ localLambdaWord i ≠ pi * mu * lam := by decide +kernel

universe u
variable {G : Type u} [Group G]

private theorem terminal_orbit_self (K : Subgroup G) (x : G) : x ∈ terminalOrbit K x := by
  exact ⟨1, by simp⟩

private theorem terminal_orbit_stable (K : Subgroup G) {g : G} (hg : g ∈ K) (x y : G) :
    g * y * g⁻¹ ∈ terminalOrbit K x ↔ y ∈ terminalOrbit K x := by
  simp only [mem_terminalOrbit]
  constructor
  · rintro ⟨k, hk, he⟩
    refine ⟨g⁻¹ * k, K.mul_mem (K.inv_mem hg) hk, ?_⟩
    calc
      (g⁻¹ * k) * x * (g⁻¹ * k)⁻¹ = g⁻¹ * (k * x * k⁻¹) * g := by group
      _ = y := by rw [he]; group
  · rintro ⟨k, hk, he⟩
    refine ⟨g * k, K.mul_mem hg hk, ?_⟩
    calc
      (g * k) * x * (g * k)⁻¹ = g * (k * x * k⁻¹) * g⁻¹ := by group
      _ = g * y * g⁻¹ := by rw [he]

variable [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

omit [Finite G] in
private theorem terminal_orbit_subset_S (K : Subgroup G)
    (hKN : K ≤ normalizer (ambientElementary D e 1 : Set G)) :
    terminalOrbit K (D.a10ModelEmbedding e lam) ⊆ ambientElementary D e 1 := by
  rintro x ⟨g, rfl⟩
  exact (mem_normalizer_iff.mp (hKN g.property) _).mp
    (mem_map_of_mem _ (elementaryGenerators_mem 1 3))

private theorem terminal_orbit_mod_four (K : Subgroup G)
    (hDK : ambientD D e ≤ K) (hKN : K ≤ normalizer (ambientElementary D e 1 : Set G))
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam)) :
    Nat.card (terminalOrbit K (D.a10ModelEmbedding e lam)) % 4 = 0 := by
  let f := D.a10ModelEmbedding e
  let p : H → Prop := fun x => f x ∈ terminalOrbit K (f lam)
  have hconj : ∀ g ∈ modelD, ∀ x, p (g * x * g⁻¹) ↔ p x := by
    intro g hg x
    simpa only [p, map_mul, map_inv] using terminal_orbit_stable K (hDK ⟨g, hg, rfl⟩) (f lam) (f x)
  have hclass {x : H} (hx : p x) : IsConj (f lam) (f x) := by
    obtain ⟨g, hg⟩ := hx
    exact isConj_iff.mpr ⟨g, hg⟩
  have hone : ¬ p 1 := by
    intro h
    have he : f lam = 1 := isConj_one_left.mp (by simpa using hclass h)
    exact (show lam ≠ 1 by decide +kernel) ((map_eq_one_iff f (D.a10ModelEmbedding_injective e)).mp he)
  have hpi : ¬ p pi := by
    intro h
    exact hlam (by simpa only [f, D.a10ModelEmbedding_central e] using (hclass h).symm)
  have hmu' : ¬ p mu := fun h => hlam (hmu.trans (hclass h).symm)
  let b : {a : BaseCode // p (elementaryWord 1 a)} → terminalOrbit K (f lam) :=
    fun a => ⟨f (elementaryWord 1 a.1), a.2⟩
  have hb : Function.Bijective b := by
    constructor
    · intro a c hac
      apply Subtype.ext
      exact terminalWord_inj (D.a10ModelEmbedding_injective e (congrArg (fun z : terminalOrbit K (f lam) => z.val) hac))
    · rintro ⟨x, hx⟩
      obtain ⟨w, hw, rfl⟩ := terminal_orbit_subset_S D e K hKN hx
      obtain ⟨a, rfl⟩ := (mem_elementary 1 w).mp hw
      exact ⟨⟨a, hx⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective b hb)]
  exact terminal_code_card_mod_four p hconj hone hpi hmu'

private theorem terminal_fused_in_S
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (htau : ¬ IsConj D.z (D.a10ModelEmbedding e tau))
    (hpl : ¬ IsConj D.z (D.a10ModelEmbedding e (pi * lam)))
    {x : G} (hx : x ∈ ambientElementary D e 1) (hc : IsConj D.z x) :
    x = D.z ∨ x = D.a10ModelEmbedding e mu ∨ x = D.a10ModelEmbedding e (pi * mu) := by
  let f := D.a10ModelEmbedding e
  obtain ⟨w, hw, rfl⟩ := hx
  obtain ⟨a, rfl⟩ := (mem_elementary 1 w).mp hw
  obtain ⟨b, hb⟩ := terminalOrbitLabel_conjugate a
  have hr : IsConj D.z (f (orbitRepresentative (terminalOrbitLabel a))) := by
    apply hc.trans
    apply IsConj.symm
    apply f.map_isConj
    exact isConj_iff.mpr ⟨_, hb⟩
  have hl : terminalOrbitLabel a = 1 ∨ terminalOrbitLabel a = 2 := by
    generalize terminalOrbitLabel a = i at hr ⊢
    fin_cases i <;> simp_all [orbitRepresentative, f, D.z_ne_one]
  have hw : ∀ a : BaseCode, (terminalOrbitLabel a = 1 ∨ terminalOrbitLabel a = 2) →
      elementaryWord 1 a = pi ∨ elementaryWord 1 a = mu ∨ elementaryWord 1 a = pi * mu := by
    decide +kernel
  rcases hw a hl with he | he | he
  · exact Or.inl (by rw [he, D.a10ModelEmbedding_central e])
  · exact Or.inr (Or.inl (congrArg f he))
  · exact Or.inr (Or.inr (congrArg f he))

/-- Every element of order three in K acts as a three-cycle on the nonidentity
    elements of the source four-group <pi,mu>. -/
public theorem terminal_order_three_action (K : Subgroup G)
    (hKN : K ≤ normalizer (ambientElementary D e 1 : Set G))
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (htau : ¬ IsConj D.z (D.a10ModelEmbedding e tau))
    (hpl : ¬ IsConj D.z (D.a10ModelEmbedding e (pi * lam)))
    (v : G) (hv : v ∈ K) (hv3 : orderOf v = 3) :
    let f := D.a10ModelEmbedding e
    let c := MulAut.conj v
    (c (f pi) = f mu ∧ c (f mu) = f (pi * mu)) ∨
      (c (f pi) = f (pi * mu) ∧ c (f mu) = f pi) := by
  let f := D.a10ModelEmbedding e
  let c := MulAut.conj v
  have hp : f pi = D.z := D.a10ModelEmbedding_central e
  have hc (x : G) (hx : x ∈ ambientElementary D e 1) (hcx : IsConj D.z x) :
      c x = f pi ∨ c x = f mu ∨ c x = f (pi * mu) := by
    rw [hp]
    exact terminal_fused_in_S D e hlam htau hpl
      ((mem_normalizer_iff.mp (hKN hv) x).mp hx)
      (hcx.trans (isConj_iff.mpr ⟨v, rfl⟩))
  have hcp := hc (f pi) (mem_map_of_mem _ (pi_mem_elementary 1)) (hp ▸ IsConj.refl D.z)
  have hcm := hc (f mu) (mem_map_of_mem _ (mu_mem_elementary 1)) hmu
  have hn : c (f pi) ≠ f pi := by
    intro he
    have hvD : v ∈ ambientD D e := by
      rw [← normalizer_S_inf_centralizer D e]
      refine ⟨hKN hv, mem_centralizer_singleton_iff.mpr ?_⟩
      have he' : v * D.z * v⁻¹ = D.z := by
        change v * f pi * v⁻¹ = f pi at he
        simpa only [hp] using he
      exact (mul_inv_eq_iff_eq_mul.mp he')
    have hd := (ambientD D e).orderOf_dvd_natCard hvD
    rw [hv3, ambientD_card] at hd
    norm_num at hd
  have hc3 (x : G) : c (c (c x)) = x := by
    have hpow : v ^ 3 = 1 := by simpa only [hv3] using pow_orderOf_eq_one v
    have he : c ^ 3 = 1 := by
      change (MulAut.conj v) ^ 3 = 1
      rw [← map_pow, hpow, map_one]
    exact congrArg (fun a : MulAut G => a x) he
  have hpm : f pi ≠ f mu := fun h => (show Coordinates.pi ≠ mu by decide +kernel) (D.a10ModelEmbedding_injective e h)
  have hmm : f mu * f mu = 1 := by
    rw [← map_mul]
    exact (congrArg f (show mu * mu = 1 by decide +kernel)).trans (map_one f)
  rcases hcp with he | he | he
  · exact (hn he).elim
  · left
    refine ⟨he, ?_⟩
    rcases hcm with hm | hm | hm
    · have h := hc3 (f pi)
      rw [he, hm, he] at h
      exact (hpm h.symm).elim
    · exact (hpm (c.injective (he.trans hm.symm))).elim
    · exact hm
  · right
    refine ⟨he, ?_⟩
    rcases hcm with hm | hm | hm
    · exact hm
    · have h := hc3 (f pi)
      rw [he, f.map_mul, c.map_mul, he, hm, f.map_mul, mul_assoc, hmm, mul_one] at h
      exact (hn h).elim
    · exact (hpm (c.injective (he.trans hm.symm))).elim

omit [Finite G] in
private theorem terminal_lambda_centralizer_multiple (K : Subgroup G)
    (hDK : ambientD D e ≤ K) :
    32 ∣ Nat.card (K ⊓ centralizer ({D.a10ModelEmbedding e lam} : Set G) : Subgroup G) := by
  let f := D.a10ModelEmbedding e
  have hle : (terminalLocalCentralizer 0).map f ≤ K ⊓ centralizer ({f lam} : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    refine ⟨hDK ⟨y, terminalLocalCentralizer_le_modelD 0 hy, rfl⟩,
      mem_centralizer_singleton_iff.mpr ?_⟩
    have hc : y * lam = lam * y := mem_centralizer_singleton_iff.mp hy
    simpa only [map_mul] using congrArg f hc
  have hd := card_dvd_of_le hle
  rwa [card_map_of_injective (D.a10ModelEmbedding_injective e), terminalLocalCentralizer_card] at hd

/-- Held's order-three exclusion, using its action on <pi,mu> and the four
    actual local conjugates of lambda. -/
public theorem terminal_lambda_no_order_three (K : Subgroup G)
    (hDK : ambientD D e ≤ K) (hK : Nat.card K = 384)
    (hKN : K ≤ normalizer (ambientElementary D e 1 : Set G))
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (htau : ¬ IsConj D.z (D.a10ModelEmbedding e tau))
    (hpl : ¬ IsConj D.z (D.a10ModelEmbedding e (pi * lam)))
    (v : G) (hv : v ∈ K ⊓ centralizer ({D.a10ModelEmbedding e lam} : Set G)) :
    orderOf v ≠ 3 := by
  intro hv3
  let f := D.a10ModelEmbedding e
  let T : Set G := Set.range (fun i : Fin 4 => f (localLambdaWord i))
  have hT : T.ncard = 4 := by
    exact (Set.ncard_range_of_injective
      ((D.a10ModelEmbedding_injective e).comp localLambdaWord_inj)).trans (by simp)
  have hsub : T ⊆ terminalOrbit K (f lam) := by
    rintro x ⟨i, rfl⟩
    obtain ⟨b, hb⟩ := localLambdaWord_conj i
    apply (mem_terminalOrbit K _ _).mpr
    refine ⟨f (orbitConjugator b), hDK ⟨_, orbitConjugator_mem b, rfl⟩, ?_⟩
    simpa only [map_mul, map_inv] using congrArg f hb
  have hd32 := terminal_lambda_centralizer_multiple D e K hDK
  have hd3 : 3 ∣ Nat.card (K ⊓ centralizer ({f lam} : Set G) : Subgroup G) := by
    simpa only [hv3] using (K ⊓ centralizer ({f lam} : Set G)).orderOf_dvd_natCard hv
  have hd96 := (show Nat.Coprime 32 3 by decide).mul_dvd_of_dvd_of_dvd hd32 hd3
  have hc96 : 96 ≤ Nat.card (K ⊓ centralizer ({f lam} : Set G) : Subgroup G) :=
    Nat.le_of_dvd Nat.card_pos hd96
  have hlK : f lam ∈ K := hDK ⟨lam, elementary_le_modelD 1 (elementaryGenerators_mem 1 3), rfl⟩
  have hcount := terminalOrbit_card_mul K (f lam) hlK
  rw [hK] at hcount
  have hn : Nat.card (terminalOrbit K (f lam)) ≤ 4 := by nlinarith only [hcount, hc96]
  have heq : T = terminalOrbit K (f lam) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hT]; exact hn)
  have hml : f (mu * lam) ∈ terminalOrbit K (f lam) := hsub ⟨1, rfl⟩
  have hcl : MulAut.conj v (f lam) = f lam := by
    change v * f lam * v⁻¹ = f lam
    rw [mem_centralizer_singleton_iff.mp hv.2, mul_inv_cancel_right]
  have hconj : MulAut.conj v (f (mu * lam)) ∈ terminalOrbit K (f lam) :=
    (terminal_orbit_stable K hv.1 _ _).mpr hml
  rw [← heq] at hconj
  obtain ⟨i, hi⟩ := hconj
  have hact := terminal_order_three_action D e K hKN hmu hlam htau hpl v hv.1 hv3
  rcases hact with ⟨_, hm⟩ | ⟨_, hm⟩
  · change MulAut.conj v (f mu) = f (pi * mu) at hm
    rw [f.map_mul, (MulAut.conj v).map_mul, hm, hcl] at hi
    have he : localLambdaWord i = Coordinates.pi * mu * lam := by
      apply D.a10ModelEmbedding_injective e
      change f (localLambdaWord i) = f (pi * mu * lam)
      simpa only [f.map_mul] using hi
    exact (localLambdaWord_separate i).2 he
  · change MulAut.conj v (f mu) = f pi at hm
    rw [f.map_mul, (MulAut.conj v).map_mul, hm, hcl] at hi
    have he : localLambdaWord i = Coordinates.pi * lam := by
      apply D.a10ModelEmbedding_injective e
      change f (localLambdaWord i) = f (pi * lam)
      simpa only [f.map_mul] using hi
    exact (localLambdaWord_separate i).1 he

/-- The factor three is absent from the actual relative lambda-centralizer. -/
public theorem terminal_lambda_centralizer_not_dvd_three (K : Subgroup G)
    (hDK : ambientD D e ≤ K) (hK : Nat.card K = 384)
    (hKN : K ≤ normalizer (ambientElementary D e 1 : Set G))
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (htau : ¬ IsConj D.z (D.a10ModelEmbedding e tau))
    (hpl : ¬ IsConj D.z (D.a10ModelEmbedding e (pi * lam))) :
    ¬ 3 ∣ Nat.card (K ⊓ centralizer ({D.a10ModelEmbedding e lam} : Set G) : Subgroup G) := by
  intro hd
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 3 hd
  exact terminal_lambda_no_order_three D e K hDK hK hKN hmu hlam htau hpl v v.property
    ((Subgroup.orderOf_coe v).trans hv)

/-- The exact orbit size in Held, Lemma 2.6, p.229. The additional fusion
    premise and simplicity are retained for the source interface; their role
    is in constructing K, whose order and normalization are supplied here. -/
public theorem terminal_lambda_orbit_card [IsSimpleGroup G] (K : Subgroup G)
    (hDK : ambientD D e ≤ K) (hK : Nat.card K = 384)
    (hKN : K ≤ normalizer (ambientElementary D e 1 : Set G))
    (hmu : IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
    (htau : ¬ IsConj D.z (D.a10ModelEmbedding e tau))
    (hpl : ¬ IsConj D.z (D.a10ModelEmbedding e (pi * lam)))
    (_hadditional : IsConj D.z (D.a10ModelEmbedding e xi) ∨
      IsConj D.z (D.a10ModelEmbedding e (pi * xi)) ∨
      IsConj D.z (D.a10ModelEmbedding e (tau * lam * xi))) :
    Nat.card (terminalOrbit K (D.a10ModelEmbedding e lam)) = 12 := by
  let f := D.a10ModelEmbedding e
  have hmod := terminal_orbit_mod_four D e K hDK hKN hmu hlam
  change Nat.card (terminalOrbit K (f lam)) % 4 = 0 at hmod
  have hd32 := terminal_lambda_centralizer_multiple D e K hDK
  have hc32 : 32 ≤ Nat.card (K ⊓ centralizer ({f lam} : Set G) : Subgroup G) :=
    Nat.le_of_dvd Nat.card_pos hd32
  have hlK : f lam ∈ K := hDK ⟨lam, elementary_le_modelD 1 (elementaryGenerators_mem 1 3), rfl⟩
  have hcount := terminalOrbit_card_mul K (f lam) hlK
  rw [hK] at hcount
  have hnot3 := terminal_lambda_centralizer_not_dvd_three D e K hDK hK hKN hmu hlam htau hpl
  change ¬ 3 ∣ Nat.card (K ⊓ centralizer ({f lam} : Set G) : Subgroup G) at hnot3
  have hn : Nat.card (terminalOrbit K (f lam)) ≤ 12 := by nlinarith only [hcount, hc32]
  have hpos : 0 < Nat.card (terminalOrbit K (f lam)) :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨f lam, terminal_orbit_self K (f lam)⟩
  have hcases : Nat.card (terminalOrbit K (f lam)) = 4 ∨
      Nat.card (terminalOrbit K (f lam)) = 8 ∨ Nat.card (terminalOrbit K (f lam)) = 12 := by omega
  rcases hcases with hn | hn | hn
  · rw [hn] at hcount
    have hc : Nat.card (K ⊓ centralizer ({f lam} : Set G) : Subgroup G) = 96 := by omega
    exact (hnot3 (by rw [hc]; norm_num)).elim
  · rw [hn] at hcount
    have hc : Nat.card (K ⊓ centralizer ({f lam} : Set G) : Subgroup G) = 48 := by omega
    exact (hnot3 (by rw [hc]; norm_num)).elim
  · exact hn

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion

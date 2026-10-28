module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.SNormalizer.Overgroups
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.NormalizerAction

/-!
# Excluding the order-384 S-normalizer in Held's tau case

Let N be the actual ambient normalizer of the displayed elementary subgroup S.
If N has order 384, the pi stabilizer of order 128 makes its orbit have three
points. Explicit conjugators on the sixteen binary words of S force this
orbit to be exactly {pi, mu, pi*mu}.

An order-64 subgroup P of N centralizing tau is a two-group. Sylow conjugacy
inside N moves P into the displayed Sylow subgroup D. The same conjugation
keeps tau in S, and its image has centralizer of order at least 64 in the
concrete local group H. The local centralizer catalogue leaves only
1, pi, mu and pi*mu. The identity is impossible, so tau belongs to the pi
orbit, contradicting the three-point description.

All finite checks use binary coordinates and kernel reduction. The overgroup
hypotheses are explicit; no global fusion hypothesis or additional normalizer
order assertion is assumed.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.6, printed p.228.
The source convention is x^g = g⁻¹*x*g; here conjugation is g*x*g⁻¹.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates LambdaSeparation
namespace TauSylow
private abbrev ConjCode := Fin 2 × Fin 2 × Fin 2
private def conjugator (b : ConjCode) : H := mup ^ b.1.val * taup ^ b.2.1.val * xi ^ b.2.2.val
private def representative : Fin 6 → H := ![1, pi, mu, tau, lam, pi * lam]
private def orbitLabel (a : BaseCode) : Fin 6 :=
  if a.2.2.2 = 1 then (if a.1 = a.2.1 * a.2.2.1 then 4 else 5)
  else if a.2.2.1 = 1 then 3 else if a.2.1 = 1 then 2 else if a.1 = 1 then 1 else 0

private theorem conjugator_mem (b : ConjCode) : conjugator b ∈ modelD := by
  have h (i : Fin 7) : (![pi, mu, mup, tau, taup, lam, xi] : Fin 7 → H) i ∈ modelD :=
    subset_closure ⟨i, rfl⟩
  exact modelD.mul_mem (modelD.mul_mem (modelD.pow_mem (h 2) _)
    (modelD.pow_mem (h 4) _)) (modelD.pow_mem (h 6) _)

private theorem orbitLabel_conjugate : ∀ a : BaseCode, ∃ b : ConjCode,
    conjugator b * representative (orbitLabel a) * (conjugator b)⁻¹ = elementaryWord 1 a := by
  decide +kernel

private def selected (b : Fin 4 → Bool) (a : BaseCode) : Prop :=
  orbitLabel a = 1 ∨ (orbitLabel a = 2 ∧ b 0 = true) ∨
    (orbitLabel a = 3 ∧ b 1 = true) ∨
    (orbitLabel a = 4 ∧ b 2 = true) ∨ (orbitLabel a = 5 ∧ b 3 = true)
private instance (b : Fin 4 → Bool) (a : BaseCode) : Decidable (selected b a) := by
  unfold selected
  infer_instance
private theorem selected_three : ∀ b : Fin 4 → Bool,
    Fintype.card {a : BaseCode // selected b a} = 3 →
    ∀ a, selected b a ↔
      elementaryWord 1 a = pi ∨ elementaryWord 1 a = mu ∨ elementaryWord 1 a = pi * mu := by
  decide +kernel

private theorem code_card_three (p : H → Prop)
    (hconj : ∀ (g : H), g ∈ modelD → ∀ x, p (g * x * g⁻¹) ↔ p x)
    (hone : ¬ p 1) (hpi : p pi)
    (hc : Nat.card {a : BaseCode // p (elementaryWord 1 a)} = 3) (a : BaseCode) :
    p (elementaryWord 1 a) ↔
      elementaryWord 1 a = pi ∨ elementaryWord 1 a = mu ∨ elementaryWord 1 a = pi * mu := by
  classical
  let b : Fin 4 → Bool := ![decide (p mu), decide (p tau), decide (p lam), decide (p (pi * lam))]
  have hp (a : BaseCode) : p (elementaryWord 1 a) ↔ p (representative (orbitLabel a)) := by
    obtain ⟨c, hc⟩ := orbitLabel_conjugate a
    rw [← hc]
    exact hconj _ (conjugator_mem c) _
  have hs (a : BaseCode) : p (elementaryWord 1 a) ↔ selected b a := by
    rw [hp]
    unfold selected
    generalize orbitLabel a = i
    fin_cases i <;> simp [representative, b, hone, hpi]
  have he := Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl BaseCode) hs)
  rw [he, Nat.card_eq_fintype_card] at hc
  exact (hs a).trans (selected_three b hc a)

private theorem low_label : ∀ a : BaseCode,
    orbitLabel a = 0 ∨ orbitLabel a = 1 ∨ orbitLabel a = 2 →
    elementaryWord 1 a = 1 ∨ elementaryWord 1 a = pi ∨
      elementaryWord 1 a = mu ∨ elementaryWord 1 a = pi * mu := by
  decide +kernel

private theorem large_centralizer (y : H) (hy : y ∈ modelS)
    (hc : 64 ≤ Nat.card (centralizer ({y} : Set H))) :
    y = 1 ∨ y = pi ∨ y = mu ∨ y = pi * mu := by
  obtain ⟨a, rfl⟩ := (mem_elementary 1 y).mp hy
  apply low_label a
  obtain ⟨b, hb⟩ := orbitLabel_conjugate a
  let f := MulAut.conj (conjugator b)
  have he : f (representative (orbitLabel a)) = elementaryWord 1 a := hb
  have hh : Nat.card (centralizer ({representative (orbitLabel a)} : Set H)) =
      Nat.card (centralizer ({elementaryWord 1 a} : Set H)) := by
    rw [← he]
    apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
    intro x
    change x ∈ centralizer ({representative (orbitLabel a)} : Set H) ↔
      f x ∈ centralizer ({f (representative (orbitLabel a))} : Set H)
    simp only [mem_centralizer_singleton_iff, ← map_mul, f.injective.eq_iff]
  by_contra hn
  have hi : orbitLabel a = 3 ∨ orbitLabel a = 4 ∨ orbitLabel a = 5 := by omega
  have h32 : Nat.card (centralizer ({representative (orbitLabel a)} : Set H)) = 32 := by
    rcases hi with h | h | h
    · rw [h]; exact involution_centralizer_cards.2.2.1
    · rw [h]; exact involution_centralizer_cards.2.2.2.1
    · rw [h]; exact involution_centralizer_cards.2.2.2.2.1
  omega

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private def inPiOrbit (y : G) : Prop :=
  ∃ n : sNormalizer D e, (n : G) * D.z * (n : G)⁻¹ = y

private theorem inPiOrbit_iff (y : ambientElementary D e 1) :
    inPiOrbit D e (y : G) ↔ y ∈ MulAction.orbit (sNormalizer D e) (piPoint D e) := by
  constructor
  · rintro ⟨n, hn⟩
    exact MulAction.mem_orbit_iff.mpr ⟨n, Subtype.ext hn⟩
  · intro hy
    obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.mp hy
    exact ⟨n, congrArg Subtype.val hn⟩

omit [Finite G] in
private theorem inPiOrbit_conj (g : sNormalizer D e) (y : G) :
    inPiOrbit D e ((g : G) * y * (g : G)⁻¹) ↔ inPiOrbit D e y := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨g⁻¹ * n, ?_⟩
    change ((g : G)⁻¹ * (n : G)) * D.z * ((g : G)⁻¹ * (n : G))⁻¹ = y
    calc
      _ = (g : G)⁻¹ * ((n : G) * D.z * (n : G)⁻¹) * (g : G) := by group
      _ = y := by rw [hn]; group
  · rintro ⟨n, hn⟩
    refine ⟨g * n, ?_⟩
    change ((g : G) * (n : G)) * D.z * ((g : G) * (n : G))⁻¹ = _
    calc
      _ = (g : G) * ((n : G) * D.z * (n : G)⁻¹) * (g : G)⁻¹ := by group
      _ = _ := by rw [hn]

private noncomputable def sWord (a : BaseCode) : ambientElementary D e 1 :=
  ⟨D.a10ModelEmbedding e (elementaryWord 1 a), mem_map_of_mem _ ((mem_elementary _ _).mpr ⟨a, rfl⟩)⟩

omit [Finite G] in
private theorem sWord_bijective : Function.Bijective (sWord D e) := by
  constructor
  · intro a b hab
    have h : elementaryWord 1 a = elementaryWord 1 b :=
      D.a10ModelEmbedding_injective e (congrArg (fun y : ambientElementary D e 1 => (y : G)) hab)
    rw [elementaryWord_eq_word, elementaryWord_eq_word] at h
    have he := word_injective h
    simpa [elementaryCode, Prod.ext_iff, and_assoc] using he
  · rintro ⟨y, t, ht, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_elementary 1 t).mp ht
    exact ⟨a, rfl⟩

private theorem inPiOrbit_of_card (hN : Nat.card (sNormalizer D e) = 384)
    (y : H) (hy : y ∈ modelS) :
    inPiOrbit D e (D.a10ModelEmbedding e y) ↔ y = pi ∨ y = mu ∨ y = pi * mu := by
  let p (y : H) : Prop := inPiOrbit D e (D.a10ModelEmbedding e y)
  have hconj (g : H) (hg : g ∈ modelD) (y : H) : p (g * y * g⁻¹) ↔ p y := by
    let n : sNormalizer D e := ⟨D.a10ModelEmbedding e g,
      ambientSylow_le_normalizer_S D e (mem_map_of_mem _ hg)⟩
    simpa only [p, map_mul, map_inv] using inPiOrbit_conj D e n (D.a10ModelEmbedding e y)
  have h1 : ¬ p 1 := by
    rintro ⟨n, hn⟩
    rw [map_one, mul_inv_eq_one] at hn
    have hz : D.z = 1 := by
      apply mul_left_cancel (a := (n : G))
      simpa using hn
    exact D.z_ne_one hz
  have hp : p pi := by
    refine ⟨1, ?_⟩
    simpa using (D.a10ModelEmbedding_central e).symm
  have he := Equiv.subtypeEquiv (Equiv.ofBijective (sWord D e) (sWord_bijective D e))
    (fun a => inPiOrbit_iff D e (sWord D e a))
  have hh : Nat.card {a : BaseCode // p (elementaryWord 1 a)} =
      (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard :=
    (Nat.card_congr he).trans (Nat.card_coe_set_eq _)
  have hc : Nat.card {a : BaseCode // p (elementaryWord 1 a)} = 3 := by
    have h := normalizer_card D e
    rw [hN] at h
    omega
  obtain ⟨a, rfl⟩ := (mem_elementary 1 y).mp hy
  exact code_card_three p hconj h1 hp hc a

private theorem exists_conjugate_le (P : Subgroup G) (hc : Nat.card P = 64)
    (hPN : P ≤ sNormalizer D e) :
    ∃ n : sNormalizer D e,
      P.map (MulAut.conj (n : G)).toMonoidHom ≤ ambientD D e := by
  let N := sNormalizer D e
  have htwo : IsPGroup 2 (P.subgroupOf N) := IsPGroup.of_card (n := 6) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv, hc]
    norm_num)
  obtain ⟨X, hPX⟩ := htwo.exists_le_sylow
  let T : Sylow 2 N := (ambientSylow D e).subtype (ambientSylow_le_normalizer_S D e)
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N X T
  refine ⟨n, ?_⟩
  rintro x ⟨a, ha, rfl⟩
  let aN : N := ⟨a, hPN ha⟩
  have hx := Subgroup.smul_mem_pointwise_smul aN (MulAut.conj n) (X : Subgroup N) (hPX ha)
  change MulAut.conj n aN ∈ (n • X : Sylow 2 N) at hx
  rw [hn] at hx
  exact hx

end TauSylow

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

open TauSylow in
/-- The tau overgroup inside N_G(S) excludes normalizer order 384. -/
public theorem tau_overgroup_normalizer_card_ne_384
    (P : Subgroup G) (hc : Nat.card P = 64)
    (_hQP : ambientSCaseCentralizer D e 0 ≤ P)
    (hPC : P ≤ centralizer ({D.a10ModelEmbedding e tau} : Set G))
    (hPN : P ≤ normalizer (ambientElementary D e 1 : Set G)) :
    Nat.card (normalizer (ambientElementary D e 1 : Set G)) ≠ 384 := by
  intro hN
  let f := D.a10ModelEmbedding e
  obtain ⟨n, hRD⟩ := exists_conjugate_le D e P hc hPN
  let c := MulAut.conj (n : G)
  have htS : f tau ∈ ambientElementary D e 1 :=
    mem_map_of_mem f (elementaryGenerators_mem 1 2)
  have hyS : c (f tau) ∈ ambientElementary D e 1 :=
    (n • (⟨f tau, htS⟩ : ambientElementary D e 1)).property
  obtain ⟨y, hy, he⟩ := hyS
  have ht : f tau ≠ 1 := by
    intro h
    have hn : tau ≠ 1 := by decide +kernel
    exact hn ((D.a10ModelEmbedding_injective e) (h.trans (map_one f).symm))
  have hy1 : y ≠ 1 := by
    intro h
    apply ht
    apply c.injective
    rw [← he, h, map_one, map_one]
  have hRC : P.map c.toMonoidHom ≤ (centralizer ({y} : Set H)).map f := by
    rintro x ⟨a, ha, rfl⟩
    have hax : c a ∈ f.range := (map_le_range f modelD) (hRD ⟨a, ha, rfl⟩)
    obtain ⟨b, hb⟩ := hax
    refine ⟨b, mem_centralizer_singleton_iff.mpr ?_, hb⟩
    apply D.a10ModelEmbedding_injective e
    change f (b * y) = f (y * b)
    simp only [map_mul]
    rw [hb, he, ← map_mul, ← map_mul]
    exact congrArg c (mem_centralizer_singleton_iff.mp (hPC ha))
  have hbound := card_le_of_le hRC
  rw [card_map_of_injective c.injective, hc,
    card_map_of_injective (D.a10ModelEmbedding_injective e)] at hbound
  have horb := (inPiOrbit_of_card D e hN y hy).mpr
    ((large_centralizer y hy hbound).resolve_left hy1)
  have htOrb : inPiOrbit D e (f tau) := by
    apply (inPiOrbit_conj D e n (f tau)).mp
    change inPiOrbit D e (c (f tau))
    rw [← he]
    exact horb
  have hbad := (inPiOrbit_of_card D e hN tau (elementaryGenerators_mem 1 2)).mp htOrb
  have hn : ¬ (tau = Coordinates.pi ∨ tau = mu ∨ tau = Coordinates.pi * mu) := by decide +kernel
  exact hn hbad

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion

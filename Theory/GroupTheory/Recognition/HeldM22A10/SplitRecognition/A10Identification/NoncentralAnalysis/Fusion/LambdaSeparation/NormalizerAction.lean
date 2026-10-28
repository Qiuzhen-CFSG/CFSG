module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry

/-!
# The order-72 reduction in Held's lambda separation argument

Let S be the displayed elementary subgroup of order sixteen. Its actual
normalizer has pi stabilizer equal to the displayed Sylow subgroup of order
128. Self-centralization identifies N_G(S)/S with its conjugation image in
Aut(S).

If an element of order three in N_G(S) centralizes pi*mu, then pi*mu cannot
belong to the pi orbit: its stabilizer would contain that element, whereas
the pi stabilizer is a two-group. The local tau' conjugation also excludes mu.
The concrete Sylow action partitions S into blocks represented by
1, pi, mu, tau, lambda and pi*lambda, of sizes 1, 1, 2, 4, 4 and 4.
Consequently the pi orbit has size congruent to one modulo four. Its size is
at most fifteen and is divisible by three, so it is nine. Orbit-stabilizer
then gives |N_G(S)/S| = 72.

Finite checks use only sixteen binary words and eight conjugators, with kernel
reduction. The order-three witness remains an explicit hypothesis: this module
does not construct it from the two proposed fusions or exclude the order-72
case, and therefore does not yet prove Lemma 2.4.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.4, pp.226--227. The orbit congruence
replaces the printed separate exclusion of quotient order 24. Source
conjugation is x^g = g⁻¹*x*g; conjugators here use Lean's opposite convention.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
open Coordinates
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

private def selected (b : Fin 3 → Bool) (a : BaseCode) : Prop :=
  orbitLabel a = 1 ∨ (orbitLabel a = 3 ∧ b 0 = true) ∨
    (orbitLabel a = 4 ∧ b 1 = true) ∨ (orbitLabel a = 5 ∧ b 2 = true)

private instance (b : Fin 3 → Bool) (a : BaseCode) : Decidable (selected b a) := by
  unfold selected
  infer_instance

private theorem selected_card : ∀ b : Fin 3 → Bool,
    Fintype.card {a : BaseCode // selected b a} % 4 = 1 := by decide +kernel

private theorem code_card_mod_four (p : H → Prop)
    (hconj : ∀ (g : H), g ∈ modelD → ∀ x, p (g * x * g⁻¹) ↔ p x)
    (hone : ¬ p 1) (hpi : p pi) (hmu : ¬ p mu) :
    Nat.card {a : BaseCode // p (elementaryWord 1 a)} % 4 = 1 := by
  classical
  let b : Fin 3 → Bool := ![decide (p tau), decide (p lam), decide (p (pi * lam))]
  have hp (a : BaseCode) : p (elementaryWord 1 a) ↔ p (representative (orbitLabel a)) := by
    obtain ⟨c, hc⟩ := orbitLabel_conjugate a
    rw [← hc]
    exact hconj _ (conjugator_mem c) _
  have hs (a : BaseCode) : p (elementaryWord 1 a) ↔ selected b a := by
    rw [hp]
    unfold selected
    generalize orbitLabel a = i
    fin_cases i <;> simp [representative, b, hone, hpi, hmu]
  have hc := Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl BaseCode) hs)
  rw [hc, Nat.card_eq_fintype_card]
  exact selected_card b

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The actual ambient normalizer of the displayed elementary subgroup S. -/
public abbrev sNormalizer := normalizer (ambientElementary D e 1 : Set G)
/-- The quotient by S inside its own normalizer; normality is relative to this overgroup. -/
public abbrev sNormalizerQuotient := sNormalizer D e ⧸ (ambientElementary D e 1).subgroupOf (sNormalizer D e)

/-- Self-centralization identifies the quotient with its actual conjugation image in Aut(S). -/
public noncomputable def quotientEquivAction : sNormalizerQuotient D e ≃*
    (ambientElementary D e 1).normalizerMonoidHom.range :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [normalizerMonoidHom_ker, ambientElementary_selfCentralizing D e 1])).symm.trans
      (QuotientGroup.quotientKerEquivRange _)

/-- The distinguished ambient involution as a point of S. -/
@[expose] public def piPoint : ambientElementary D e 1 := ⟨D.z, z_mem_ambientElementary D e 1⟩

/-- The stabilizer of pi is exactly the displayed Sylow subgroup, restricted to N_G(S). -/
public theorem piPoint_stabilizer :
    MulAction.stabilizer (sNormalizer D e) (piPoint D e) =
      (ambientD D e).subgroupOf (sNormalizer D e) := by
  have h := normalizer_S_inf_centralizer D e
  ext g
  rw [MulAction.mem_stabilizer_iff]
  change (⟨(g : G) * D.z * (g : G)⁻¹, _⟩ : ambientElementary D e 1) = piPoint D e ↔
    (g : G) ∈ ambientD D e
  rw [Subtype.ext_iff, ← h]
  change (g : G) * D.z * (g : G)⁻¹ = D.z ↔ _
  rw [mem_inf, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  simp only [g.property, true_and]

/-- The pi stabilizer in the normalizer has order 128. -/
public theorem piPoint_stabilizer_card :
    Nat.card (MulAction.stabilizer (sNormalizer D e) (piPoint D e)) = 128 := by
  have h : ambientD D e ≤ sNormalizer D e := ambientSylow_le_normalizer_S D e
  rw [piPoint_stabilizer, Nat.card_congr (subgroupOfEquivOfLe h).toEquiv, ambientD_card]

/-- Orbit-stabilizer for the normalizer acting on S. -/
public theorem normalizer_card : Nat.card (sNormalizer D e) =
    128 * (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard := by
  have h := (MulAction.stabilizer (sNormalizer D e) (piPoint D e)).card_mul_index
  rw [piPoint_stabilizer_card, MulAction.index_stabilizer] at h
  exact h.symm

/-- The quotient order is eight times the pi orbit size. -/
public theorem quotient_card : Nat.card (sNormalizerQuotient D e) =
    8 * (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard := by
  have h := card_eq_card_quotient_mul_card_subgroup
    ((ambientElementary D e 1).subgroupOf (sNormalizer D e))
  rw [Nat.card_congr (subgroupOfEquivOfLe (ambientElementary D e 1).le_normalizer).toEquiv,
    ambientElementary_card, normalizer_card] at h
  change _ = Nat.card (sNormalizerQuotient D e) * 16 at h
  omega

/-- The pi orbit contains only nonidentity elements of S. -/
public theorem piPoint_orbit_card_le :
    (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard ≤ 15 := by
  have hs : MulAction.orbit (sNormalizer D e) (piPoint D e) ⊆ {1}ᶜ := by
    intro x hx hx1
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
    have h1 : piPoint D e = 1 := (MulAction.injective g) (by simpa using hx1)
    exact D.z_ne_one (congrArg Subtype.val h1)
  have h := Set.ncard_le_ncard hs
  rw [Set.ncard_compl, Set.ncard_singleton, ambientElementary_card] at h
  exact h

/-- No element of order three in this normalizer centralizes pi. -/
public theorem normalizer_three_not_centralize_pi (x : sNormalizer D e) (hx : orderOf x = 3) :
    (x : G) * D.z ≠ D.z * (x : G) := by
  intro hc
  have hs : x ∈ MulAction.stabilizer (sNormalizer D e) (piPoint D e) := by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change (x : G) * D.z * (x : G)⁻¹ = D.z
    rwa [mul_inv_eq_iff_eq_mul]
  have hd := (MulAction.stabilizer (sNormalizer D e) (piPoint D e)).orderOf_dvd_natCard hs
  rw [hx, piPoint_stabilizer_card] at hd
  norm_num at hd

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

private theorem not_inPiOrbit_of_three (x : sNormalizer D e) (hx : orderOf x = 3)
    (y : G) (hxy : (x : G) * y = y * (x : G)) : ¬ inPiOrbit D e y := by
  rintro ⟨n, hn⟩
  let t := MulAut.conj n⁻¹ x
  have ht : orderOf t = 3 := ((MulAut.conj n⁻¹).orderOf_eq x).trans hx
  apply normalizer_three_not_centralize_pi D e t ht
  apply (mul_inv_eq_iff_eq_mul).mp
  simp only [t, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  calc
    _ = (n : G)⁻¹ * ((x : G) * ((n : G) * D.z * (n : G)⁻¹) * (x : G)⁻¹) * (n : G) := by group
    _ = (n : G)⁻¹ * y * (n : G) := by rw [hn, hxy]; group
    _ = D.z := by rw [← hn]; group

/-- An order-three element centralizing pi*mu excludes fusion of pi with pi*mu in N_G(S). -/
public theorem pi_mul_mu_not_normalizer_conjugate (x : sNormalizer D e) (hx : orderOf x = 3)
    (hc : Commute (x : G) (D.a10ModelEmbedding e (pi * mu)))
    (n : sNormalizer D e) :
    (n : G) * D.z * (n : G)⁻¹ ≠ D.a10ModelEmbedding e (pi * mu) := by
  intro hn
  exact not_inPiOrbit_of_three D e x hx _ hc.eq ⟨n, hn⟩

private theorem mu_not_inPiOrbit_of_three (x : sNormalizer D e) (hx : orderOf x = 3)
    (hc : Commute (x : G) (D.a10ModelEmbedding e (pi * mu))) :
    ¬ inPiOrbit D e (D.a10ModelEmbedding e mu) := by
  have ht : taup ∈ modelD := subset_closure ⟨(4 : Fin 7), rfl⟩
  let t : sNormalizer D e := ⟨D.a10ModelEmbedding e taup,
    ambientSylow_le_normalizer_S D e (mem_map_of_mem _ ht)⟩
  have he : taup * mu * taup⁻¹ = pi * mu := by decide +kernel
  intro h
  have h' := (inPiOrbit_conj D e t (D.a10ModelEmbedding e mu)).mpr h
  change inPiOrbit D e (D.a10ModelEmbedding e taup * D.a10ModelEmbedding e mu *
    (D.a10ModelEmbedding e taup)⁻¹) at h'
  rw [← map_inv, ← map_mul, ← map_mul, he] at h'
  exact not_inPiOrbit_of_three D e x hx _ hc.eq h'

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

private theorem piPoint_orbit_card_mod_four (x : sNormalizer D e) (hx : orderOf x = 3)
    (hc : Commute (x : G) (D.a10ModelEmbedding e (pi * mu))) :
    (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard % 4 = 1 := by
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
  have hm : ¬ p mu := mu_not_inPiOrbit_of_three D e x hx hc
  have h := code_card_mod_four p hconj h1 hp hm
  have he := Equiv.subtypeEquiv (Equiv.ofBijective (sWord D e) (sWord_bijective D e))
    (fun a => inPiOrbit_iff D e (sWord D e a))
  have hh : Nat.card {a : BaseCode // p (elementaryWord 1 a)} =
      (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard := by
    exact (Nat.card_congr he).trans (Nat.card_coe_set_eq _)
  rwa [hh] at h

/-- The source order-three witness forces the quotient to have order 72. -/
public theorem quotient_card_of_three_centralizer (x : sNormalizer D e) (hx : orderOf x = 3)
    (hc : Commute (x : G) (D.a10ModelEmbedding e (pi * mu))) :
    Nat.card (sNormalizerQuotient D e) = 72 := by
  have hd := orderOf_dvd_natCard x
  rw [hx, normalizer_card] at hd
  have hb := piPoint_orbit_card_le D e
  have hm := piPoint_orbit_card_mod_four D e x hx hc
  have hn : (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard = 9 := by
    generalize (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard = n at *
    interval_cases n <;> norm_num at *
  rw [quotient_card, hn]

/-- The same witness gives the full ambient normalizer order 1152. -/
public theorem normalizer_card_of_three_centralizer (x : sNormalizer D e) (hx : orderOf x = 3)
    (hc : Commute (x : G) (D.a10ModelEmbedding e (pi * mu))) :
    Nat.card (sNormalizer D e) = 1152 := by
  have h := quotient_card_of_three_centralizer D e x hx hc
  rw [quotient_card] at h
  rw [normalizer_card]
  omega

/-- The pi orbit has nine elements once the source order-three witness exists. -/
public theorem piPoint_orbit_card_of_three_centralizer (x : sNormalizer D e) (hx : orderOf x = 3)
    (hc : Commute (x : G) (D.a10ModelEmbedding e (pi * mu))) :
    (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard = 9 := by
  have h := quotient_card_of_three_centralizer D e x hx hc
  rw [quotient_card] at h
  omega

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation

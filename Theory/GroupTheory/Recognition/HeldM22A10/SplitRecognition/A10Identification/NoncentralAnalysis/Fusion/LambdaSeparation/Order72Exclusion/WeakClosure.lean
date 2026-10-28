module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.NormalizerAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.Tables

/-!
# Weak closure of S when its normalizer quotient has order 72

The normalizer of S then has order 1152. If S were conjugate to either L₁
or L₂, the pi stabilizer of order 64 would give an orbit of size eighteen
in an elementary group of order sixteen. If S were conjugate to M, its pi
orbit would have size three; the local H-classes in M have sizes 1, 6, 4, 4,
which excludes this. The four-subgroup catalogue therefore makes S weakly
closed in the displayed Sylow subgroup.

Sylow conjugacy in the centralizer of the target element then corrects any
ambient fusion between elements of the abelian S to fusion in N_G(S).
This argument is an alternative to the structural order-72 case split in
Held's Lemma 2.4; it does not assume either quotient isomorphism type or use
ambient pi--mu nonfusion. The Sylow adjustment follows the proof pattern of
`Theory/GroupTheory/WeakClosureFusion.lean`, using only that both fused
points belong to the abelian subgroup, rather than centrality in the Sylow.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.4, p.227 and Section 1, p.225.
-/

open Subgroup Equiv
open scoped IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation
open Coordinates

private theorem modelM_count_ne_three (p : H → Prop)
    (hc : ∀ a b, IsConj a b → (p a ↔ p b)) (h1 : ¬ p 1) (hp : p pi) :
    Nat.card {a : BaseCode // p (elementaryWord 0 a)} ≠ 3 := by
  classical
  let b : Fin 9 → Bool := fun i => decide (p (localRepresentative i))
  have he (a : BaseCode) : p (elementaryWord 0 a) ↔ b (elementaryClass 0 a) = true := by
    simpa only [b, decide_eq_true_eq] using (hc _ _ (elementaryWord_isConj 0 a)).symm
  have h0 : b 0 = false := by simp [b, localRepresentative, h1]
  have hpi : b 1 = true := by simp [b, localRepresentative, hp]
  have ht : ∀ b : Fin 9 → Bool, b 0 = false → b 1 = true →
      Fintype.card {a : BaseCode // b (elementaryClass 0 a) = true} ≠ 3 := by
    decide +kernel
  rw [Nat.card_congr (Equiv.subtypeEquiv (p := fun a => p (elementaryWord 0 a))
    (q := fun a => b (elementaryClass 0 a) = true) (Equiv.refl BaseCode) he), Nat.card_eq_fintype_card]
  exact ht b h0 hpi

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private def elementaryPiPoint (k : Fin 4) : ambientElementary D e k :=
  ⟨D.z, z_mem_ambientElementary D e k⟩

private theorem elementaryPiPoint_stabilizer_card (k : Fin 4) :
    Nat.card (MulAction.stabilizer (normalizer (ambientElementary D e k : Set G))
      (elementaryPiPoint D e k)) = (![384,128,64,64] : Fin 4 → ℕ) k := by
  let N := normalizer (ambientElementary D e k : Set G)
  have he : MulAction.stabilizer N (elementaryPiPoint D e k) =
      (N ⊓ D.centralizer).subgroupOf N := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    change (⟨(g : G) * D.z * (g : G)⁻¹, _⟩ : ambientElementary D e k) =
      elementaryPiPoint D e k ↔ (g : G) ∈ N ⊓ D.centralizer
    rw [Subtype.ext_iff]
    change (g : G) * D.z * (g : G)⁻¹ = D.z ↔ _
    rw [mem_inf, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    simp only [g.property, true_and]
  rw [he, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]
  exact ambient_normalizer_intersection_card D e k

private theorem elementary_normalizer_card (k : Fin 4) :
    Nat.card (normalizer (ambientElementary D e k : Set G)) =
      (![384,128,64,64] : Fin 4 → ℕ) k *
      (MulAction.orbit (normalizer (ambientElementary D e k : Set G))
        (elementaryPiPoint D e k)).ncard := by
  have h := (MulAction.stabilizer (normalizer (ambientElementary D e k : Set G))
      (elementaryPiPoint D e k)).card_mul_index
  rw [elementaryPiPoint_stabilizer_card, MulAction.index_stabilizer] at h
  exact h.symm

private theorem elementary_orbit_le (k : Fin 4) :
    (MulAction.orbit (normalizer (ambientElementary D e k : Set G))
        (elementaryPiPoint D e k)).ncard ≤ 16 := by
  have h := Set.ncard_le_card (MulAction.orbit (normalizer (ambientElementary D e k : Set G))
        (elementaryPiPoint D e k))
  rwa [ambientElementary_card] at h

private def elementaryOrbit (k : Fin 4) (y : G) : Prop :=
  ∃ n : normalizer (ambientElementary D e k : Set G), (n : G) * D.z * (n : G)⁻¹ = y

private theorem elementaryOrbit_iff (k : Fin 4) (y : ambientElementary D e k) :
    elementaryOrbit D e k (y : G) ↔
      y ∈ MulAction.orbit (normalizer (ambientElementary D e k : Set G))
        (elementaryPiPoint D e k) := by
  constructor
  · rintro ⟨n,hn⟩
    exact MulAction.mem_orbit_iff.mpr ⟨n, Subtype.ext hn⟩
  · intro hy
    obtain ⟨n,hn⟩ := MulAction.mem_orbit_iff.mp hy
    exact ⟨n, congrArg Subtype.val hn⟩

omit [Finite G] in
private theorem elementaryOrbit_conj (k : Fin 4)
    (g : normalizer (ambientElementary D e k : Set G)) (y : G) :
    elementaryOrbit D e k ((g : G) * y * (g : G)⁻¹) ↔ elementaryOrbit D e k y := by
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨g⁻¹ * n, ?_⟩
    change ((g : G)⁻¹ * (n : G)) * D.z * ((g : G)⁻¹ * (n : G))⁻¹ = y
    calc
      _ = (g : G)⁻¹ * ((n : G) * D.z * (n : G)⁻¹) * (g : G) := by group
      _ = y := by rw [hn]; group
  · rintro ⟨n,hn⟩
    refine ⟨g * n, ?_⟩
    change ((g : G) * (n : G)) * D.z * ((g : G) * (n : G))⁻¹ = _
    calc
      _ = (g : G) * ((n : G) * D.z * (n : G)⁻¹) * (g : G)⁻¹ := by group
      _ = _ := by rw [hn]

private noncomputable def elementaryWordEquiv (k : Fin 4) :
    BaseCode ≃ ambientElementary D e k :=
  (Equiv.ofBijective _ (elementaryWord_bijective k)).trans
    ((elementary k).equivMapOfInjective (D.a10ModelEmbedding e)
      (D.a10ModelEmbedding_injective e)).toEquiv

private theorem m_orbit_ne_three :
    (MulAction.orbit (normalizer (ambientElementary D e 0 : Set G))
      (elementaryPiPoint D e 0)).ncard ≠ 3 := by
  let p (y : H) := elementaryOrbit D e 0 (D.a10ModelEmbedding e y)
  have hc (a b : H) (hab : IsConj a b) : p a ↔ p b := by
    obtain ⟨g,rfl⟩ := isConj_iff.mp hab
    let n : normalizer (ambientElementary D e 0 : Set G) :=
      ⟨D.a10ModelEmbedding e g, centralizer_le_normalizer_M D e
        (by rw [← D.a10ModelEmbedding_range e]; exact ⟨g,rfl⟩)⟩
    simpa only [p, map_mul, map_inv] using
      (elementaryOrbit_conj D e 0 n (D.a10ModelEmbedding e a)).symm
  have h1 : ¬ p 1 := by
    rintro ⟨n,hn⟩
    rw [map_one, mul_inv_eq_one] at hn
    exact D.z_ne_one (by
      apply mul_left_cancel (a := (n : G))
      simpa using hn)
  have hp : p pi := by
    refine ⟨1, ?_⟩
    simpa using (D.a10ModelEmbedding_central e).symm
  have he := Equiv.subtypeEquiv (elementaryWordEquiv D e 0)
    (fun a => elementaryOrbit_iff D e 0 (elementaryWordEquiv D e 0 a))
  have hcard : Nat.card {a : BaseCode // p (elementaryWord 0 a)} =
      (MulAction.orbit (normalizer (ambientElementary D e 0 : Set G))
        (elementaryPiPoint D e 0)).ncard :=
    (Nat.card_congr he).trans (Nat.card_coe_set_eq _)
  rw [← hcard]
  exact modelM_count_ne_three p hc h1 hp

/-- Normalizer orders separate S from all three other elementary-sixteen catalogue entries. -/
public theorem s_not_conjugate_other_of_order72
    (h72 : Nat.card (sNormalizerQuotient D e) = 72)
    (k : Fin 4) (hk : k ≠ 1) (g : G) :
    (ambientElementary D e 1).map (MulAut.conj g).toMonoidHom ≠
      ambientElementary D e k := by
  intro he
  have hq := quotient_card D e
  have hn := normalizer_card D e
  rw [h72] at hq
  have hs : Nat.card (sNormalizer D e) = 1152 := by omega
  have hn' : Nat.card (normalizer (ambientElementary D e k : Set G)) = 1152 := by
    rw [← he, ← map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,
      card_map_of_injective (MulAut.conj g).injective]
    exact hs
  rw [elementary_normalizer_card] at hn'
  have hb := elementary_orbit_le D e k
  fin_cases k
  · have hh := m_orbit_ne_three D e
    change 384 * (MulAction.orbit (normalizer (ambientElementary D e 0 : Set G))
      (elementaryPiPoint D e 0)).ncard = 1152 at hn'
    exact hh (by omega)
  · exact hk rfl
  · norm_num at hn'
    omega
  · norm_num at hn'
    omega

/-- Every conjugate of S contained in the displayed Sylow subgroup equals S. -/
public theorem s_weakly_closed_of_order72
    (h72 : Nat.card (sNormalizerQuotient D e) = 72) (g : G)
    (hg : (ambientElementary D e 1).map (MulAut.conj g).toMonoidHom ≤ ambientSylow D e) :
    (ambientElementary D e 1).map (MulAut.conj g).toMonoidHom = ambientElementary D e 1 := by
  have hA : IsElementaryAbelian 2 ((ambientElementary D e 1).map (MulAut.conj g).toMonoidHom) := by
    let := ambientElementary_isElementaryAbelian D e 1
    exact IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hcard : Nat.card ((ambientElementary D e 1).map (MulAut.conj g).toMonoidHom) = 16 := by
    rw [card_map_of_injective (MulAut.conj g).injective, ambientElementary_card]
  obtain ⟨k,hk⟩ := ambient_elementary_sixteen D e _ hg hA hcard
  by_cases he : k = 1
  · simpa [he] using hk
  · exact (s_not_conjugate_other_of_order72 D e h72 k he g hk).elim

private theorem exists_conj_map_le (P : Sylow 2 G) {K : Subgroup G}
    (hK : IsPGroup 2 K) : ∃ g : G, K.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hK.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  rw [← hg]
  exact map_mono hQ

/-- Every ambient fusion between points of S has a conjugator in its actual normalizer. -/
public theorem s_controls_fusion_of_order72
    (h72 : Nat.card (sNormalizerQuotient D e) = 72)
    {a b : G} (ha : a ∈ ambientElementary D e 1) (hb : b ∈ ambientElementary D e 1)
    (hab : IsConj a b) : ∃ n : sNormalizer D e, (n : G) * a * (n : G)⁻¹ = b := by
  let W := ambientElementary D e 1
  let P := ambientSylow D e
  let := ambientElementary_isElementaryAbelian D e 1
  have hweak (g : G) (hg : W.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G)) :
      g ∈ normalizer (W : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (s_weakly_closed_of_order72 D e h72 g hg)
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  let C := centralizer ({b} : Set G)
  let f := MulAut.conj g
  let V := W.map f.toMonoidHom
  have hW : IsPGroup 2 W := P.isPGroup'.to_le (ambientElementary_le_ambientSylow D e 1)
  have hWC : W ≤ C := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr ((W.le_centralizer hb) w hw)
  have hVC : V ≤ C := by
    rintro _ ⟨w, hw, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg f ((W.le_centralizer ha) w hw)
    have hfa : f a = b := hg
    change f w * b = b * f w
    simpa only [map_mul, hfa] using he
  obtain ⟨Q, hQ⟩ := (hW.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨c, hc⟩ := exists_conj_map_le Q ((hW.map f.toMonoidHom).comap_subtype (K := C))
  obtain ⟨k, hk⟩ := exists_conj_map_le P (Q.isPGroup'.map C.subtype)
  have hkW : k ∈ normalizer (W : Set G) := by
    apply hweak
    rintro _ ⟨w, hw, rfl⟩
    apply hk
    exact mem_map_of_mem _ ⟨⟨w, hWC hw⟩, hQ hw, rfl⟩
  have hkcgW : k * (c : G) * g ∈ normalizer (W : Set G) := by
    apply hweak
    rintro _ ⟨w, hw, rfl⟩
    have hwV : f w ∈ V := mem_map_of_mem _ hw
    have hcQ := hc (mem_map_of_mem (MulAut.conj c).toMonoidHom
      (show (⟨f w, hVC hwV⟩ : C) ∈ V.subgroupOf C from hwV))
    have hkP := hk (mem_map_of_mem (MulAut.conj k).toMonoidHom
      (mem_map_of_mem C.subtype hcQ))
    change k * (↑c * (g * w * g⁻¹) * (↑c)⁻¹) * k⁻¹ ∈ (P : Subgroup G) at hkP
    change (k * ↑c * g) * w * (k * ↑c * g)⁻¹ ∈ (P : Subgroup G)
    simpa only [mul_inv_rev, mul_assoc] using hkP
  have hcgW : (c : G) * g ∈ normalizer (W : Set G) := by
    have := (normalizer (W : Set G)).mul_mem
      ((normalizer (W : Set G)).inv_mem hkW) hkcgW
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using this
  refine ⟨⟨(c : G) * g, hcgW⟩, ?_⟩
  change (↑c * g) * a * (↑c * g)⁻¹ = b
  calc
    _ = ↑c * (g * a * g⁻¹) * (↑c)⁻¹ := by group
    _ = ↑c * b * (↑c)⁻¹ := by rw [hg]
    _ = b := mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property)

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation

module

public import Theory.GroupTheory.NormalComplementFusion

/-!
# Fusion controlled by normalizers of weakly closed central subgroups

Let W lie in a Sylow p-subgroup P of a finite group, centralize P, and be
weakly closed in P. Then N_G(W) controls element fusion in P. If C_G(W)
has a normal p-complement, N_G(P) also controls element fusion in P.

For the first assertion, if g sends x to y in P, both W and gWg⁻¹ lie
in C_G(y). Choose a Sylow subgroup Q of that centralizer containing W,
conjugate gWg⁻¹ into Q within the centralizer, and conjugate Q into P.
Weak closure applied to both images makes the corrected conjugator
normalize W while it still sends x to y.

For the second assertion, Sylow conjugacy inside C_G(W) adjusts that
conjugator to normalize P. Normal-complement fusion inside C_G(W) then
corrects its action on x by an element of P.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Lemma 2.1(ii–iii), pp. 78–79, saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

open Subgroup

namespace Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem exists_conj_map_le (P : Sylow p G) {H : Subgroup G}
    (hH : IsPGroup p H) : ∃ g : G, H.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  rw [← hg]
  exact map_mono hQ

/-- The normalizer of a weakly closed subgroup central in P controls element
fusion in P (Glauberman Lemma 2.1(ii)). -/
public theorem weakly_closed_normalizer_controls_fusion
    (P : Sylow p G) (W : Subgroup G)
    (hWP : W ≤ (P : Subgroup G))
    (hPC : (P : Subgroup G) ≤ centralizer (W : Set G))
    (hweak : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      g ∈ normalizer (W : Set G))
    {x y : G} (hx : x ∈ (P : Subgroup G)) (hy : y ∈ (P : Subgroup G))
    (hxy : IsConj x y) :
    ∃ n ∈ normalizer (W : Set G), n * x * n⁻¹ = y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  let C := centralizer ({y} : Set G)
  let f := MulAut.conj g
  let V := W.map f.toMonoidHom
  have hW : IsPGroup p W := P.isPGroup'.to_le hWP
  have hWC : W ≤ C := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr ((hPC hy) w hw)
  have hVC : V ≤ C := by
    rintro _ ⟨w, hw, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg f ((hPC hx) w hw)
    have hfx : f x = y := hg
    change f w * y = y * f w
    simpa only [map_mul, hfx] using he
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
  refine ⟨(c : G) * g, hcgW, ?_⟩
  calc
    (↑c * g) * x * (↑c * g)⁻¹ = ↑c * (g * x * g⁻¹) * (↑c)⁻¹ := by group
    _ = ↑c * y * (↑c)⁻¹ := by rw [hg]
    _ = y := mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property)

/-- If the centralizer of a weakly closed subgroup central in P has a normal
p-complement, the normalizer of P controls element fusion in P
(Glauberman Lemma 2.1(iii)). -/
public theorem normalizer_controls_fusion_of_weakly_closed
    (P : Sylow p G) (W : Subgroup G)
    (hWP : W ≤ (P : Subgroup G))
    (hPC : (P : Subgroup G) ≤ centralizer (W : Set G))
    (hweak : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      g ∈ normalizer (W : Set G))
    (K : Subgroup (centralizer (W : Set G))) [K.Normal]
    (hcop : Nat.Coprime p (Nat.card K))
    (hquot : IsPGroup p ((centralizer (W : Set G)) ⧸ K))
    (x : G) (hx : x ∈ (P : Subgroup G)) (y : G) (hy : y ∈ (P : Subgroup G))
    (hxy : IsConj x y) :
    ∃ n ∈ normalizer (P : Set G), n * x * n⁻¹ = y := by
  obtain ⟨t, ht, htx⟩ := P.weakly_closed_normalizer_controls_fusion W hWP hPC hweak hx hy hxy
  let C := centralizer (W : Set G)
  have hNC : normalizer (W : Set G) ≤ normalizer (C : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (W : Set G))).mp
      inferInstance
  have htPC : ((t • P : Sylow p G) : Subgroup G) ≤ C := by
    rintro _ ⟨u, hu, rfl⟩
    exact (mem_normalizer_iff.mp (hNC ht) u).mp (hPC hu)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C ((t • P).subtype htPC) (P.subtype hPC)
  simp_rw [smul_subtype, Subgroup.smul_def, smul_smul] at hc
  have hct : (c : G) * t ∈ normalizer (P : Set G) :=
    smul_eq_iff_mem_normalizer.mp (subtype_injective hc)
  let z := ((c : G) * t) * x * ((c : G) * t)⁻¹
  have hz : z ∈ (P : Subgroup G) := (mem_normalizer_iff.mp hct x).mp hx
  have hcy : (c : G) * y * (c : G)⁻¹ = z := by
    rw [← htx]
    dsimp [z]
    group
  let yP : P.subtype hPC := ⟨⟨y, hPC hy⟩, hy⟩
  let zP : P.subtype hPC := ⟨⟨z, hPC hz⟩, hz⟩
  have hconj : IsConj (yP : C) (zP : C) := by
    apply isConj_iff.mpr
    exact ⟨c, Subtype.ext hcy⟩
  obtain ⟨s, hs⟩ := isConj_iff.mp
    ((P.subtype hPC).isConj_of_isConj_of_normal_pComplement K hcop hquot hconj)
  let a : G := ((s : C) : G)
  have ha : a ∈ (P : Subgroup G) := s.property
  have hay : a * y * a⁻¹ = z :=
    congrArg (fun u : P.subtype hPC => ((u : C) : G)) hs
  refine ⟨a⁻¹ * ((c : G) * t), (normalizer (P : Set G)).mul_mem
    ((normalizer (P : Set G)).inv_mem (le_normalizer ha)) hct, ?_⟩
  calc
    (a⁻¹ * (↑c * t)) * x * (a⁻¹ * (↑c * t))⁻¹ = a⁻¹ * z * a := by dsimp [z]; group
    _ = y := by rw [← hay]; group

end Sylow

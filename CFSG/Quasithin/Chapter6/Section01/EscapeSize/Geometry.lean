module

public import CFSG.Quasithin.Chapter6.Section01.EscapeSize.Basic
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Tactic.Group

/-!
# Geometric splitting and coset orbits in Lemma 6.1.26

Write `W = layer L V`, `A = W^g`, and `B = W^(gl)`, with right
conjugation throughout. This module proves the supplement `L1 = L0 R`,
the splitting `E = W F`, and the conjugation orbit assertion for `eW`.

The precise earlier geometric inputs are kept visible in the theorem types:

* The product identity of 6.1.20(4), `U = (W A) C_U(W A)`.
* The identities of 6.1.21(1–3): `L1 = LU`,
  `R = C_U(W) C_(U^l)(W)`, abelianness of `E`, and
  `[L1,E] ≤ W` (the commutator form of `E/W ≤ Z(L1/W)`).
* At `n = 2`, the geometry used on p.678: `|Z_S| = 4`,
  `|U:C_U(A)| = 4`, `C_(Z_S)(B) = 1`, and `C_(Z_S^l)(A) = 1`.
  An ambient centralizer's `relIndex` in `U` means the index of its
  intersection with `U`; no ambient normality is asserted.

The source chooses `g ∈ I` with `[W,W^g] ≠ 1` and `l ∈ L − H` to obtain
these identities. After they are supplied, the proofs below only need
`g ∈ I` and `l ∈ L`. The natural model supplies normalization of `W`.
The parent source assembly must establish all these earlier geometric facts.

For the supplement, the product expresses `U` modulo `R` using `A`;
conjugating by `l` supplies `B`. For the splitting, each crossed central
line has the full possible centralizer index, so cardinal comparison gives
`E = Z_S C_E(B) = Z_S^l C_E(A)`. Removing the two line components leaves
an element of `C_E(A) ∩ C_E(B) = F`. The equality case `E = W` is explicit.

For the orbit, choose `f ∈ eW ∩ F`. The map `r ↦ [r,f]` is a homomorphism
because `R` centralizes `W` and `[R,E] ≤ W`. Its image is invariant under
`L0`; it is nonzero because otherwise `f ∈ C_T(L) = 1`. The precise
irreducibility premise on `W`, supplied independently from the natural
model, makes this map onto. Only the orbit theorem needs that premise.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
Lemmas 6.1.20–21 and 6.1.26, printed pp.675–676 and 678–679.
The full source theorem and terminal size bound are assembled by the parent.
-/

public section

namespace CFSG.Quasithin.Chapter6.Source.Escape
open Subgroup
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G]

theorem L1_normalizes_R (T L V : Subgroup G) (l : G) :
    L1 T L V l ≤ normalizer (R T L V l : Set G) := by
  have h := le_normalizer_map (H := pCore 2 (L1 T L V l)) (L1 T L V l).subtype
  rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

theorem conjugate_layer_le_U {T L V : Subgroup G} {g : G} (hg : g ∈ I T L V) :
    (layer L V).map (MulAut.conj g⁻¹).toMonoidHom ≤ U T L V :=
  le_iSup (fun x : I T L V => (layer L V).map (MulAut.conj (x : G)).toMonoidHom)
    ⟨g⁻¹, (I T L V).inv_mem hg⟩

theorem L0_le_L1 {T L V : Subgroup G} {g l : G} (hg : g ∈ I T L V) :
    L0 L V g l ≤ L1 T L V l := by
  refine sup_le ((conjugate_layer_le_U hg).trans le_sup_left) ?_
  intro x hx
  obtain ⟨v, hv, rfl⟩ := mem_map.mp hx
  apply (le_sup_right : (U T L V).map (MulAut.conj l⁻¹).toMonoidHom ≤ L1 T L V l)
  apply mem_map.mpr
  refine ⟨g⁻¹ * v * g, ?_, ?_⟩
  · exact conjugate_layer_le_U hg (mem_map.mpr ⟨v, hv, by simp⟩)
  · simp [mul_assoc]

theorem L0_normalizes_R {T L V : Subgroup G} {g l : G} (hg : g ∈ I T L V) :
    L0 L V g l ≤ normalizer (R T L V l : Set G) :=
  (L0_le_L1 hg).trans (L1_normalizes_R T L V l)

/-- The product identity of 6.1.20(4), and the core identity of 6.1.21(2),
are sufficient for the supplement. No irreducibility or splitting is used. -/
theorem supplement_of_geometric_product {T L V : Subgroup G} {g l : G}
    (hg : g ∈ I T L V) (hl : l ∈ L)
    (hL1 : L1 T L V l = L ⊔ U T L V)
    (hVR : layer L V ≤ R T L V l)
    (hCR : U T L V ⊓ centralizer (layer L V : Set G) ≤ R T L V l)
    (hprod : U T L V = (layer L V ⊔
      (layer L V).map (MulAut.conj g⁻¹).toMonoidHom) ⊔
      (U T L V ⊓ centralizer ((layer L V ⊔
        (layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G))) :
    L1 T L V l = L0 L V g l ⊔ R T L V l ∧
      L ≤ L0 L V g l ⊔ R T L V l ∧
      L0 L V g l ≤ normalizer (R T L V l : Set G) := by
  have hLL : L ≤ L1 T L V l := hL1 ▸ le_sup_left
  have hlR := (normalizer (R T L V l : Set G)).inv_mem
    (L1_normalizes_R T L V l (hLL hl))
  have hUR : U T L V ≤ (layer L V).map (MulAut.conj g⁻¹).toMonoidHom ⊔ R T L V l := by
    rw [hprod]
    refine sup_le (sup_le (hVR.trans le_sup_right) le_sup_left) ?_
    exact (inf_le_inf_left _ (centralizer_le (show layer L V ≤ layer L V ⊔
      (layer L V).map (MulAut.conj g⁻¹).toMonoidHom from le_sup_left))).trans
        (hCR.trans le_sup_right)
  have heq : L1 T L V l = L0 L V g l ⊔ R T L V l := by
    apply le_antisymm
    · refine sup_le (hUR.trans (sup_le_sup le_sup_left le_rfl)) ?_
      have hm := map_mono (f := (MulAut.conj l⁻¹).toMonoidHom) hUR
      have hlmap : (R T L V l).map (MulAut.conj l⁻¹).toMonoidHom = R T L V l :=
        mem_normalizer_iff_map_conj_eq.mp hlR
      rw [Subgroup.map_sup, hlmap] at hm
      apply hm.trans
      refine sup_le (le_trans ?_ le_sup_left) le_sup_right
      apply le_trans ?_ le_sup_right
      apply map_le_iff_le_comap.mpr
      intro x hx
      obtain ⟨v, hv, rfl⟩ := mem_map.mp hx
      exact mem_map.mpr ⟨v, hv, by simp [mul_assoc]⟩
    · exact sup_le (L0_le_L1 hg) (pCoreIn_le 2 _)
  exact ⟨heq, heq ▸ hLL, L0_normalizes_R hg⟩

private theorem abelian_normalizes {A B E : Subgroup G}
    (hEE : E ≤ centralizer (E : Set G)) (hAE : A ≤ E) (hBE : B ≤ E) :
    B ≤ normalizer (A : Set G) :=
  ((hBE.trans hEE).trans (centralizer_le hAE)).trans (centralizer_le_normalizer _)

private theorem product_of_mem_sup {A B : Subgroup G}
    (hn : B ≤ normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hx' : x ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hn]
    exact hx
  exact hx'

/-- A fixed-point-free line of the full possible index complements the
centralizer. This is the rank argument on printed p.678. -/
private theorem centralizer_decomposition_of_rank [Finite G] {E Z A : Subgroup G}
    (hEE : E ≤ centralizer (E : Set G)) (hZE : Z ≤ E)
    (hfix : Z ⊓ centralizer (A : Set G) = ⊥)
    (hindex : (centralizer (A : Set G)).relIndex E ≤ Nat.card Z) :
    E = Z ⊔ (E ⊓ centralizer (A : Set G)) := by
  let C := E ⊓ centralizer (A : Set G)
  have hd : Disjoint Z C := disjoint_iff.mpr (eq_bot_iff.mpr (by
    intro x hx
    exact hfix ▸ (show x ∈ Z ⊓ centralizer (A : Set G) from ⟨hx.1, hx.2.2⟩)))
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint Z C
    (abelian_normalizes hEE hZE inf_le_left) hd
  have he := relIndex_mul_relIndex (⊥ : Subgroup G) C E bot_le inf_le_left
  simp only [relIndex_bot_left] at he
  apply (eq_of_le_of_card_ge (sup_le hZE inf_le_left) ?_).symm
  rw [hc, ← he, Nat.mul_comm (Nat.card Z)]
  exact Nat.mul_le_mul_left _ (by simpa only [C, inf_relIndex_left] using hindex)

private theorem centralizer_sup_eq (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) =
      centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show A ≤ A ⊔ B from le_sup_left)) (centralizer_le (show B ≤ A ⊔ B from le_sup_right))
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)

/-- Two complementary centralizer decompositions give the common fixed
factor, with no irreducibility assumption. -/
private theorem split_of_crossed_centralizers {E W Z Z' A B : Subgroup G}
    (hEE : E ≤ centralizer (E : Set G)) (hWE : W ≤ E)
    (hZW : Z ≤ W) (hZ'W : Z' ≤ W)
    (hZA : Z ≤ centralizer (A : Set G))
    (hB : E = Z ⊔ (E ⊓ centralizer (B : Set G)))
    (hA : E = Z' ⊔ (E ⊓ centralizer (A : Set G))) :
    E = W ⊔ (E ⊓ centralizer ((A ⊔ B : Subgroup G) : Set G)) := by
  apply le_antisymm
  · intro e he
    obtain ⟨z', hz', a, ha, rfl⟩ := product_of_mem_sup
      (abelian_normalizes hEE (hZ'W.trans hWE) inf_le_left) (hA ▸ he)
    obtain ⟨z, hz, b, hb, hzb⟩ := product_of_mem_sup
      (abelian_normalizes hEE (hZW.trans hWE) inf_le_left) (hB ▸ ha.1)
    have hbA : b ∈ centralizer (A : Set G) := by
      have hh := (centralizer (A : Set G)).mul_mem
        ((centralizer (A : Set G)).inv_mem (hZA hz)) ha.2
      rw [← hzb, inv_mul_cancel_left] at hh
      exact hh
    have hbF : b ∈ E ⊓ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
      rw [centralizer_sup_eq]
      exact ⟨hb.1, hbA, hb.2⟩
    rw [← hzb, ← mul_assoc]
    exact mul_mem_sup (W.mul_mem (hZ'W hz') (hZW hz)) hbF
  · exact sup_le hWE inf_le_left

/-- The image of the commutator map is invariant under every actor that
normalizes `R` and fixes `f`. Irreducibility makes that map surjective. -/
private theorem commutator_surjective_of_irreducible
    {D R E W T L : Subgroup G}
    (hWE : W ≤ E) (hET : E ≤ T) (hEE : E ≤ centralizer (E : Set G))
    (hRW : R ≤ centralizer (W : Set G)) (hRE : ⁅R, E⁆ ≤ W)
    (hDR : D ≤ normalizer (R : Set G)) (hL : L ≤ D ⊔ R)
    (hCT : T ⊓ centralizer (L : Set G) = ⊥)
    (hirr : ∀ A : Subgroup G, A ≤ W → D ≤ normalizer (A : Set G) → A = ⊥ ∨ A = W)
    {f : G} (hfE : f ∈ E) (hfD : f ∈ centralizer (D : Set G)) (hfW : f ∉ W) :
    ∀ v ∈ W, ∃ r ∈ R, ⁅r, f⁆ = v := by
  have hc (r : R) : ⁅(r : G), f⁆ ∈ W :=
    hRE (commutator_mem_commutator r.property hfE)
  let c : R →* G := {
    toFun := fun r => ⁅(r : G), f⁆
    map_one' := by simp
    map_mul' := by
      intro r s
      change ⁅(r : G) * (s : G), f⁆ = ⁅(r : G), f⁆ * ⁅(s : G), f⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hr := mem_centralizer_iff.mp (hRW r.property) _ (hc s)
      rw [← hr, mul_inv_cancel_right]
      exact mem_centralizer_iff.mp (hEE (hWE (hc r))) _ (hWE (hc s)) }
  have hAW : c.range ≤ W := by
    rintro x ⟨r, rfl⟩
    exact hc r
  have hDA : D ≤ normalizer (c.range : Set G) := by
    apply le_normalizer_iff.mpr
    intro d hd x hx
    obtain ⟨r, rfl⟩ := hx
    have hdr : d * (r : G) * d⁻¹ ∈ R :=
      (mem_normalizer_iff.mp (hDR hd) _).mp r.property
    refine ⟨⟨_, hdr⟩, ?_⟩
    change ⁅d * (r : G) * d⁻¹, f⁆ = d * ⁅(r : G), f⁆ * d⁻¹
    rw [conjugate_commutatorElement]
    have hdf := mem_centralizer_iff.mp hfD d hd
    rw [hdf, mul_inv_cancel_right]
  have hne : c.range ≠ ⊥ := by
    intro hbot
    have hRC : R ≤ centralizer ({f} : Set G) := by
      intro r hr
      apply mem_centralizer_singleton_iff.mpr
      have hh : ⁅r, f⁆ = 1 := by
        have hh : c ⟨r, hr⟩ ∈ c.range := ⟨⟨r, hr⟩, rfl⟩
        simpa only [hbot, mem_bot, c, MonoidHom.coe_mk, OneHom.coe_mk] using hh
      exact (commutatorElement_eq_one_iff_mul_comm.mp hh)
    have hDC : D ≤ centralizer ({f} : Set G) := by
      intro d hd
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hfD d hd)
    have hfL : f ∈ centralizer (L : Set G) := by
      apply mem_centralizer_iff.mpr
      intro x hx
      exact mem_centralizer_singleton_iff.mp ((hL.trans (sup_le hDC hRC)) hx)
    have hf1 : f = 1 := by
      have hh : f ∈ T ⊓ centralizer (L : Set G) := ⟨hET hfE, hfL⟩
      simpa only [hCT, mem_bot] using hh
    exact hfW (hf1 ▸ W.one_mem)
  have heq : c.range = W := (hirr c.range hAW hDA).resolve_left hne
  intro v hv
  obtain ⟨r, hr⟩ := heq ▸ hv
  exact ⟨r, r.property, hr⟩

/-- Preservation of each coset is a consequence of `[R,E] ≤ W` and the
centralization of `W`; it does not need irreducibility. -/
private theorem preserves_cosets_of_commutator_le {R E W : Subgroup G}
    (hWE : W ≤ E) (hEE : E ≤ centralizer (E : Set G))
    (hRW : R ≤ centralizer (W : Set G)) (hRE : ⁅R, E⁆ ≤ W)
    {e r v : G} (he : e ∈ E) (hr : r ∈ R) (hv : v ∈ W) :
    ∃ w ∈ W, r⁻¹ * (e * v) * r = e * w := by
  have hc : ⁅r⁻¹, e⁆ ∈ W := hRE (commutator_mem_commutator (R.inv_mem hr) he)
  refine ⟨⁅r⁻¹, e⁆ * v, W.mul_mem hc hv, ?_⟩
  have hrv := mem_centralizer_iff.mp (hRW hr) v hv
  have hec := mem_centralizer_iff.mp (hEE he) _ (hWE hc)
  calc
    r⁻¹ * (e * v) * r = (r⁻¹ * e * r) * v := by simp only [mul_assoc, hrv]
    _ = (⁅r⁻¹, e⁆ * e) * v := by simp only [commutatorElement_def]; group
    _ = e * (⁅r⁻¹, e⁆ * v) := by rw [hec, mul_assoc]

/-- A common fixed representative in a coset, followed by the surjective
commutator map, proves the literal conjugation orbit assertion. -/
private theorem transitive_cosets_of_split_and_irreducible
    {D R E W T L : Subgroup G}
    (hWE : W ≤ E) (hET : E ≤ T) (hEE : E ≤ centralizer (E : Set G))
    (hRW : R ≤ centralizer (W : Set G)) (hRE : ⁅R, E⁆ ≤ W)
    (hDR : D ≤ normalizer (R : Set G)) (hL : L ≤ D ⊔ R)
    (hCT : T ⊓ centralizer (L : Set G) = ⊥)
    (hirr : ∀ A : Subgroup G, A ≤ W → D ≤ normalizer (A : Set G) → A = ⊥ ∨ A = W)
    (hsplit : E = W ⊔ (E ⊓ centralizer (D : Set G)))
    {e : G} (he : e ∈ E) (heW : e ∉ W) :
    ∀ v ∈ W, ∃ r ∈ R, e * v = r⁻¹ * e * r := by
  obtain ⟨w, hw, f, hf, hwf⟩ := product_of_mem_sup
    (abelian_normalizes hEE hWE inf_le_left) (hsplit ▸ he)
  have hfW : f ∉ W := by
    intro hh
    exact heW (hwf ▸ W.mul_mem hw hh)
  intro v hv
  obtain ⟨s, hs, hsf⟩ := commutator_surjective_of_irreducible hWE hET hEE hRW hRE
    hDR hL hCT hirr hf.1 hf.2 hfW v hv
  refine ⟨s⁻¹, R.inv_mem hs, ?_⟩
  have hsw := mem_centralizer_iff.mp (hRW hs) w hw
  have hfv := mem_centralizer_iff.mp (hEE hf.1) v (hWE hv)
  rw [← hwf, inv_inv]
  symm
  calc
    s * (w * f) * s⁻¹ = w * (s * f * s⁻¹) := by rw [← mul_assoc, ← hsw]; group
    _ = w * (⁅s, f⁆ * f) := by simp only [commutatorElement_def]; group
    _ = w * f * v := by rw [hsf, hfv, ← mul_assoc]

private theorem conjugate_layer_twice (L V : Subgroup G) (g l : G) :
    ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj l⁻¹).toMonoidHom =
      (layer L V).map (MulAut.conj (g * l)⁻¹).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem centralizer_map_equiv (A : Subgroup G) (f : G ≃* G) :
    (centralizer (A : Set G)).map f.toMonoidHom =
      centralizer (A.map f.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine mem_map.mpr ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    apply mem_centralizer_iff.mpr
    intro a ha
    apply f.injective
    simpa using mem_centralizer_iff.mp hx (f a) (mem_map.mpr ⟨a, ha, rfl⟩)

/-- The actual natural model supplies normalization of the layer. -/
private theorem natural_normalizes_layer {L V : Subgroup G}
    (h : IsNaturalModule L (layer L V) 2) :
    L ≤ normalizer (layer L V : Set G) := by
  obtain ⟨_, _, _, _, _, hm⟩ := h
  exact hm.normalizes

/-- The layer belongs to both factors of `E`, since `l` normalizes it. -/
theorem layer_le_E_of_normalizes {T L V : Subgroup G} {l : G}
    (hn : L ≤ normalizer (layer L V : Set G)) (hl : l ∈ L) :
    layer L V ≤ E T L V l := by
  refine le_inf (layer_le_U T L V) ?_
  have hh := map_mono (f := (MulAut.conj l⁻¹).toMonoidHom) (layer_le_U T L V)
  have heq : (layer L V).map (MulAut.conj l⁻¹).toMonoidHom = layer L V :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem (hn hl))
  rw [heq] at hh
  exact hh

/-- Elementary bridges from the core product in 6.1.21(2). In particular,
normality of `R` is relative to `L1`, never ambient normality. -/
theorem core_bridges {T L V : Subgroup G} {l : G}
    (hn : L ≤ normalizer (layer L V : Set G)) (hl : l ∈ L)
    (hEE : E T L V l ≤ centralizer (E T L V l : Set G))
    (hUT : U T L V ≤ T)
    (hR : R T L V l = (U T L V ⊓ centralizer (layer L V : Set G)) ⊔
      ((U T L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓
        centralizer (layer L V : Set G))) :
    layer L V ≤ E T L V l ∧ E T L V l ≤ R T L V l ∧
      E T L V l ≤ T ∧
      E T L V l ≤ U T L V ⊓ centralizer (layer L V : Set G) ∧
      U T L V ⊓ centralizer (layer L V : Set G) ≤ R T L V l ∧
      R T L V l ≤ centralizer (layer L V : Set G) := by
  have hWE := layer_le_E_of_normalizes (T := T) hn hl
  have hEC : E T L V l ≤ U T L V ⊓ centralizer (layer L V : Set G) :=
    le_inf inf_le_left (hEE.trans (centralizer_le hWE))
  have hCR : U T L V ⊓ centralizer (layer L V : Set G) ≤ R T L V l :=
    hR ▸ le_sup_left
  refine ⟨hWE, hEC.trans hCR, inf_le_left.trans hUT, hEC, hCR, ?_⟩
  rw [hR]
  exact sup_le inf_le_right inf_le_right

private theorem geometric_rank_bounds [Finite G] {T L V : Subgroup G} {g l : G}
    (hindex : (centralizer ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G)).relIndex
      (U T L V) = 4) :
    (centralizer ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G)).relIndex
        (E T L V l) ≤ 4 ∧
    (centralizer ((layer L V).map (MulAut.conj (g * l)⁻¹).toMonoidHom : Set G)).relIndex
        (E T L V l) ≤ 4 := by
  have hnon : (4 : ℕ) ≠ 0 := by decide
  refine ⟨(relIndex_le_of_le_right inf_le_left (hindex ▸ hnon)).trans_eq hindex, ?_⟩
  have hi := relIndex_map_map_of_injective
    (centralizer ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G))
    (U T L V) (f := (MulAut.conj l⁻¹).toMonoidHom) (MulAut.conj l⁻¹).injective
  rw [centralizer_map_equiv, conjugate_layer_twice, hindex] at hi
  exact (relIndex_le_of_le_right inf_le_right (hi ▸ hnon)).trans_eq hi

/-- The two centralizer decompositions on p.678 follow by comparing the
index-four bound from 6.1.20(4) with the two fixed-point-free central lines.
The hypotheses `hfixA` and `hfixB` specify the crossed-line geometry; neither
centralizer decomposition nor the desired splitting is an input. -/
theorem centralizer_decompositions_of_geometric_ranks [Finite G]
    {T L V : Subgroup G} {g l : G}
    (hn : L ≤ normalizer (layer L V : Set G)) (hl : l ∈ L)
    (hEE : E T L V l ≤ centralizer (E T L V l : Set G))
    (hZ : Nat.card (ZS T L V) = 4)
    (hindex : (centralizer ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G)).relIndex
      (U T L V) = 4)
    (hfixB : ZS T L V ⊓ centralizer
      ((layer L V).map (MulAut.conj (g * l)⁻¹).toMonoidHom : Set G) = ⊥)
    (hfixA : (ZS T L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓ centralizer
      ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G) = ⊥) :
    E T L V l = ZS T L V ⊔ (E T L V l ⊓ centralizer
      ((layer L V).map (MulAut.conj (g * l)⁻¹).toMonoidHom : Set G)) ∧
    E T L V l = (ZS T L V).map (MulAut.conj l⁻¹).toMonoidHom ⊔
      (E T L V l ⊓ centralizer
        ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G)) := by
  have hWE := layer_le_E_of_normalizes (T := T) hn hl
  have hZlW : (ZS T L V).map (MulAut.conj l⁻¹).toMonoidHom ≤ layer L V := by
    have hh := map_mono (f := (MulAut.conj l⁻¹).toMonoidHom)
      (show ZS T L V ≤ layer L V from inf_le_left)
    have heq : (layer L V).map (MulAut.conj l⁻¹).toMonoidHom = layer L V :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem (hn hl))
    rwa [heq] at hh
  have hZl : Nat.card ((ZS T L V).map (MulAut.conj l⁻¹).toMonoidHom) = 4 :=
    (card_map_of_injective (f := (MulAut.conj l⁻¹).toMonoidHom)
      (MulAut.conj l⁻¹).injective).trans hZ
  obtain ⟨hiA, hiB⟩ := geometric_rank_bounds hindex (l := l)
  exact ⟨centralizer_decomposition_of_rank hEE (inf_le_left.trans hWE) hfixB
      (hiB.trans_eq hZ.symm),
    centralizer_decomposition_of_rank hEE (hZlW.trans hWE) hfixA
      (hiA.trans_eq hZl.symm)⟩

/-- The splitting in the first paragraph of 6.1.26, obtained from the
crossed-line fixed-point identities and the index bound. The equality case
uses `split_of_E_eq_layer` explicitly. -/
theorem split_of_geometric_ranks [Finite G]
    {T L V : Subgroup G} {g l : G}
    (hg : g ∈ I T L V) (hl : l ∈ L)
    (hV : IsNaturalModule L (layer L V) 2)
    (hEE : E T L V l ≤ centralizer (E T L V l : Set G))
    (hZ : Nat.card (ZS T L V) = 4)
    (hindex : (centralizer ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G)).relIndex
      (U T L V) = 4)
    (hfixB : ZS T L V ⊓ centralizer
      ((layer L V).map (MulAut.conj (g * l)⁻¹).toMonoidHom : Set G) = ⊥)
    (hfixA : (ZS T L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓ centralizer
      ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G) = ⊥) :
    E T L V l = layer L V ⊔ F T L V g l := by
  by_cases heq : E T L V l = layer L V
  · exact split_of_E_eq_layer heq
  have hn := natural_normalizes_layer hV
  have hWE := layer_le_E_of_normalizes (T := T) hn hl
  have hZlW : (ZS T L V).map (MulAut.conj l⁻¹).toMonoidHom ≤ layer L V := by
    have hh := map_mono (f := (MulAut.conj l⁻¹).toMonoidHom)
      (show ZS T L V ≤ layer L V from inf_le_left)
    have heq : (layer L V).map (MulAut.conj l⁻¹).toMonoidHom = layer L V :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem (hn hl))
    rwa [heq] at hh
  have hVZ : layer L V ≤ centralizer (ZS T L V : Set G) :=
    (hWE.trans hEE).trans (centralizer_le (inf_le_left.trans hWE))
  have hZA : ZS T L V ≤ centralizer
      ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G) :=
    le_centralizer_iff.mpr ((conjugate_layer_le_U hg).trans (U_centralizes_ZS hVZ))
  obtain ⟨hB, hA⟩ := centralizer_decompositions_of_geometric_ranks hn hl hEE hZ hindex
    hfixB hfixA
  exact split_of_crossed_centralizers hEE hWE inf_le_left hZlW hZA hB hA

/-- The join splitting is the actual set product `E = V_L F`, because
both factors lie in the abelian group `E`. -/
theorem set_product_of_split {T L V : Subgroup G} {g l : G}
    (hEE : E T L V l ≤ centralizer (E T L V l : Set G))
    (hsplit : E T L V l = layer L V ⊔ F T L V g l) :
    (E T L V l : Set G) = (layer L V : Set G) * (F T L V g l : Set G) := by
  have hWE : layer L V ≤ E T L V l := hsplit ▸ le_sup_left
  have hn := abelian_normalizes hEE hWE
    (show F T L V g l ≤ E T L V l from inf_le_left)
  rw [← coe_mul_of_right_le_normalizer_left _ _ hn, hsplit]

/-- The supplement, with all its containment premises obtained from the
natural action and the genuine core-product identity of 6.1.21(2).
Neither splitting nor irreducibility is assumed. -/
theorem supplement_of_geometric_identities {T L V : Subgroup G} {g l : G}
    (hg : g ∈ I T L V) (hl : l ∈ L)
    (hV : IsNaturalModule L (layer L V) 2)
    (hL1 : L1 T L V l = L ⊔ U T L V)
    (hEE : E T L V l ≤ centralizer (E T L V l : Set G))
    (hR : R T L V l = (U T L V ⊓ centralizer (layer L V : Set G)) ⊔
      ((U T L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓
        centralizer (layer L V : Set G)))
    (hprod : U T L V = (layer L V ⊔
      (layer L V).map (MulAut.conj g⁻¹).toMonoidHom) ⊔
      (U T L V ⊓ centralizer ((layer L V ⊔
        (layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G))) :
    L1 T L V l = L0 L V g l ⊔ R T L V l ∧
      L ≤ L0 L V g l ⊔ R T L V l ∧
      L0 L V g l ≤ normalizer (R T L V l : Set G) := by
  have hWE := layer_le_E_of_normalizes (T := T) (natural_normalizes_layer hV) hl
  have hEC : E T L V l ≤ U T L V ⊓ centralizer (layer L V : Set G) :=
    le_inf inf_le_left (hEE.trans (centralizer_le hWE))
  have hCR : U T L V ⊓ centralizer (layer L V : Set G) ≤ R T L V l :=
    hR ▸ le_sup_left
  exact supplement_of_geometric_product hg hl hL1 (hWE.trans (hEC.trans hCR)) hCR hprod

/-- The centrality assertion `E/V_L ≤ Z(L1/V_L)` of 6.1.21(3),
in commutator form, restricts to the actual two-core `R`. -/
theorem core_commutator_le_layer {T L V : Subgroup G} {l : G}
    (hcentral : ⁅L1 T L V l, E T L V l⁆ ≤ layer L V) :
    ⁅R T L V l, E T L V l⁆ ≤ layer L V :=
  (commutator_mono (pCoreIn_le 2 _) le_rfl).trans hcentral

/-- Preservation of all layer cosets follows directly from the core and
central-quotient identities. It requires neither splitting nor irreducibility. -/
theorem preserves_cosets_of_geometric_identities {T L V : Subgroup G} {l : G}
    (hl : l ∈ L) (hV : IsNaturalModule L (layer L V) 2)
    (hEE : E T L V l ≤ centralizer (E T L V l : Set G))
    (hR : R T L V l = (U T L V ⊓ centralizer (layer L V : Set G)) ⊔
      ((U T L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓
        centralizer (layer L V : Set G)))
    (hcentral : ⁅L1 T L V l, E T L V l⁆ ≤ layer L V)
    {e r v : G} (he : e ∈ E T L V l) (hr : r ∈ R T L V l) (hv : v ∈ layer L V) :
    ∃ w ∈ layer L V, r⁻¹ * (e * v) * r = e * w := by
  have hWE := layer_le_E_of_normalizes (T := T) (natural_normalizes_layer hV) hl
  have hRW : R T L V l ≤ centralizer (layer L V : Set G) := by
    rw [hR]
    exact sup_le inf_le_right inf_le_right
  exact preserves_cosets_of_commutator_le hWE hEE hRW (core_commutator_le_layer hcentral)
    he hr hv

/-- Conditional geometric assembly of 6.1.26(1). The source product and
core identities first give the supplement, and the crossed-line geometry
gives `E = V_L F`. Only the orbit assertion uses irreducibility on `V_L`.
The parent must discharge the displayed earlier geometric and model facts.
-/
theorem cosets_of_geometric_identities [Finite G] {T L V : Subgroup G} {g l : G}
    (hg : g ∈ I T L V) (hl : l ∈ L)
    (hV : IsNaturalModule L (layer L V) 2)
    (hL1 : L1 T L V l = L ⊔ U T L V)
    (hEE : E T L V l ≤ centralizer (E T L V l : Set G))
    (hUT : U T L V ≤ T)
    (hR : R T L V l = (U T L V ⊓ centralizer (layer L V : Set G)) ⊔
      ((U T L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓
        centralizer (layer L V : Set G)))
    (hprod : U T L V = (layer L V ⊔
      (layer L V).map (MulAut.conj g⁻¹).toMonoidHom) ⊔
      (U T L V ⊓ centralizer ((layer L V ⊔
        (layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G)))
    (hcentral : ⁅L1 T L V l, E T L V l⁆ ≤ layer L V)
    (hZ : Nat.card (ZS T L V) = 4)
    (hindex : (centralizer ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G)).relIndex
      (U T L V) = 4)
    (hfixB : ZS T L V ⊓ centralizer
      ((layer L V).map (MulAut.conj (g * l)⁻¹).toMonoidHom : Set G) = ⊥)
    (hfixA : (ZS T L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓ centralizer
      ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G) = ⊥)
    (hCT : T ⊓ centralizer (L : Set G) = ⊥)
    (hirr : ∀ A : Subgroup G, A ≤ layer L V →
      L0 L V g l ≤ normalizer (A : Set G) → A = ⊥ ∨ A = layer L V) :
    (∀ e ∈ E T L V l, ∀ r ∈ R T L V l, ∀ v ∈ layer L V,
      ∃ w ∈ layer L V, r⁻¹ * (e * v) * r = e * w) ∧
    (∀ e ∈ E T L V l, e ∉ layer L V → ∀ v ∈ layer L V,
      ∃ r ∈ R T L V l, e * v = r⁻¹ * e * r) := by
  obtain ⟨hWE, _, hET, _, _, hRW⟩ :=
    core_bridges (natural_normalizes_layer hV) hl hEE hUT hR
  obtain ⟨_, hL, hDR⟩ := supplement_of_geometric_identities hg hl hV hL1 hEE hR hprod
  have hsplit := split_of_geometric_ranks hg hl hV hEE hZ hindex hfixB hfixA
  have hRE := core_commutator_le_layer hcentral
  refine ⟨fun e he r hr v hv =>
    preserves_cosets_of_geometric_identities hl hV hEE hR hcentral he hr hv, ?_⟩
  intro e he heW
  exact transitive_cosets_of_split_and_irreducible hWE hET hEE hRW hRE hDR hL hCT
    hirr hsplit he heW

end CFSG.Quasithin.Chapter6.Source.Escape

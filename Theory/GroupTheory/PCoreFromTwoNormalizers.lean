module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Index
public import Theory.GroupTheory.SubgroupEnumeration

/-!
# Intrinsic p-cores from two normalizers

Let P be a p-subgroup containing nontrivial subgroups U and V. Suppose every
x outside both normalizers generates the ambient group together with P.
A proper overgroup of P is then contained in the union of the normalizers.
A subgroup contained in a union of two subgroups lies in one of them, so U
or V gives a nontrivial normal p-subgroup of the overgroup itself.

For an overgroup of index prime to p, the fixed-point theorem on its cosets
first conjugates P into it. The final core is intrinsic to that overgroup;
no ambient normality is inferred. A double-coset variant separates the
finite coverage and generator-recovery obligations.

Source application: the Rudvalis Sylow-overgroup analysis used in
Aschbacher--Smith, proof of Proposition 1.3.4, printed p.511 (PDF p.528),
citing Aschbacher, *Overgroups of Sylow subgroups in sporadic groups* (1986).
The argument here is general finite-group theory; the required concrete
normalizer and generation assertions are separate obligations.
-/

namespace Subgroup

variable {G : Type*} [Group G] {p : ℕ}

/-- A p-subgroup fixes a coset of any subgroup of index prime to p. -/
public theorem exists_conj_overgroup_of_index_primeTo [Fact p.Prime]
    (P M : Subgroup G) (hP : IsPGroup p P) (hindex : ¬ p ∣ M.index) :
    ∃ g : G, P ≤ M.comap (MulAut.conj g).toMonoidHom := by
  let : MulAction P (G ⧸ M) := MulAction.compHom (G ⧸ M) P.subtype
  obtain ⟨q, hq⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ M) hindex
  induction q using Quotient.inductionOn' with
  | h g =>
    refine ⟨g⁻¹, ?_⟩
    intro x hx
    have hf := (MulAction.mem_fixedPoints.mp hq ⟨x, hx⟩).symm
    change (g : G ⧸ M) = ((x * g : G) : G ⧸ M) at hf
    have hm := QuotientGroup.eq.mp hf
    change g⁻¹ * x * (g⁻¹)⁻¹ ∈ M
    simpa only [inv_inv, mul_assoc] using hm

/-- A nontrivial p-subgroup normalized by M lies in its intrinsic p-core. -/
public theorem pCore_ne_bot_of_normalized_nontrivial
    (M U : Subgroup G) (hUM : U ≤ M) (hU : IsPGroup p U) (hne : U ≠ ⊥)
    (hnorm : M ≤ normalizer (U : Set G)) : pCore p M ≠ ⊥ := by
  let _ : (U.subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUM).mpr hnorm
  have hle : U.subgroupOf M ≤ pCore p M :=
    le_sSup ⟨inferInstance, hU.of_equiv (subgroupOfEquivOfLe hUM).symm⟩
  intro hbot
  have hUb : U.subgroupOf M = ⊥ := bot_unique (hle.trans_eq hbot)
  have hm := congrArg (Subgroup.map M.subtype) hUb
  rw [map_subgroupOf_eq_of_le hUM, map_bot] at hm
  exact hne hm

/-- The two-normalizer generation condition forces a core in every proper
overgroup of P. -/
public theorem pCore_ne_bot_of_two_normalizers
    (P U V M : Subgroup G) (hP : IsPGroup p P)
    (hUP : U ≤ P) (hVP : V ≤ P) (hU : U ≠ ⊥) (hV : V ≠ ⊥)
    (hgen : ∀ g : G, g ∉ normalizer (U : Set G) →
      g ∉ normalizer (V : Set G) → closure (insert g (P : Set G)) = ⊤)
    (hPM : P ≤ M) (hM : M ≠ ⊤) : pCore p M ≠ ⊥ := by
  have hcover : (M : Set G) ⊆
      (normalizer (U : Set G) : Set G) ∪ (normalizer (V : Set G) : Set G) := by
    intro g hg
    by_contra hn
    have hgn := not_or.mp hn
    have hle : closure (insert g (P : Set G)) ≤ M :=
      (closure_le M).mpr (by rintro x (rfl | hx); exact hg; exact hPM hx)
    exact hM (top_unique ((hgen g hgn.1 hgn.2) ▸ hle))
  rcases SubgroupClass.subset_union.mp hcover with hMU | hMV
  · exact pCore_ne_bot_of_normalized_nontrivial M U (hUP.trans hPM)
      (hP.to_le hUP) hU hMU
  · exact pCore_ne_bot_of_normalized_nontrivial M V (hVP.trans hPM)
      (hP.to_le hVP) hV hMV

/-- Conjugating P into M gives the same conclusion for prime-to-p index.
P itself need not be a Sylow subgroup. -/
public theorem pCore_ne_bot_of_two_normalizers_of_index_primeTo [Fact p.Prime]
    (P U V M : Subgroup G) (hP : IsPGroup p P)
    (hUP : U ≤ P) (hVP : V ≤ P) (hU : U ≠ ⊥) (hV : V ≠ ⊥)
    (hgen : ∀ g : G, g ∉ normalizer (U : Set G) →
      g ∉ normalizer (V : Set G) → closure (insert g (P : Set G)) = ⊤)
    (hM : M ≠ ⊤) (hindex : ¬ p ∣ M.index) : pCore p M ≠ ⊥ := by
  obtain ⟨g, hg⟩ := exists_conj_overgroup_of_index_primeTo P M hP hindex
  let e := MulAut.conj g
  let K := M.comap e.toMonoidHom
  have hK : K ≠ ⊤ := by
    intro htop
    apply hM
    apply comap_injective (f := e.toMonoidHom) e.surjective
    exact htop.trans (comap_top _).symm
  have hcore := pCore_ne_bot_of_two_normalizers P U V K hP hUP hVP hU hV hgen hg hK
  let f : K ≃* M := (e.subgroupMap K).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective e.surjective M))
  intro hbot
  apply hcore
  apply ((pCore p K).map_eq_bot_iff_of_injective (f := f.toMonoidHom) f.injective).mp
  rw [pCore_map_iso p f, hbot]

/-- Double-coset coverage and one recovery check per representative imply
the generation condition. The representatives need not be distinct. -/
public theorem generation_outside_two_normalizers_of_doubleCosetCover
    (P U V : Subgroup G)
    (hPU : P ≤ normalizer (U : Set G)) (hPV : P ≤ normalizer (V : Set G))
    {ι : Type*} (r : ι → G)
    (hcover : Theory.GroupTheory.SubgroupEnumeration.DoubleCosetCover P r)
    (hstep : ∀ i, r i ∈ normalizer (U : Set G) ∨
      r i ∈ normalizer (V : Set G) ∨ closure (insert (r i) (P : Set G)) = ⊤) :
    ∀ g : G, g ∉ normalizer (U : Set G) →
      g ∉ normalizer (V : Set G) → closure (insert g (P : Set G)) = ⊤ := by
  intro g hgU hgV
  obtain ⟨i, a, b, ha, hb, heq⟩ := hcover g
  rcases hstep i with hr | hr | hr
  · exact (hgU (heq ▸ (normalizer (U : Set G)).mul_mem
      ((normalizer (U : Set G)).mul_mem (hPU ha) hr) (hPU hb))).elim
  · exact (hgV (heq ▸ (normalizer (V : Set G)).mul_mem
      ((normalizer (V : Set G)).mul_mem (hPV ha) hr) (hPV hb))).elim
  · let K := closure (insert g (P : Set G))
    have hPK : P ≤ K := fun x hx => subset_closure (Set.mem_insert_of_mem g hx)
    have hgK : g ∈ K := subset_closure (Set.mem_insert g _)
    have hrK : r i ∈ K := by
      have hm := K.mul_mem (K.mul_mem (K.inv_mem (hPK ha)) hgK) (K.inv_mem (hPK hb))
      rw [heq] at hm
      simpa only [← mul_assoc, mul_inv_cancel_right, inv_mul_cancel, one_mul] using hm
    have hle : closure (insert (r i) (P : Set G)) ≤ K :=
      (closure_le K).mpr (by rintro x (rfl | hx); exact hrK; exact hPK hx)
    exact top_unique (hr ▸ hle)

end Subgroup

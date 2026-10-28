module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction

/-!
# Replacing the T-orbit by the N_T(P)-orbit

The intrinsic 1.3.2 input supplies T = O₂(X) N_T(P), but does not assert
that all of T normalizes P. Since O₂(X) is T-invariant, its normalization
of L identifies these two conjugate orbits. When the H-normalizer of L
has index two, O₂(X) = [O₂(X),P] supplies that normalization.
This justifies the commutator generation step using the actual N_T(P)
action. Relative normality of the orbit remains a separate obligation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.510,
using Lemma 1.3.2(2)–(3), printed p.509.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G]

/-- The two-core of X normalizes any subgroup of H whose H-normalizer has
index two. This uses Q = [Q,P], not a Sylow hypothesis in H. -/
theorem LocalInput.core_le_normalizer_of_index_two
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hLH : L ≤ H) (hi : (normalizer (L.subgroupOf H : Set H)).index = 2) :
    X.pCoreIn 2 ≤ normalizer L := by
  classical
  rw [h.core_commutator]
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  have hxH := le_sup_left.trans h.overgroup (pCoreIn_le 2 X hx)
  have hyH := le_sup_left.trans h.overgroup (le_sup_right.trans h.complement.le hy)
  have hn : ⁅(⟨x, hxH⟩ : H), (⟨y, hyH⟩ : H)⁆ ∈ normalizer (L.subgroupOf H : Set H) := by
    simp only [commutatorElement_def, mul_mem_iff_of_index_two hi, inv_mem_iff]
    by_cases hxN : (⟨x, hxH⟩ : H) ∈ normalizer (L.subgroupOf H : Set H) <;>
      by_cases hyN : (⟨y, hyH⟩ : H) ∈ normalizer (L.subgroupOf H : Set H) <;>
      simp [hxN, hyN]
  rwa [← subgroupOf_normalizer_eq hLH] at hn

/-- The normalizer factorization in 1.3.2 identifies the actual T-orbit with
the N_T(P)-orbit whenever O₂(X) fixes L. -/
theorem LocalInput.componentOrbit_eq_normalizerOrbit
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hQL : X.pCoreIn 2 ≤ normalizer L) :
    componentOrbit L T = componentOrbit L (T ⊓ normalizer P) := by
  let Q := X.pCoreIn 2
  let S := T ⊓ normalizer P
  have hQT : Q ≤ T := le_sup_left.trans h.normalizer_factor.ge
  have hST : S ≤ T := inf_le_left
  have hTQ : T ≤ normalizer Q := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    dsimp [Q]
    rw [map_pCoreIn_of_injective 2 X _ (MulAut.conj t).injective,
      mem_normalizer_iff_map_conj_eq.mp (h.invariant ht)]
  let _ : (Q.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hQT).mpr hTQ
  have hgen : S.subgroupOf T ⊔ Q.subgroupOf T = ⊤ := by
    apply map_injective T.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hST, map_subgroupOf_eq_of_le hQT,
      ← MonoidHom.range_eq_map, range_subtype]
    exact (sup_comm _ _).trans h.normalizer_factor.symm
  apply le_antisymm
  · apply iSup_le
    intro t
    have ht : t ∈ S.subgroupOf T ⊔ Q.subgroupOf T := hgen.symm ▸ mem_top t
    obtain ⟨s, hs, q, hq, he⟩ := mem_sup_of_normal_right.mp ht
    have hm : (MulAut.conj (s : G)).toMonoidHom.comp
        (MulAut.conj (q : G)).toMonoidHom = (MulAut.conj (t : G)).toMonoidHom := by
      ext g
      have he' : (s : G) * q = t := congrArg Subtype.val he
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        ← he', mul_inv_rev, mul_assoc]
    have hmap : L.map (MulAut.conj (t : G)).toMonoidHom =
        L.map (MulAut.conj (s : G)).toMonoidHom := by
      have hqmap : L.map (MulAut.conj (q : G)).toMonoidHom = L :=
        mem_normalizer_iff_map_conj_eq.mp (hQL hq)
      rw [← hm, ← map_map, hqmap]
    rw [hmap]
    exact le_iSup (fun a : S => L.map (MulAut.conj (a : G)).toMonoidHom) ⟨s, hs⟩
  · apply iSup_le
    intro s
    exact le_iSup (fun a : T => L.map (MulAut.conj (a : G)).toMonoidHom) ⟨s, s.property.1⟩

/-- A commutator containing L generates its whole N_T(P)-orbit. The hypotheses
separate the genuine orbit comparison and normality obligations. -/
theorem LocalInput.commutator_componentOrbit_eq
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hQL : X.pCoreIn 2 ≤ normalizer L) (hLC : L ≤ ⁅L, P⁆)
    (hPK : P ≤ normalizer (componentOrbit L T)) :
    ⁅componentOrbit L T, P⁆ = componentOrbit L T := by
  let K := componentOrbit L T
  let S := T ⊓ normalizer P
  have hSK : S ≤ normalizer K := inf_le_left.trans (le_normalizer_componentOrbit L T)
  have hSC : S ≤ normalizer (⁅K, P⁆ : Subgroup G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hSK hs),
      mem_normalizer_iff_map_conj_eq.mp hs.2]
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp hPK)
  calc
    K = componentOrbit L S := h.componentOrbit_eq_normalizerOrbit hQL
    _ ≤ ⁅K, P⁆ := iSup_conjugates_le_of_le_normalizer L S ⁅K, P⁆
      (hLC.trans (commutator_mono (le_componentOrbit L T) le_rfl)) hSC

end CFSG.Quasithin.Chapter1.XiEmbedding

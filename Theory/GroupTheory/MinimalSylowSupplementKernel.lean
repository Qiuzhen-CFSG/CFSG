module

public import Mathlib.GroupTheory.Frattini
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Solvable kernels of minimal Sylow supplements

Suppose a finite group is minimal among the supplements of a normal subgroup
`N` which contain a prescribed Sylow `p`-subgroup `S`. If `S ∩ N` is normal in
the whole group, then `N` is solvable.

First, a normal subgroup of order prime to `p` in this configuration lies in
the Frattini subgroup: any maximal subgroup supplementing it has index prime
to `p`, so contains an ambient Sylow subgroup; conjugacy then contradicts
minimality. Apply this to the image of `N` after quotienting by `S ∩ N`.
That image is a subgroup of the finite, nilpotent Frattini subgroup, while
`S ∩ N` is a `p`-group. Solvability follows by extension.

This elementary argument supplies the kernel step in Aschbacher--Smith,
*The Classification of Quasithin Groups*, E.1.10, printed p.211, without
appealing to solvability of arbitrary odd-order groups.
-/

public section

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
private theorem coprime_index {N M : Subgroup G} [N.Normal]
    (hn : ¬ p ∣ Nat.card N) (hs : M ⊔ N = ⊤) : ¬ p ∣ M.index := by
  have he : (M ⊓ N).relIndex M * M.index =
      (M ⊓ N).relIndex M * (M ⊓ N).relIndex N := by
    calc
      _ = (M ⊓ N).relIndex (M ⊔ N) := by
        rw [← relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left, hs,
          relIndex_top_right]
      _ = (M ⊓ N).relIndex N * N.relIndex (M ⊔ N) :=
        (relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right).symm
      _ = _ := by rw [relIndex_sup_right, inf_relIndex_left, Nat.mul_comm]
  have hi : M.index = (M ⊓ N).relIndex N :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) he
  exact fun hd => hn (hd.trans (hi ▸ relIndex_dvd_card (M ⊓ N) N))

/-- A normal subgroup of order prime to `p` belongs to the Frattini subgroup
when no proper supplement contains the prescribed Sylow `p`-subgroup. -/
theorem Sylow.normal_le_frattini_of_minimal_supplement (S : Sylow p G) (N : Subgroup G) [N.Normal]
    (hn : ¬ p ∣ Nat.card N)
    (hmin : ∀ L : Subgroup G, (S : Subgroup G) ≤ L → L ⊔ N = ⊤ → L = ⊤) :
    N ≤ frattini G := by
  classical
  change N ≤ ⨅ M ∈ {H : Subgroup G | IsCoatom H}, M
  refine le_iInf fun M => le_iInf fun hM => ?_
  by_contra hNM
  have hs : M ⊔ N = ⊤ :=
    hM.2 _ (lt_of_le_of_ne le_sup_left (fun he => hNM (le_sup_right.trans_eq he.symm)))
  have hi : ¬ p ∣ M.index := coprime_index hn hs
  let R : Sylow p M := Classical.choice inferInstance
  have hRi : ¬ p ∣ ((R : Subgroup M).map M.subtype).index := by
    rw [index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul R.not_dvd_index hi
  let Q : Sylow p G := (R.isPGroup'.map M.subtype).toSylow hRi
  have hQM : (Q : Subgroup G) ≤ M := map_subtype_le _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  let c := (MulAut.conj g).toMonoidHom
  have hNc : N.map c = N := by
    apply le_antisymm
    · rintro _ ⟨n, hn, rfl⟩
      exact (inferInstance : N.Normal).conj_mem n hn g
    · intro n hn
      refine ⟨g⁻¹ * n * g, ?_, ?_⟩
      · simpa using (inferInstance : N.Normal).conj_mem n hn g⁻¹
      · simp [c, MulAut.conj_apply, mul_assoc]
  have hSc : (S : Subgroup G) ≤ M.map c := by
    rw [← hg]
    exact map_mono hQM
  have hsup : M.map c ⊔ N = ⊤ := by
    rw [← hNc, ← Subgroup.map_sup, hs, map_top_of_surjective c (MulAut.conj g).surjective]
  have htop := hmin (M.map c) hSc hsup
  have hMt : M = ⊤ := by
    apply map_injective (f := c) (MulAut.conj g).injective
    simpa only [map_top_of_surjective c (MulAut.conj g).surjective] using htop
  exact hM.1 hMt

/-- A minimal supplement over a Sylow subgroup has solvable kernel whenever
the Sylow intersection with the kernel is normal in the whole supplement. -/
theorem Sylow.isSolvable_of_minimal_supplement (S : Sylow p G) (N : Subgroup G) [N.Normal]
    (hnormal : ((S : Subgroup G) ⊓ N).Normal)
    (hmin : ∀ L : Subgroup G, (S : Subgroup G) ≤ L → L ⊔ N = ⊤ → L = ⊤) :
    Group.IsSolvable N := by
  let P : Subgroup G := (S : Subgroup G) ⊓ N
  let : P.Normal := hnormal
  let q := QuotientGroup.mk' P
  have hq := QuotientGroup.mk'_surjective P
  let D := N.map q
  let : D.Normal := (inferInstance : N.Normal).map q hq
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal N
  have hPN : P.subgroupOf N = (R : Subgroup N) := by
    rw [hR]
    ext x
    exact and_iff_left x.property
  have hDcard : ¬ p ∣ Nat.card D := by
    have he : Nat.card D = (R : Subgroup N).index := by
      rw [← relIndex_ker N q]
      change (QuotientGroup.mk' P).ker.relIndex N = _
      rw [QuotientGroup.ker_mk', relIndex, hPN]
    rw [he]
    exact R.not_dvd_index
  have hDmin : ∀ L : Subgroup (G ⧸ P),
      (S.mapSurjective hq : Subgroup (G ⧸ P)) ≤ L → L ⊔ D = ⊤ → L = ⊤ := by
    intro L hSL hLD
    have hSL' : (S : Subgroup G) ≤ L.comap q := map_le_iff_le_comap.mp hSL
    have hDN : D.comap q = N := by
      change (N.map q).comap q = N
      rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr inf_le_right]
    have hLN : L.comap q ⊔ N = ⊤ := by
      rw [← hDN, comap_sup_eq q L D hq, hLD, comap_top]
    have ht := hmin (L.comap q) hSL' hLN
    have he := congrArg (Subgroup.map q) ht
    rw [map_comap_eq_self_of_surjective hq, map_top_of_surjective q hq] at he
    exact he
  have hDF := Sylow.normal_le_frattini_of_minimal_supplement (S.mapSurjective hq) D hDcard hDmin
  let := frattini_nilpotent (G := G ⧸ P)
  have : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hDF)
  let f := q.subgroupMap N
  have hfker : f.ker = (R : Subgroup N) := by
    rw [show f.ker = (q.subgroupMap N).ker from rfl, ker_subgroupMap,
      QuotientGroup.ker_mk', hPN]
  have : Group.IsNilpotent f.ker := by
    rw [hfker]
    exact R.isPGroup'.isNilpotent
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp)

module
public import FeitThompson.BGsection6.Defs
public import Theory.GroupTheory.AutomorphismInvariantNormalKernel

/-!
# Maximum abelian intersection with an invariant normal kernel

Choose an outside maximum-order abelian subgroup A maximizing |A intersect N|.
The join of all maximum abelian subgroups with larger intersections lies in Q.
Once maximum abelian order agrees in Q and S, that join is ambient-normal and
fixed by the given automorphism. Maximality of the invariant normal kernel
puts the entire join in N. The abelian replacement (A intersect Q)V belongs
to the join, which gives A intersect Q = A intersect N.

The proof uses literal maximum-order abelian subgroups throughout. The
replacement and equality of maximum orders are the independent counting
conclusions of Niles7.4, not conclusions of the selection argument.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma7.5, printed p.61.
-/

public section
open Subgroup
namespace Glauberman
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] [Finite H] in
private theorem maximum_abelian_map {P A : Subgroup G} (f : G →* H)
    (hf : Function.Injective f) (hA : A ∈ thompsonAbelianSubgroups P) :
    A.map f ∈ thompsonAbelianSubgroups (P.map f) := by
  let _ := hA.2.1
  refine ⟨map_mono hA.1, ?_, ?_⟩
  · exact IsMulCommutative.of_setLike_mul_comm fun x hx y hy => by
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      simpa only [← map_mul] using congrArg f (setLike_mul_comm ha hb)
  · intro B hB hBc
    have hpre : B.comap f ≤ P := by
      intro x hx
      obtain ⟨y, hy, he⟩ := hB hx
      exact hf he ▸ hy
    have hprecomm : IsMulCommutative (B.comap f) := by
      let _ := hBc
      exact IsMulCommutative.of_setLike_mul_comm fun x hx y hy => by
        apply hf
        simpa only [map_mul] using setLike_mul_comm (s := B) hx hy
    have hmap : (B.comap f).map f = B :=
      map_comap_eq_self (hB.trans (map_le_range _ _))
    rw [← hmap, card_map_of_injective hf, card_map_of_injective hf]
    exact hA.2.2 _ hpre hprecomm

omit [Finite H] in
private theorem maximum_abelian_of_map {P A : Subgroup G} (f : G →* H)
    (hf : Function.Injective f) (hA : A.map f ∈ thompsonAbelianSubgroups (P.map f)) :
    A ∈ thompsonAbelianSubgroups P := by
  have hAP : A ≤ P := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hA.1 (mem_map_of_mem f hx)
    exact hf he ▸ hy
  have hc : IsMulCommutative A := by
    let _ := hA.2.1
    exact IsMulCommutative.of_setLike_mul_comm fun x hx y hy => by
      apply hf
      simpa only [map_mul] using
        setLike_mul_comm (mem_map_of_mem f hx) (mem_map_of_mem f hy)
  refine ⟨hAP,hc,?_⟩
  intro B hBP hBc
  have hb := maximum_abelian_map f hf (show B ∈ thompsonAbelianSubgroups B from
    ⟨le_rfl,hBc,fun C hC _ => Nat.card_le_card_of_injective (Subgroup.inclusion hC)
      (Subgroup.inclusion_injective hC)⟩)
  have hh := hA.2.2 (B.map f) (map_mono hBP) hb.2.1
  simpa only [card_map_of_injective hf] using hh

/-- Join of the maximum abelian subgroups whose intersection with N exceeds k. -/
@[expose] def maximumIntersectionJoin (P N : Subgroup G) (k : ℕ) : Subgroup G :=
  sSup {B : Subgroup G | B ∈ thompsonAbelianSubgroups P ∧ k < Nat.card ↥(B ⊓ N)}

omit [Finite H] in
private theorem maximumIntersectionJoin_map (P N : Subgroup G) (k : ℕ)
    (f : G →* H) (hf : Function.Injective f) :
    (maximumIntersectionJoin P N k).map f = maximumIntersectionJoin (P.map f) (N.map f) k := by
  apply le_antisymm
  · rw [maximumIntersectionJoin, sSup_eq_iSup, Subgroup.map_iSup]
    apply iSup_le
    intro B
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hB
    apply le_sSup
    refine ⟨maximum_abelian_map f hf hB.1, ?_⟩
    rw [← map_inf _ _ _ hf, card_map_of_injective hf]
    exact hB.2
  · apply sSup_le
    intro B hB
    have hmap : (B.comap f).map f = B :=
      map_comap_eq_self (hB.1.1.trans (map_le_range _ _))
    have hpre : B.comap f ∈ thompsonAbelianSubgroups P :=
      maximum_abelian_of_map f hf (by rw [hmap]; exact hB.1)
    have hi : k < Nat.card ↥(B.comap f ⊓ N) := by
      have hh := hB.2
      rw [← hmap, ← map_inf _ _ _ hf, card_map_of_injective hf] at hh
      exact hh
    rw [← hmap]
    exact map_mono (le_sSup ⟨hpre,hi⟩)

omit [Finite G] in
private theorem maximumIntersectionJoin_eq_of_le {P Q N : Subgroup G} (k : ℕ)
    (hQP : Q ≤ P)
    (hfamily : thompsonAbelianSubgroups Q ⊆ thompsonAbelianSubgroups P)
    (hinside : ∀ B : Subgroup G, B ∈ thompsonAbelianSubgroups P →
      k < Nat.card ↥(B ⊓ N) → B ≤ Q) :
    maximumIntersectionJoin P N k = maximumIntersectionJoin Q N k := by
  apply le_antisymm
  · apply sSup_le
    intro B hB
    exact le_sSup ⟨thompsonAbelianSubgroups_mem_of_le hQP hB.1 (hinside B hB.1 hB.2),hB.2⟩
  · apply sSup_le
    intro B hB
    exact le_sSup ⟨hfamily hB.1,hB.2⟩

private theorem maximumIntersectionJoin_normal (Q N : Subgroup G) (k : ℕ)
    [Q.Normal] [N.Normal] : (maximumIntersectionJoin Q N k).Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  rw [maximumIntersectionJoin_map Q N k _ (MulAut.conj g).injective,
    (normal_iff_map_conj_eq.mp (inferInstance : Q.Normal)) g,
    (normal_iff_map_conj_eq.mp (inferInstance : N.Normal)) g]


/-- Niles7.5: maximum abelian replacement and the invariant-normal kernel
select an outside maximum abelian subgroup with the same Q and N intersection. -/
theorem exists_maximum_abelian_kernel_intersection
    (S : Subgroup H) (α : MulAut S) (Q V : Subgroup H) [Q.Normal]
    (hQS : Q ≤ S)
    (hfamily : thompsonAbelianSubgroups Q ⊆ thompsonAbelianSubgroups S)
    (hex : ∃ A : Subgroup H, A ∈ thompsonAbelianSubgroups S ∧ ¬ A ≤ Q)
    (hreplace : ∀ A : Subgroup H, A ∈ thompsonAbelianSubgroups S → ¬ A ≤ Q →
      (A ⊓ Q) ⊔ V ∈ thompsonAbelianSubgroups S ∧ ¬ V ≤ A)
    (hNQ : (NilesRankOneKernel.invariantNormalKernel S α).map S.subtype ≤ Q)
    (hVN : V ≤ (NilesRankOneKernel.invariantNormalKernel S α).map S.subtype) :
    ∃ A : Subgroup H, A ∈ thompsonAbelianSubgroups S ∧ ¬ A ≤ Q ∧
      A ⊓ Q = A ⊓ (NilesRankOneKernel.invariantNormalKernel S α).map S.subtype := by
  classical
  let N := NilesRankOneKernel.invariantNormalKernel S α
  let NM := N.map S.subtype
  let t : Set (Subgroup H) := {A | A ∈ thompsonAbelianSubgroups S ∧ ¬ A ≤ Q}
  obtain ⟨A,hA,hmax⟩ := Set.exists_max_image t (fun B => Nat.card ↥(B ⊓ NM))
    (Set.toFinite t) hex
  have hinside : ∀ B : Subgroup H, B ∈ thompsonAbelianSubgroups S →
      Nat.card ↥(A ⊓ NM) < Nat.card ↥(B ⊓ NM) → B ≤ Q := by
    intro B hB hlarge
    by_contra hBQ
    exact (not_lt_of_ge (hmax B ⟨hB,hBQ⟩)) hlarge
  let k := Nat.card ↥(A ⊓ NM)
  let P := maximumIntersectionJoin (⊤ : Subgroup S) N k
  have himage : P.map S.subtype = maximumIntersectionJoin Q NM k := by
    rw [maximumIntersectionJoin_map _ _ _ S.subtype S.subtype_injective]
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact maximumIntersectionJoin_eq_of_le k hQS hfamily hinside
  have hnormal : (P.map S.subtype).Normal := by
    rw [himage]
    exact maximumIntersectionJoin_normal Q NM k
  have hfixed : P.map α.toMonoidHom = P := by
    dsimp only [P]
    rw [maximumIntersectionJoin_map _ _ _ _ α.injective]
    rw [Subgroup.map_top_of_surjective _ α.surjective]
    dsimp only [N]
    rw [NilesRankOneKernel.invariantNormalKernel_fixed]
  have hPN : P ≤ N := NilesRankOneKernel.le_invariantNormalKernel S α P hnormal hfixed
  have hjN : maximumIntersectionJoin S NM k ≤ NM := by
    have he := maximumIntersectionJoin_eq_of_le k hQS hfamily hinside
    rw [he,← himage]
    exact map_mono hPN
  obtain ⟨hr,hnV⟩ := hreplace A hA.1 hA.2
  let B := (A ⊓ Q) ⊔ V
  have hinc : A ⊓ NM ≤ B ⊓ NM := by
    intro x hx
    exact ⟨mem_sup_left ⟨hx.1,hNQ hx.2⟩,hx.2⟩
  have hstrict : Nat.card ↥(A ⊓ NM) < Nat.card ↥(B ⊓ NM) := by
    apply lt_of_le_of_ne (card_le_of_le hinc)
    intro he
    have heq := Subgroup.eq_of_le_of_card_ge hinc (Nat.le_of_eq he.symm)
    apply hnV
    have hvb : V ≤ B ⊓ NM := le_inf le_sup_right hVN
    exact hvb.trans (heq ▸ inf_le_left)
  have hBN : B ≤ NM := (le_sSup (show B ∈
      {B : Subgroup H | B ∈ thompsonAbelianSubgroups S ∧ k < Nat.card ↥(B ⊓ NM)} from
      ⟨hr,hstrict⟩)).trans hjN
  refine ⟨A,hA.1,hA.2,le_antisymm ?_ (inf_le_inf_left A hNQ)⟩
  exact le_inf inf_le_left (le_sup_left.trans hBN)


end Glauberman

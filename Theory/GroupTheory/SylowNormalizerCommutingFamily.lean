module

public import Theory.GroupTheory.SylowNormalizerFrattini
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.Solvable

/-!
# Sylow normalizers of commuting products

A surjective homomorphism of finite groups maps a Sylow normalizer onto
its image's normalizer. Apply the relative Frattini argument to the inverse
image of the image Sylow; this works for arbitrary kernels.

The normalizer of a Sylow subgroup of a finite direct product embeds in the
product of its coordinate Sylow normalizers. Multiplication from a finite
commuting family is surjective onto its join. Consequently solvability of
all factor Sylow normalizers implies solvability of the whole normalizer,
including central products with nontrivial intersections.

This is the elementary transport implicit in the Borel of L₀ = ⟨L^T⟩ in
Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1144,
proof of 15.3.49(k). No model classification is used here.
-/

public section

open Subgroup

namespace Sylow

/-- Sylow normalizers map onto the actual image normalizers under any surjection. -/
theorem normalizer_map_surjective {G H : Type*} [Group G] [Group H] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (f : G →* H)
    (hf : Function.Surjective f) :
    (normalizer (P : Set G)).map f = normalizer (P.map f : Set H) := by
  apply le_antisymm ((P : Subgroup G).le_normalizer_map f)
  let C := (P.map f).comap f
  let W := (normalizer (P.map f : Set H)).comap f
  have hPC : (P : Subgroup G) ≤ C := le_comap_map f P
  have hCW : C ≤ W := comap_mono (P.map f).le_normalizer
  have hWC : W ≤ normalizer (C : Set G) := by
    exact (comap_normalizer_eq_of_surjective (P.map f) hf).le
  have hfr := le_normalizer_sylow_sup C W hCW hWC (P.subtype hPC)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPC] at hfr
  have hm : W.map f ≤ (normalizer (P : Set G)).map f := by
    apply (map_mono hfr).trans
    rw [Subgroup.map_sup]
    apply sup_le le_rfl
    change ((P.map f).comap f).map f ≤ _
    rw [map_comap_eq_self_of_surjective hf]
    exact map_mono P.le_normalizer
  simpa only [W, map_comap_eq_self_of_surjective hf, Sylow.coe_coe] using hm

end Sylow

namespace Group

/-- A finite product of solvable groups is solvable; their derived lengths may differ. -/
theorem isSolvable_finite_pi {ι : Type*} [Finite ι]
    (K : ι → Type*) [∀ i, Group (K i)] [∀ i, IsSolvable (K i)] :
    IsSolvable (∀ i, K i) := by
  classical
  let _ := Fintype.ofFinite ι
  choose n hn using fun i => (inferInstance : IsSolvable (K i)).solvable
  refine ⟨⟨∑ i, n i, le_bot_iff.mp ?_⟩⟩
  intro x hx
  change x = 1
  funext i
  have hle : derivedSeries (K i) (∑ j, n j) ≤ derivedSeries (K i) (n i) :=
    derivedSeries_antitone (K i) (Finset.single_le_sum (fun j _ => Nat.zero_le (n j))
      (Finset.mem_univ i))
  have hm := map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom K i) (∑ j, n j)
  have hi := hle (hm (mem_map_of_mem _ hx))
  simpa only [hn i, mem_bot, Pi.evalMonoidHom_apply, Pi.one_apply] using hi

end Group

namespace Sylow

/-- Solvability of all Sylow normalizers passes to a homomorphic image. -/
theorem isSolvable_normalizer_of_surjective
    {G H : Type*} [Group G] [Group H] [Finite G]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hG : ∀ P : Sylow p G, Group.IsSolvable (normalizer (P : Set G)))
    (Q : Sylow p H) : Group.IsSolvable (normalizer (Q : Set H)) := by
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hf p Q
  let _ := hG P
  have h := normalizer_map_surjective P f hf
  change Group.IsSolvable (normalizer (P.map f : Set H))
  rw [← h]
  exact Group.isSolvable_of_surjective (f.subgroupMap_surjective _)

/-- Coordinate projections embed the product Sylow normalizer into solvable normalizers. -/
theorem isSolvable_normalizer_pi
    {ι : Type*} [Finite ι] (K : ι → Type*)
    [∀ i, Group (K i)] [∀ i, Finite (K i)]
    {p : ℕ} [Fact p.Prime]
    (hK : ∀ i, ∀ P : Sylow p (K i), Group.IsSolvable (normalizer (P : Set (K i))))
    (P : Sylow p (∀ i, K i)) :
    Group.IsSolvable (normalizer (P : Set (∀ i, K i))) := by
  let Q (i : ι) : Sylow p (K i) :=
    P.mapSurjective (f := Pi.evalMonoidHom K i) (Function.surjective_eval i)
  let N (i : ι) := normalizer (Q i : Set (K i))
  let _ (i : ι) : Group.IsSolvable (N i) := hK i (Q i)
  let _ : Group.IsSolvable (∀ i, N i) :=
    Group.isSolvable_finite_pi (fun i => ↥(N i))
  let f (i : ι) : normalizer (P : Set (∀ i, K i)) →* N i :=
    ((Pi.evalMonoidHom K i).comp (normalizer (P : Set (∀ i, K i))).subtype).codRestrict
      (N i) (fun x => (P : Subgroup (∀ i, K i)).le_normalizer_map
        (Pi.evalMonoidHom K i) (mem_map_of_mem _ x.property))
  apply Group.isSolvable_of_isSolvable_injective (f := MonoidHom.pi f)
  intro x y h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

/-- Every factor is retained when transporting Sylow-normalizer solvability to a commuting join. -/
theorem isSolvable_normalizer_of_commuting_family
    {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι]
    (C : ι → Subgroup G)
    (hcomm : Pairwise fun i j => C i ≤ centralizer (C j : Set G))
    (hgen : iSup C = ⊤) {p : ℕ} [Fact p.Prime]
    (hC : ∀ i, ∀ P : Sylow p (C i), Group.IsSolvable (normalizer (P : Set (C i))))
    (P : Sylow p G) : Group.IsSolvable (normalizer (P : Set G)) := by
  have hc : Pairwise fun i j => ∀ x y : G, x ∈ C i → y ∈ C j → Commute x y := by
    intro i j hij x y hx hy
    exact (hcomm hij hx y hy).symm
  let f : (∀ i, C i) →* G := noncommPiCoprod hc
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp
    (noncommPiCoprod_range.trans hgen)
  exact isSolvable_normalizer_of_surjective f hf
    (isSolvable_normalizer_pi (fun i => C i) hC) P

end Sylow

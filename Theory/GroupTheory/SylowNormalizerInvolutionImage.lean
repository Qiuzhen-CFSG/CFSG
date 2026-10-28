module

public import Theory.GroupTheory.InvolutionCentralizerControl
public import Mathlib.GroupTheory.Sylow

/-!
# Normalizers with involution image and Sylow restrictions

When a subgroup maps onto an involution line, its normalizer maps into
the involution centralizer. If the kernel and a subgroup C normalize
the subgroup, and C maps onto the quotient centralizer,
the normalizer is exactly its preimage. A Sylow intersection calculation
in any quotient with prime-group kernel then lifts to the same original
Sylow subgroup, by pulling back the quotient Sylow witness.

Source application: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup

namespace Subgroup
variable {G Q : Type*} [Group G] [Group Q]

theorem normalizer_eq_comap_involution_centralizer
    (f : G →* Q) (D C : Subgroup G) (i : G)
    (hfi : orderOf (f i) = 2)
    (hD : D.map f = zpowers (f i))
    (hker : f.ker ≤ normalizer (D : Set G))
    (hC : C ≤ normalizer (D : Set G))
    (himage : C.map f = centralizer ({f i} : Set Q)) :
    normalizer (D : Set G) = (centralizer ({f i} : Set Q)).comap f := by
  apply le_antisymm
  · intro g hg
    have hn : f g ∈ normalizer (zpowers (f i) : Set Q) := by
      rw [← hD]
      exact le_normalizer_map f (mem_map_of_mem f hg)
    have hc := normalizer_le_centralizer_of_card_two (zpowers (f i))
      (by rw [Nat.card_zpowers,hfi]) hn
    rw [zpowers_eq_closure, centralizer_closure] at hc
    exact hc
  · rw [← himage, comap_map_eq]
    exact sup_le hC hker

theorem exists_sylow_preimage_restriction
    {p : ℕ} [Fact p.Prime] (f : G →* Q) (hf : Function.Surjective f)
    (hk : IsPGroup p f.ker) (T : Sylow p G) (B : Subgroup Q)
    (P : Sylow p B)
    (hP : (P : Subgroup B) = ((T : Subgroup G).map f).subgroupOf B) :
    ∃ S : Sylow p (B.comap f),
      (S : Subgroup (B.comap f)) = (T : Subgroup G).subgroupOf (B.comap f) := by
  let M := B.comap f
  let q : M →* B := (f.domRestrict M).codRestrict B (fun a => a.property)
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨g,hg⟩ := hf b
    exact ⟨⟨g,by change f g ∈ B; rw [hg]; exact b.property⟩,Subtype.ext hg⟩
  have hqker : IsPGroup p q.ker := by
    have he : q.ker = f.ker.subgroupOf M := by
      ext a
      change q a = 1 ↔ f (a : G) = 1
      exact Subtype.ext_iff
    rw [he]
    exact hk.comap_subtype
  let S := P.comapOfKerIsPGroup q hqker (by rw [MonoidHom.range_eq_top_of_surjective q hq]; exact le_top)
  refine ⟨S, ?_⟩
  change (P : Subgroup B).comap q = _
  rw [hP]
  have hkerT : f.ker ≤ (T : Subgroup G) := hk.le_sylow_of_normal T
  have hpre : ((T : Subgroup G).map f).comap f = (T : Subgroup G) :=
    comap_map_eq_self hkerT
  ext a
  exact SetLike.ext_iff.mp hpre (a : G)

end Subgroup

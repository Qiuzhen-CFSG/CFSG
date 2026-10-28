module

public import Theory.GroupTheory.PCoreCentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Extension

/-!
# Characteristic p in images modulo a normal subgroup's centralizer

Let L be normal in a finite group G with G/L a p-group. If a homomorphism's
kernel centralizes L, the image of every characteristic-p subgroup A is
again of characteristic p. First pass to the normal subgroup A ∩ L; the
restricted kernel is central there. Its image has characteristic p by
central-quotient descent, and the quotient of the image of A by this normal
image is a p-group. The normal p-group extension lemma finishes.

In particular this applies to the actual quotient G/C_G(L). It does not
require Z(L) to be a p-group, because the only central kernel used lies
inside the characteristic-p group A ∩ L.

Source application: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.41(2), printed p.1138, with the local input from 15.3.11(7).
-/

public section
open Subgroup

namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G]
  {p : ℕ} [Fact p.Prime]

/-- Descend characteristic p when the kernel centralizes a normal subgroup
with p-group quotient. -/
theorem centralizer_pCore_image_of_ker_le_centralizer
    (f : G →* H) (L : Subgroup G) [L.Normal]
    (hq : IsPGroup p (G ⧸ L)) (hk : f.ker ≤ centralizer (L : Set G))
    (A : Subgroup G) (hA : centralizer (pCore p A : Set A) ≤ pCore p A) :
    centralizer (pCore p (A.map f) : Set (A.map f)) ≤ pCore p (A.map f) := by
  let B := L.subgroupOf A
  let a := f.subgroupMap A
  let N := B.map a
  let : N.Normal := Normal.map inferInstance a (f.subgroupMap_surjective A)
  have hB : centralizer (pCore p B : Set B) ≤ pCore p B :=
    normal_core_selfCentralizing hA B
  have hkB : (a.subgroupMap B).ker ≤ center B := by
    intro x hx
    have hxker : (x : A).val ∈ f.ker :=
      congrArg (fun z : N => ((z : A.map f) : H)) hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (Subtype.ext ((hk hxker) (y : A) y.property))
  have hN : centralizer (pCore p N : Set N) ≤ pCore p N :=
    (a.subgroupMap B).centralizer_pCore_le_of_surjective_centralKernel
      (a.subgroupMap_surjective B) hkB hB
  have hquot : IsPGroup p ((A.map f) ⧸ N) := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨x, rfl⟩ := f.subgroupMap_surjective A z
    obtain ⟨n, hn⟩ := hq ((QuotientGroup.mk' L) (x : G))
    refine ⟨n, ?_⟩
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    have hxL : (x : G) ^ p ^ n ∈ L := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' L ((x : G) ^ p ^ n) = 1
      rw [map_pow]
      exact hn
    exact ⟨x ^ p ^ n, hxL, map_pow a x (p ^ n)⟩
  exact Theory.GroupTheory.centralizer_pCore_le_of_normal_pGroup_quotient N hN hquot
end MonoidHom

namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The image in G/C_G(L) of a characteristic-p subgroup has characteristic p
when L is normal and G/L is a p-group. -/
theorem centralizer_pCore_image_mod_centralizer
    (L : Subgroup G) [L.Normal] (hq : IsPGroup p (G ⧸ L))
    (A : Subgroup G) (hA : centralizer (pCore p A : Set A) ≤ pCore p A) :
    let B := A.map (QuotientGroup.mk' (centralizer (L : Set G)))
    centralizer (pCore p B : Set B) ≤ pCore p B := by
  apply (QuotientGroup.mk' (centralizer (L : Set G))).centralizer_pCore_image_of_ker_le_centralizer
    L hq _ A hA
  rw [QuotientGroup.ker_mk']
end Subgroup

end

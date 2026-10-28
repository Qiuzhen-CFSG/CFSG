module

public import FeitThompson.BGsection1.CentralizerLemmas

/-!
# Normalizers in a coprime normal supplement

Let a finite group G factor as NH, where N is normal and has order prime
to p. For every p-subgroup P of H, its normalizer factors as
`N_G(P) = (N ∩ N_G(P))(H ∩ N_G(P))`. The statement records the join;
the first factor is normal inside the normalizer, so this join is the
displayed ordered product. P need not be a Sylow subgroup of H.

The quotient-normalizer theorem for a normal p′-subgroup extends to any
surjection with p′-kernel by the first isomorphism theorem. Apply it to
`H → G/N`, which is surjective because G=NH. The quotient image of each
normalizing element g then lifts to an element h of H that normalizes P.
The remaining factor `g*h⁻¹` belongs to both N and the normalizer.

This is Kurzweil–Stellmacher, *The Theory of Finite Groups*, 3.2.9
(printed p. 67), used by the relative signalizer factorization in 11.2.6
(printed p. 321). The existing quotient-normalizer result is the proved
Lemma 1.14 in `FeitThompson.BGsection1.CentralizerLemmas`; this source
adapter therefore remains above Theory.
-/

namespace Glauberman

private theorem normalizer_map_of_coprime_kernel
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (P : Subgroup G) (hP : IsPGroup p P) (hcop : Nat.Coprime p (Nat.card f.ker)) :
    Subgroup.normalizer (P.map f : Set H) = (Subgroup.normalizer (P : Set G)).map f := by
  let q : G →* G ⧸ f.ker := QuotientGroup.mk' f.ker
  let e : G ⧸ f.ker ≃* H := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hcomp : e.toMonoidHom.comp q = f := by ext; rfl
  let : Fact (IsPGroup p P) := ⟨hP⟩
  calc
    Subgroup.normalizer (P.map f : Set H) =
        Subgroup.normalizer ((P.map q).map e.toMonoidHom : Set H) := by
      rw [Subgroup.map_map, hcomp]
    _ = (Subgroup.normalizer (P.map q : Set (G ⧸ f.ker))).map e.toMonoidHom :=
      (Subgroup.map_normalizer_eq_of_bijective (P.map q) e.bijective).symm
    _ = ((Subgroup.normalizer (P : Set G)).map q).map e.toMonoidHom := by
      rw [normalizer_map_quotient_eq_map_normalizer p P f.ker inferInstance hcop]
    _ = (Subgroup.normalizer (P : Set G)).map f := by rw [Subgroup.map_map, hcomp]

/-- A normal p′-supplement factors the normalizer of any p-subgroup of the
other factor; the first intersection is normal in that normalizer. -/
public theorem normalizer_eq_inf_sup_inf_of_coprime_normal_supplement
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N H P : Subgroup G) [N.Normal] (hcop : Nat.Coprime p (Nat.card N))
    (hsup : N ⊔ H = ⊤) (hP : IsPGroup p P) (hPH : P ≤ H) :
    Subgroup.normalizer (P : Set G) =
      (N ⊓ Subgroup.normalizer (P : Set G)) ⊔
        (H ⊓ Subgroup.normalizer (P : Set G)) := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let f : H →* G ⧸ N := q.comp H.subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hg : g ∈ N ⊔ H := by rw [hsup]; trivial
    obtain ⟨n, hn, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    refine ⟨⟨h, hh⟩, ?_⟩
    change q h = q (n * h)
    rw [map_mul, show q n = 1 from (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  let fk : f.ker →* N :=
    (H.subtype.comp f.ker.subtype).codRestrict N (fun x => by
      apply (QuotientGroup.eq_one_iff (x : H).val).mp
      exact x.property)
  have hfk : Function.Injective fk := by
    intro x y h
    have hv : ((x : H) : G) = ((y : H) : G) := congrArg (fun z : N => (z : G)) h
    exact Subtype.ext (Subtype.ext hv)
  have hcopker : Nat.Coprime p (Nat.card f.ker) :=
    hcop.of_dvd_right (Subgroup.card_dvd_of_injective fk hfk)
  have hPHp : IsPGroup p (P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hmapP : (P.subgroupOf H).map f = P.map q := by
    change (P.subgroupOf H).map (q.comp H.subtype) = P.map q
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hPH]
  have hmapN := normalizer_map_of_coprime_kernel f hf (P.subgroupOf H) hPHp hcopker
  rw [hmapP] at hmapN
  apply le_antisymm
  · intro g hg
    have hqg : q g ∈ Subgroup.normalizer (P.map q : Set (G ⧸ N)) :=
      P.le_normalizer_map q (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
    rw [hmapN] at hqg
    obtain ⟨h, hh, heq⟩ := hqg
    have hhN : (h : G) ∈ Subgroup.normalizer (P : Set G) := by
      have h' : h ∈ (Subgroup.normalizer (P : Set G)).subgroupOf H := by
        rw [Subgroup.subgroupOf_normalizer_eq hPH]
        exact hh
      exact h'
    let n : G := g * (h : G)⁻¹
    have hn : n ∈ N := by
      apply (QuotientGroup.eq_one_iff n).mp
      change q (g * (h : G)⁻¹) = 1
      rw [map_mul, map_inv]
      change q g * (f h)⁻¹ = 1
      rw [heq, mul_inv_cancel]
    have hnN : n ∈ Subgroup.normalizer (P : Set G) :=
      (Subgroup.normalizer (P : Set G)).mul_mem hg
        ((Subgroup.normalizer (P : Set G)).inv_mem hhN)
    have hmem : n * (h : G) ∈
        (N ⊓ Subgroup.normalizer (P : Set G)) ⊔ (H ⊓ Subgroup.normalizer (P : Set G)) :=
      Subgroup.mul_mem_sup ⟨hn, hnN⟩ ⟨h.property, hhN⟩
    simpa [n] using hmem
  · exact sup_le inf_le_right inf_le_right

end Glauberman

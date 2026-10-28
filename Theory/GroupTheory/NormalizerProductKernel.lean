module
public import Theory.PGroupCore
public import Mathlib.Data.SetLike.Fintype

/-!
# Maximal normal kernels for a product of two overgroups

For subgroups U and V containing a Sylow subgroup P, choose a normal kernel S
maximal with SP = (SP ∩ U)(SP ∩ V). The quotient has trivial p-core. Neither
factor covers a nontrivial normal subgroup of G/S: such coverage would enlarge
S while preserving the product. The original p-core is contained in S.

These are the initial maximal-kernel deductions in GLS, Number 2,
G.26.18(a), printed pp.152–153. No factorization theorem or induction
hypothesis is assumed in constructing the kernel.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The literal ordered product on the subgroup SP. -/
@[expose] def NormalizerProductOn (P U V S : Subgroup G) : Prop :=
  ((S ⊔ P : Subgroup G) : Set G) =
    (((S ⊔ P) ⊓ U : Subgroup G) : Set G) *
    (((S ⊔ P) ⊓ V : Subgroup G) : Set G)

/-- Maximality among normal kernels with the displayed product property. -/
structure IsMaximalProductKernel (P U V S : Subgroup G) : Prop where
  normal : S.Normal
  factorization : NormalizerProductOn P U V S
  maximal : ∀ D : Subgroup G, D.Normal → NormalizerProductOn P U V D → S ≤ D → D ≤ S

theorem normalizerProductOn_of_le (P U V S : Subgroup G)
    (hPU : P ≤ U) (hPV : P ≤ V) (hSP : S ≤ P) : NormalizerProductOn P U V S := by
  change ((S ⊔ P : Subgroup G) : Set G) = _
  rw [sup_of_le_right hSP,inf_of_le_left hPU,inf_of_le_left hPV]
  simpa only [sup_idem] using coe_mul_of_left_le_normalizer_right P P P.le_normalizer

theorem exists_maximalProductKernel [Finite G] (P U V : Subgroup G)
    (hPU : P ≤ U) (hPV : P ≤ V) : ∃ S : Subgroup G, IsMaximalProductKernel P U V S := by
  classical
  let candidates : Set (Subgroup G) := {S | S.Normal ∧ NormalizerProductOn P U V S}
  obtain ⟨S,hS,hmax⟩ := candidates.toFinite.exists_maximal
    ⟨⊥,inferInstance,normalizerProductOn_of_le P U V ⊥ hPU hPV bot_le⟩
  exact ⟨S,hS.1,hS.2,fun D hn hf hSD => hmax ⟨hn,hf⟩ hSD⟩

theorem IsMaximalProductKernel.pCore_quotient_eq_bot [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (U V S : Subgroup G)
    (h : IsMaximalProductKernel (P : Subgroup G) U V S) :
    let := h.normal
    pCore p (G ⧸ S) = ⊥ := by
  let := h.normal
  let q := QuotientGroup.mk' S
  let D := (pCore p (G ⧸ S)).comap q
  have hSD : S ≤ D := by
    intro s hs
    change q s ∈ pCore p (G ⧸ S)
    rw [show q s = 1 from (QuotientGroup.eq_one_iff s).mpr hs]
    exact one_mem _
  have hDS : D ≤ S ⊔ (P : Subgroup G) := by
    have hh := pCore_isPGroup.le_sylow_of_normal (P.mapSurjective (QuotientGroup.mk'_surjective S))
    have hm := comap_mono (f := q) hh
    simpa only [D,q,Sylow.coe_mapSurjective,comap_map_eq,QuotientGroup.ker_mk',sup_comm] using hm
  have he : D ⊔ (P : Subgroup G) = S ⊔ (P : Subgroup G) :=
    le_antisymm (sup_le hDS le_sup_right) (sup_le_sup_right hSD _)
  have hf : NormalizerProductOn (P : Subgroup G) U V D := by
    unfold NormalizerProductOn
    rw [he]
    exact h.factorization
  have hD : D ≤ S := h.maximal D inferInstance hf hSD
  have hm := map_mono (f := q) hD
  apply bot_unique
  simpa only [D,q,map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S),
    QuotientGroup.map_mk'_self] using hm

/-- Enlarge the kernel when the first factor covers its new section. -/
theorem NormalizerProductOn.extend_left (P U V S D : Subgroup G) [S.Normal]
    (h : NormalizerProductOn P U V S) (hPU : P ≤ U)
    (hSD : S ≤ D) (hDU : D ≤ U ⊔ S) : NormalizerProductOn P U V D := by
  apply Set.Subset.antisymm
  · intro x hx
    have hh : x ∈ U ⊔ S := (sup_le hDU (hPU.trans le_sup_left)) hx
    obtain ⟨u,hu,s,hs,hxus⟩ := mem_sup_of_normal_right.mp hh
    have hsD : s ∈ D ⊔ P := Subgroup.mem_sup_left (hSD hs)
    have huD : u ∈ D ⊔ P := by
      have he : u = x * s⁻¹ := eq_mul_inv_iff_mul_eq.mpr hxus
      rw [he]
      exact (D ⊔ P).mul_mem hx ((D ⊔ P).inv_mem hsD)
    have hsSP : s ∈ S ⊔ P := Subgroup.mem_sup_left hs
    change s ∈ ((S ⊔ P : Subgroup G) : Set G) at hsSP
    rw [h] at hsSP
    obtain ⟨a,ha,b,hb,hab⟩ := hsSP
    refine ⟨u*a,⟨(D ⊔ P).mul_mem huD ((sup_le_sup_right hSD P) ha.1),
      U.mul_mem hu ha.2⟩,b,⟨(sup_le_sup_right hSD P) hb.1,hb.2⟩,?_⟩
    change (u*a)*b = x
    change a*b = s at hab
    rw [mul_assoc,hab,hxus]
  · rintro x ⟨a,ha,b,hb,rfl⟩
    exact (D ⊔ P).mul_mem ha.1 hb.1

/-- A product of subgroups which is itself a subgroup also factors in reverse order. -/
theorem NormalizerProductOn.symm (P U V S : Subgroup G)
    (h : NormalizerProductOn P U V S) : NormalizerProductOn P V U S := by
  apply Set.Subset.antisymm
  · intro x hx
    have hi : x⁻¹ ∈ S ⊔ P := (S ⊔ P).inv_mem hx
    change x⁻¹ ∈ ((S ⊔ P : Subgroup G) : Set G) at hi
    rw [h] at hi
    obtain ⟨a,ha,b,hb,hab⟩ := hi
    exact ⟨b⁻¹,((S ⊔ P) ⊓ V).inv_mem hb,a⁻¹,((S ⊔ P) ⊓ U).inv_mem ha,
      by simpa only [mul_inv_rev,inv_inv] using congrArg Inv.inv hab⟩
  · rintro x ⟨a,ha,b,hb,rfl⟩
    exact (S ⊔ P).mul_mem ha.1 hb.1

theorem IsMaximalProductKernel.symm (P U V S : Subgroup G)
    (h : IsMaximalProductKernel P U V S) : IsMaximalProductKernel P V U S :=
  ⟨h.normal,h.factorization.symm P U V S,
    fun D hn hf hSD => h.maximal D hn (hf.symm P V U D) hSD⟩

/-- Neither factor covers any nontrivial normal section above the maximal kernel. -/
theorem IsMaximalProductKernel.not_covering_left (P U V S : Subgroup G)
    (h : IsMaximalProductKernel P U V S) (hPU : P ≤ U)
    [S.Normal] (Y : Subgroup (G ⧸ S)) [Y.Normal] (hne : Y ≠ ⊥) :
    ¬ Y ≤ U.map (QuotientGroup.mk' S) := by
  let := h.normal
  intro hc
  let q := QuotientGroup.mk' S
  let D := Y.comap q
  have hSD : S ≤ D := by
    intro s hs
    change q s ∈ Y
    rw [show q s = 1 from (QuotientGroup.eq_one_iff s).mpr hs]
    exact Y.one_mem
  have hDU : D ≤ U ⊔ S := by
    have hh := comap_mono (f := q) hc
    simpa only [q,comap_map_eq,QuotientGroup.ker_mk'] using hh
  have hf : NormalizerProductOn P U V D :=
    h.factorization.extend_left P U V S D hPU hSD hDU
  have he : D = S := le_antisymm (h.maximal D inferInstance hf hSD) hSD
  apply hne
  have hh := congrArg (map q) he
  simpa only [D,q,map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S),
    QuotientGroup.map_mk'_self] using hh

theorem IsMaximalProductKernel.not_covering_right (P U V S : Subgroup G)
    (h : IsMaximalProductKernel P U V S) (hPV : P ≤ V)
    [S.Normal] (Y : Subgroup (G ⧸ S)) [Y.Normal] (hne : Y ≠ ⊥) :
    ¬ Y ≤ V.map (QuotientGroup.mk' S) :=
  (h.symm P U V S).not_covering_left P V U S hPV Y hne

/-- The original prime core is absorbed by every maximal kernel. -/
theorem IsMaximalProductKernel.pCore_le [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (U V S : Subgroup G)
    (h : IsMaximalProductKernel (P : Subgroup G) U V S) : pCore p G ≤ S := by
  let := h.normal
  let D := S ⊔ pCore p G
  have he : D ⊔ (P : Subgroup G) = S ⊔ (P : Subgroup G) := by
    dsimp [D]
    rw [sup_assoc,sup_of_le_right (pCore_isPGroup.le_sylow_of_normal P)]
  have hf : NormalizerProductOn (P : Subgroup G) U V D := by
    unfold NormalizerProductOn
    rw [he]
    exact h.factorization
  exact le_sup_right.trans (h.maximal D inferInstance hf le_sup_left)

theorem IsMaximalProductKernel.ne_top (P U V S : Subgroup G)
    (h : IsMaximalProductKernel P U V S)
    (hfail : ¬ NormalizerProductOn P U V ⊤) : S ≠ ⊤ := by
  intro he
  exact hfail (he ▸ h.factorization)
end Theory.GroupTheory

module

public import Theory.PPrimeCore
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The prime-complement core of a centric radical normalizer

Let D be a normal p-subgroup, with a centric Sylow intersection. The Sylow
intersection with C_G(D) is central there, so Burnside transfer puts that
centralizer inside O_{p'}(G) D. The p'-core commutes with D by coprime
normality. If the p-core of the actual action image is inner, map the p-core
of G/O_{p'}(G) to that image. Its inverse image is exactly O_{p'}(G) D.

This proves the structural comparison needed to pass from the relative
radical fusion family to the literal Alperin–Goldschmidt family. The core
is genuinely the inverse image from the quotient by the p'-core.
Source: Huppert X.4.12; Aschbacher–Smith, combined 1 March 2004 manuscript,
Definition 2.2.1, p. 518.
-/

@[expose] public section

open Subgroup

namespace AlperinGoldschmidt
variable {G A : Type*} [Group G] [Finite G] [Group A]
variable {p : ℕ} [Fact p.Prime]

def primeCorePreimage (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  (pCore p (G ⧸ pPrimeCore p G)).comap (QuotientGroup.mk' (pPrimeCore p G))

theorem normal_p_centralizer_le (P : Sylow p G) (D : Subgroup G) [D.Normal]
    (hcent : (P : Subgroup G) ⊓ centralizer (D : Set G) ≤ D) :
    centralizer (D : Set G) ≤ pPrimeCore p G ⊔ D := by
  let C := centralizer (D : Set G)
  let : C.Normal := normal_centralizer
  obtain ⟨S, hS⟩ := P.exists_subgroupOf_eq_of_normal C
  have hSC : normalizer (S : Set C) ≤ centralizer (S : Set C) := by
    intro c _
    rw [mem_centralizer_iff]
    intro s hs
    apply Subtype.ext
    have hsP : (s : G) ∈ (P : Subgroup G) := by
      change s ∈ (P : Subgroup G).subgroupOf C
      rwa [← hS]
    exact mem_centralizer_iff.mp c.property s (hcent ⟨hsP, s.property⟩)
  let f := MonoidHom.transferSylow S hSC
  have hk : f.ker ≤ pPrimeCore p C := le_sSup ⟨inferInstance,
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (MonoidHom.not_dvd_card_ker_transferSylow S hSC)⟩
  have hcore : (pPrimeCore p C).map C.subtype ≤ pPrimeCore p G :=
    le_sSup ⟨inferInstance, Nat.Coprime.of_dvd_right
      (card_map_dvd _ C.subtype) pPrimeCore_coprime_card⟩
  intro c hc
  have hgen := (MonoidHom.ker_transferSylow_isComplement' S hSC).sup_eq_top
  have hmem : (⟨c, hc⟩ : C) ∈ f.ker ⊔ (S : Subgroup C) := by rw [hgen]; trivial
  obtain ⟨k, hk', s, hs, hks⟩ := mem_sup_of_normal_left.mp hmem
  have hkG : (k : G) ∈ pPrimeCore p G := hcore (mem_map_of_mem C.subtype (hk hk'))
  have hsG : (s : G) ∈ D := by
    apply hcent
    refine ⟨?_, s.property⟩
    change s ∈ (P : Subgroup G).subgroupOf C
    rwa [← hS]
  have he := congrArg Subtype.val hks
  change (k : G) * (s : G) = c at he
  rw [← he]
  exact (pPrimeCore p G ⊔ D).mul_mem (mem_sup_left hkG) (mem_sup_right hsG)

theorem primeCore_product (P : Sylow p G) (D : Subgroup G) [D.Normal]
    (hD : IsPGroup p D)
    (hcent : (P : Subgroup G) ⊓ centralizer (D : Set G) ≤ D)
    (f : G →* A) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (D : Set G))
    (hrad : pCore p A ≤ D.map f) :
    centralizer (D : Set G) ≤ primeCorePreimage p G ∧
    primeCorePreimage p G = pPrimeCore p G ⊔ D ∧
    Disjoint (pPrimeCore p G) D ∧
    (∀ o ∈ pPrimeCore p G, ∀ d ∈ D, Commute o d) := by
  have hcop : Nat.Coprime (Nat.card (pPrimeCore p G)) (Nat.card D) := by
    obtain ⟨n, hn⟩ := hD.exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := p)).symm.pow_right n
  have hdisj := disjoint_of_coprime_natCard hcop
  have hOC : pPrimeCore p G ≤ centralizer (D : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hdisj)
  have hCD := normal_p_centralizer_le P D hcent
  let O := pPrimeCore p G
  let q := QuotientGroup.mk' O
  let fbar : G ⧸ O →* A := QuotientGroup.lift O f (by simpa only [hker] using hOC)
  have hfbar : Function.Surjective fbar := by
    intro a
    obtain ⟨g, rfl⟩ := hf a
    exact ⟨q g, rfl⟩
  have himage : (pCore p (G ⧸ O)).map fbar ≤ pCore p A :=
    le_sSup ⟨Subgroup.Normal.map inferInstance fbar hfbar, pCore_isPGroup.map fbar⟩
  have hpre : primeCorePreimage p G ≤ O ⊔ D := by
    intro g hg
    have hfg : f g ∈ D.map f := hrad (himage (mem_map.mpr ⟨q g, hg, rfl⟩))
    obtain ⟨d, hd, he⟩ := hfg
    have hgc : g * d⁻¹ ∈ centralizer (D : Set G) := by
      rw [← hker]
      simp [MonoidHom.mem_ker, ← he]
    have hh := (O ⊔ D).mul_mem (hCD hgc) (mem_sup_right hd)
    simpa only [inv_mul_cancel_right] using hh
  have hback : O ⊔ D ≤ primeCorePreimage p G := by
    apply sup_le
    · intro o ho
      change q o ∈ pCore p (G ⧸ O)
      have he : q o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
      rw [he]
      exact one_mem _
    · have hDq : D.map q ≤ pCore p (G ⧸ O) :=
        le_sSup ⟨Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective O), hD.map q⟩
      intro d hd
      exact hDq (mem_map_of_mem q hd)
  have heq := le_antisymm hpre hback
  refine ⟨hCD.trans hback, heq, hdisj, ?_⟩
  intro o ho d hd
  exact (mem_centralizer_iff.mp (hOC ho) d hd).symm
end AlperinGoldschmidt

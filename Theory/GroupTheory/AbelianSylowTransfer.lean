module
public import Mathlib.GroupTheory.Transfer
public import Theory.GroupTheory.ConjugateSpanNormalClosure
public import Mathlib.GroupTheory.Commutator.Basic
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Transfer across a central supplement to an abelian Sylow subgroup

A homomorphism from an abelian Sylow subgroup that is invariant under its
normalizer is evaluated by transfer as the index power. Burnside fusion
reduces conjugation of each orbit factor to conjugation in the normalizer.
If a normal generating subgroup has a central supplement in that Sylow
and is preserved by its normalizer, transfer to the Sylow quotient kills
the whole group and forces the supplement into the generating subgroup.
The final result applies the same argument modulo a common normal subgroup.

This is the central-extension step used in DGS, Groups and Graphs (1985),
6.4, printed p.121, using the transfer construction from Mathlib.
-/

open Subgroup
open scoped IsMulCommutative
public noncomputable section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Normalizer-invariant transfer on an abelian Sylow is the index power. -/
theorem transfer_eq_pow_of_normalizer_invariant
    (P : Sylow p G) [IsMulCommutative P]
    {A : Type*} [CommGroup A] (f : P →* A)
    (hf : ∀ (n : G) (hn : n ∈ normalizer (P : Set G)) (x : P),
      f ((P : Subgroup G).normalizerMonoidHom ⟨n,hn⟩ x) = f x)
    (x : P) : MonoidHom.transfer f (x : G) = f x ^ P.index := by
  classical
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient (zpowers (x : G)) (G ⧸ (P : Subgroup G)))
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  have hterm (k : ℕ) (g : G) (h : g⁻¹ * (x : G)^k * g ∈ P) :
      f ⟨g⁻¹ * (x : G)^k * g,h⟩ = f x ^ k := by
    obtain ⟨n,hn,he⟩ := P.conj_eq_normalizer_conj_of_mem ((x : G)^k) g
      (P.pow_mem x.property k) h
    have hh := hf n⁻¹ ((normalizer (P : Set G)).inv_mem hn) (x^k)
    calc
      f ⟨g⁻¹ * (x : G)^k * g,h⟩ =
          f ((P : Subgroup G).normalizerMonoidHom
            ⟨n⁻¹,(normalizer (P : Set G)).inv_mem hn⟩ (x^k)) := by
        congr 1
        apply Subtype.ext
        change g⁻¹ * (x : G)^k * g = n⁻¹ * ((x^k : P) : G) * n⁻¹⁻¹
        simpa only [inv_inv, SubgroupClass.coe_pow] using he
      _ = f x ^ k := hh.trans (map_pow f x k)
  simp_rw [hterm]
  rw [Finset.prod_pow_eq_pow_sum, ← Subgroup.index_eq_sum_minimalPeriod (P : Subgroup G) (x : G)]

/-- A normal generating subgroup with a central Sylow supplement is the full Sylow. -/
theorem sylow_eq_of_normal_generation_central_supplement
    (P : Sylow p G) [IsMulCommutative P]
    (A C : Subgroup G) (hAP : A ≤ P) (hCP : C ≤ P)
    (hC : C ≤ center G) (hs : A ⊔ C = P)
    (hn : normalizer (P : Set G) ≤ normalizer (A : Set G))
    (hg : normalClosure (A : Set G) = ⊤) : A = P := by
  let : C.Normal := normalizer_eq_top_iff.mp (top_unique (by
    intro x _
    exact (centralizer_le_normalizer _ (fun c hc => (mem_center_iff.mp (hC hc) x).symm))))
  let D := A.subgroupOf (P : Subgroup G)
  let f := QuotientGroup.mk' D
  have hf : ∀ (n : G) (hn' : n ∈ normalizer (P : Set G)) (x : P),
      f ((P : Subgroup G).normalizerMonoidHom ⟨n,hn'⟩ x) = f x := by
    intro n hn' x
    have hx : (x : G) ∈ A ⊔ C := hs.symm ▸ x.property
    rw [show (A ⊔ C : Subgroup G) = C ⊔ A from sup_comm _ _,
      mem_sup_of_normal_left] at hx
    obtain ⟨c,hc,a,ha,hca⟩ := hx
    have hac : a*c = x := (mem_center_iff.mp (hC hc) a).trans hca
    have hna : n*a*n⁻¹ ∈ A := (mem_normalizer_iff.mp (hn hn') a).mp ha
    have hnc : n*c*n⁻¹ = c := by
      rw [(mem_center_iff.mp (hC hc) n),mul_inv_cancel_right]
    have he : ((P : Subgroup G).normalizerMonoidHom ⟨n,hn'⟩ x) =
        (⟨n*a*n⁻¹,hAP hna⟩ : P) * ⟨c,hCP hc⟩ := by
      apply Subtype.ext
      change n*x*n⁻¹ = (n*a*n⁻¹)*c
      rw [←hac]
      calc
        n*(a*c)*n⁻¹ = (n*a*n⁻¹)*(n*c*n⁻¹) := by group
        _ = _ := by rw [hnc]
    have hex : x = (⟨a,hAP ha⟩ : P) * ⟨c,hCP hc⟩ := Subtype.ext hac.symm
    rw [he,hex,map_mul,map_mul]
    have ha0 : f ⟨a,hAP ha⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    have hna0 : f ⟨n*a*n⁻¹,hAP hna⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hna
    rw [ha0,hna0]
  let t := MonoidHom.transfer f
  have hAt : A ≤ t.ker := by
    intro a ha
    change t a = 1
    rw [show t a = f ⟨a,hAP ha⟩ ^ P.index from
      transfer_eq_pow_of_normalizer_invariant P f hf ⟨a,hAP ha⟩]
    rw [show f ⟨a,hAP ha⟩ = 1 from (QuotientGroup.eq_one_iff _).mpr ha,one_pow]
  have ht : t.ker = ⊤ := top_unique (hg ▸ normalClosure_le_normal hAt)
  have hD : D = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y,hy⟩ := (P.isPGroup'.powEquiv' P.not_dvd_index).surjective x
    have hh : t (y : G) = 1 := show y.val ∈ t.ker from ht ▸ mem_top _
    rw [show t (y : G) = f y ^ P.index from
      transfer_eq_pow_of_normalizer_invariant P f hf y,←map_pow] at hh
    change y ^ P.index = x at hy
    rw [hy] at hh
    exact (QuotientGroup.eq_one_iff _).mp hh
  have hm := congrArg (map (P : Subgroup G).subtype) hD
  rwa [map_subgroupOf_eq_of_le hAP,←MonoidHom.range_eq_map,range_subtype] at hm

open scoped commutatorElement in
/-- The same conclusion modulo the indicated common normal subgroup. -/
theorem sylow_eq_of_normal_generation_mod_central
    (P : Sylow p G) (A N D : Subgroup G) [D.Normal]
    (hDA : D ≤ A) (hAP : A ≤ P) (hNP : N ≤ P)
    (hs : A ⊔ N = P) (hAA : ⁅A,A⁆ ≤ D) (hN : ⁅N,⊤⁆ ≤ D)
    (hn : normalizer (P : Set G) ≤ normalizer (A : Set G))
    (hg : normalClosure (A : Set G) = ⊤) : A = P := by
  let q := QuotientGroup.mk' D
  let R := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective D)
  have hNc : N.map q ≤ center (G ⧸ D) := by
    rintro _ ⟨n,hnN,rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective D y
    symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅q n,q x⁆ = 1
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hN (commutator_mem_commutator hnN (show x ∈ (⊤ : Subgroup G) from mem_top x)))
  have hAc : A.map q ≤ centralizer (A.map q : Set (G ⧸ D)) := by
    rw [←commutator_eq_bot_iff_le_centralizer,←map_commutator]
    exact (map_eq_bot_iff _).mpr (hAA.trans_eq (QuotientGroup.ker_mk' D).symm)
  have hR : (R : Subgroup (G ⧸ D)) = A.map q ⊔ N.map q := by
    change (P : Subgroup G).map q = _
    rw [←hs,Subgroup.map_sup]
  have hRn : (R : Subgroup (G ⧸ D)) ≤ centralizer (R : Set (G ⧸ D)) := by
    change (R : Subgroup (G ⧸ D)) ≤ centralizer ((R : Subgroup (G ⧸ D)) : Set (G ⧸ D))
    rw [hR]
    apply le_centralizer_iff.mpr
    apply sup_le
    · apply le_centralizer_iff.mpr
      apply sup_le hAc
      exact hNc.trans (center_le_centralizer _)
    · exact (center_le_centralizer _).trans' hNc
  let : IsMulCommutative R := le_centralizer_iff_isMulCommutative.mp hRn
  have hn' : normalizer (R : Set (G ⧸ D)) ≤ normalizer (A.map q : Set (G ⧸ D)) := by
    change normalizer ((P : Subgroup G).map q : Set (G ⧸ D)) ≤ _
    rw [←P.normalizer_map_surjective q (QuotientGroup.mk'_surjective D)]
    exact (map_mono hn).trans (A.le_normalizer_map q)
  have hg' : normalClosure (A.map q : Set (G ⧸ D)) = ⊤ := by
    rw [coe_map,←map_normalClosure _ q (QuotientGroup.mk'_surjective D),hg,
      map_top_of_surjective q (QuotientGroup.mk'_surjective D)]
  have he := sylow_eq_of_normal_generation_central_supplement R (A.map q) (N.map q)
    (map_mono hAP) (map_mono hNP) hNc hR.symm hn' hg'
  have hh := congrArg (Subgroup.comap q) he
  change (A.map q).comap q = ((P : Subgroup G).map q).comap q at hh
  rwa [comap_map_eq_self ((QuotientGroup.ker_mk' D).le.trans hDA),
    comap_map_eq_self ((QuotientGroup.ker_mk' D).le.trans (hDA.trans hAP))] at hh
end Subgroup

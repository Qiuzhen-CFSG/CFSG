module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPointThompson
public import Theory.GroupTheory.InvariantLeviDecomposition
public import Theory.GroupTheory.PResidual.NormalSup
public import Theory.GroupTheory.SylowNormalizedResidual
public import Theory.GroupTheory.SylowLocalCore

/-!
# Residual factors of the paired point centralizer

A central point normalizes each of the two disjoint commuting blocks.
Uniqueness of their product decomposes its centralizer blockwise. The
original Sylow subgroup supplements the residual of this normal product,
so adjoining that Sylow does not change the residual. Relative normality
of the commuting point factors identifies the result with the join of
their literal embedded residuals; disjointness identifies its intersections.

Source: Aschbacher--Smith, proof of 14.6.9, printed pp.1026--1027
(refs/quasithin.pdf).
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_pair_join (K L : Subgroup G) (z : G)
    (hd : Disjoint K L) (hc : L ≤ centralizer (K : Set G))
    (hzK : z ∈ normalizer (K : Set G)) (hzL : z ∈ normalizer (L : Set G)) :
    (K ⊔ L) ⊓ centralizer ({z} : Set G) =
      (K ⊓ centralizer ({z} : Set G)) ⊔ (L ⊓ centralizer ({z} : Set G)) := by
  apply le_antisymm
  · rintro g ⟨hg,hgz⟩
    have hgm : g ∈ (K : Set G) * (L : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left K L
        (hc.trans (Subgroup.centralizer_le_normalizer _))]
      exact hg
    obtain ⟨k,hk,l,hl,rfl⟩ := hgm
    have hfix : (MulAut.conj z) (k*l) = k*l := by
      have hh := mem_centralizer_singleton_iff.mp hgz
      simpa only [MulAut.conj_apply,mul_inv_eq_iff_eq_mul] using hh.symm
    have hf := Subgroup.fixed_factors_of_disjoint (MulAut.conj z).toMonoidHom K L
      hd (fun k hk => (hzK k).mp hk) (fun l hl => (hzL l).mp hl) hk hl hfix
    have hkc : k ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have hh := hf.1
      change z*k*z⁻¹=k at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hlc : l ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have hh := hf.2
      change z*l*z⁻¹=l at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    exact mul_mem_sup ⟨hk,hkc⟩ ⟨hl,hlc⟩
  · exact sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)

omit [Finite G] in
private theorem centralizer_supplement (K R : Subgroup G) (z : G)
    (hn : R ≤ normalizer (K : Set G)) (hz : R ≤ centralizer ({z} : Set G)) :
    (K ⊔ R) ⊓ centralizer ({z} : Set G) =
      (K ⊓ centralizer ({z} : Set G)) ⊔ R := by
  apply le_antisymm
  · rintro g ⟨hg,hgz⟩
    have hgm : g ∈ (K : Set G) * (R : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left K R hn]
      exact hg
    obtain ⟨k,hk,r,hr,rfl⟩ := hgm
    have hkc : k ∈ centralizer ({z} : Set G) := by
      simpa only [mul_inv_cancel_right] using
        (centralizer ({z} : Set G)).mul_mem hgz ((centralizer ({z} : Set G)).inv_mem (hz hr))
    exact mul_mem_sup ⟨hk,hkc⟩ hr
  · exact sup_le (inf_le_inf_right _ le_sup_left) (le_inf le_sup_right hz)

private theorem residual_of_normal_sylow_supplement
    (B N R : Subgroup G) (S : Sylow 2 B) (hS : (S : Subgroup B).map B.subtype = R)
    (hNB : N ≤ B) (hn : B ≤ normalizer (N : Set G)) (hgen : N ⊔ R = B) :
    (pResidual 2 B).map B.subtype = (pResidual 2 N).map N.subtype := by
  let X := (pResidual 2 N).map N.subtype
  have hnormal : (N.subgroupOf B).Normal := normal_subgroupOf_of_le_normalizer hn
  let := hnormal
  have hcov := le_embedded_pResidual_sup_sylow_of_normalizes S (N.subgroupOf B)
    (show (S : Subgroup B) ≤ normalizer (N.subgroupOf B : Set B) from le_normalizer_of_normal)
  have hcov' := map_mono (f := B.subtype) hcov
  rw [Subgroup.map_sup,map_embedded_pResidual,map_subgroupOf_eq_of_le hNB,hS] at hcov'
  have hXB : X ≤ B := (map_subtype_le _).trans hNB
  have hRB : R ≤ B := hS ▸ map_subtype_le (S : Subgroup B)
  have he : X ⊔ R = B := le_antisymm (sup_le hXB hRB)
    (hgen ▸ sup_le hcov' le_sup_right)
  have hRX : R ≤ normalizer (X : Set G) := hRB.trans
    (hn.trans (normalizer_le_normalizer_characteristic_image N (pResidual 2 N)))
  rw [←he]
  exact embedded_pResidual_join_pGroup X R (isPPerfect_embedded_pResidual 2 N)
    (hS ▸ S.isPGroup'.map B.subtype) hRX

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

/-- The literal point-centralizer residual is the join of the two block residuals. -/
theorem AlternatingPairSetup.central_point_residual_pair
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G))
    (z : G) (hzS : z ∈ ChapterB.baumann R) (hzR : z ∈ centralizer (R : Set G))
    (I : Subgroup G) (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = R)
    (hgen : I = (K ⊔ L) ⊔ R) (hn : I ≤ normalizer ((K ⊔ L : Subgroup G) : Set G)) :
    (pResidual 2 (I ⊓ centralizer ({z} : Set G) : Subgroup G)).map
        (I ⊓ centralizer ({z} : Set G)).subtype =
      (pResidual 2 (K ⊓ centralizer ({z} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({z} : Set G)).subtype ⊔
      (pResidual 2 (L ⊓ centralizer ({z} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({z} : Set G)).subtype := by
  let C := centralizer ({z} : Set G)
  let B := I ⊓ C
  let N := (K ⊔ L) ⊓ C
  let A₁ := K ⊓ C
  let A₂ := L ⊓ C
  have hRI : R ≤ I := hgen ▸ le_sup_right
  have hRC : R ≤ C := by
    intro r hr
    exact mem_centralizer_singleton_iff.mpr (hzR r hr)
  have hRB : R ≤ B := le_inf hRI hRC
  obtain ⟨P,hP⟩ := S.exists_map_subtype_eq_of_le
    (show B ≤ I from inf_le_left) (by rw [hS]; exact hRB)
  have hNB : N ≤ B := inf_le_inf_right C (hgen ▸ le_sup_left)
  have hBN : B ≤ normalizer (N : Set G) :=
    (le_inf (inf_le_left.trans hn) (inf_le_right.trans C.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hNgen : N ⊔ R = B := by
    change N ⊔ R = I ⊓ C
    rw [hgen]
    exact (centralizer_supplement (K ⊔ L) R z (hRI.trans hn) hRC).symm
  have hres := residual_of_normal_sylow_supplement B N R P (hP.trans hS) hNB hBN hNgen
  have hpair : N = A₁ ⊔ A₂ := centralizer_pair_join K L z (h.disjoint_blocks x hx hnc)
    h.commute (h.normalizes hzS) (h'.normalizes hzS)
  have hcomm : A₂ ≤ centralizer (A₁ : Set G) :=
    inf_le_left.trans (h.commute.trans (centralizer_le inf_le_left))
  let : (A₁.subgroupOf (A₁ ⊔ A₂)).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le A₁.le_normalizer (hcomm.trans (Subgroup.centralizer_le_normalizer _)))
  let : (A₂.subgroupOf (A₁ ⊔ A₂)).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le ((le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le_normalizer _))
      A₂.le_normalizer)
  exact hres.trans ((congrArg (fun P : Subgroup G => (pResidual 2 P).map P.subtype) hpair).trans
    (embedded_pResidual_sup_of_relative_normal 2 A₁ A₂).symm)

omit [Finite G] in
private theorem join_inf_factor (K L A B : Subgroup G) (hAK : A ≤ K) (hBL : B ≤ L)
    (hd : Disjoint K L) (hc : B ≤ centralizer (A : Set G)) : (A ⊔ B) ⊓ K = A := by
  apply le_antisymm
  · rintro g ⟨hg,hgK⟩
    have hgm : g ∈ (A : Set G) * (B : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left A B (hc.trans (Subgroup.centralizer_le_normalizer _))]
      exact hg
    obtain ⟨a,ha,b,hb,rfl⟩ := hgm
    have hbK : b ∈ K := by simpa only [inv_mul_cancel_left] using K.mul_mem (K.inv_mem (hAK ha)) hgK
    have hb1 : b = 1 := mem_bot.mp (hd.le_bot ⟨hbK,hBL hb⟩)
    change a*b ∈ A
    rw [hb1,mul_one]
    exact ha
  · exact le_inf le_sup_left hAK

/-- Intersecting the ambient point residual with a block recovers its own point residual. -/
theorem AlternatingPairSetup.central_point_residual_factor
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G))
    (z : G) (hzS : z ∈ ChapterB.baumann R) (hzR : z ∈ centralizer (R : Set G))
    (I : Subgroup G) (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = R)
    (hgen : I = (K ⊔ L) ⊔ R) (hn : I ≤ normalizer ((K ⊔ L : Subgroup G) : Set G)) :
    ((pResidual 2 (I ⊓ centralizer ({z} : Set G) : Subgroup G)).map
      (I ⊓ centralizer ({z} : Set G)).subtype) ⊓ K =
      (pResidual 2 (K ⊓ centralizer ({z} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({z} : Set G)).subtype := by
  rw [h.central_point_residual_pair h' x hx hnc z hzS hzR I S hS hgen hn]
  apply join_inf_factor K L _ _ ((map_subtype_le _).trans inf_le_left)
    ((map_subtype_le _).trans inf_le_left) (h.disjoint_blocks x hx hnc)
  exact ((map_subtype_le _).trans inf_le_left).trans
    (h.commute.trans (centralizer_le ((map_subtype_le _).trans inf_le_left)))

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource


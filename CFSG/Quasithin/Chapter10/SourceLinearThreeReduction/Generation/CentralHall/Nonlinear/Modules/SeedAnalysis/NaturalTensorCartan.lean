module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorHall
public import Theory.GroupTheory.Hall.Conjugacy

/-!
# The actual cyclic Cartan in the remaining natural tensor branch

Hall conjugacy in the original solvable overlap puts the E.2.2 cyclic
Mersenne divisor into the exponent of the prescribed B. Split-torus placement
bounds that exponent by 2ⁿ−1. The established n(H) >= n−1 forces the
E.2.2 degree to be exactly n. A nonzero seed vector fixed by B makes its
projection on one SL₂ factor faithful, so B is cyclic of order 2ⁿ−1.

The literal Hall alternative retains the original tensor and determinant
markings, seed preservation, common split Cartan and exact Hall order.
An actual E.2.2 witness at degree n retains permutation and reflected escape.
We prove n−1 <= n(H) <= n, not equality through a solvable quotient kernel.
The exchanged-actor fixed-space comparison of 9.2.7 and the final
SourceNonnormalCentralHallAt assembly are still required.
Source: Aschbacher--Smith 9.2.5--7 and 10.2.3, pp.731--732,745,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 ChapterE
open ClassicalOrthogonal.FourPlusMatrix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance tensorCartanSeedElementary : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance tensorCartanBinaryAlgebra (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
variable {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
include c hn e ht htn hsep

open HallGeometry
open ChapterE.Section06.FixedPointBounds.ParabolicCartan

omit hn e ht htn hsep in
/-- Hall conjugacy transports the actual E.2.2 cyclic torus into the
prescribed original Hall group, so its order divides that group's exponent. -/
theorem original_hall_mersenne_exponent :
    ∃ f : ℕ, generationParameter H ≤ f ∧ 1 < f ∧
      2^f-1 ∣ Monoid.exponent B := by
  obtain ⟨hP,f,_hg,hf,d,he,_hp,_hx⟩ :=
    source_hstar_cartan_data_of_generation_gt_one D c.hstar c.large
  let C := D.maximalLocal.subgroupOf H
  have hD : d.witness.abelianGroup ≤ C := by simpa only [he] using d.hall_le
  have hdHall := d.hall
  rw [he] at hdHall
  have hsolv : Group.IsSolvable (D.maximalLocal.subgroupOf H) := by
    rw [←he]
    exact d.maximal_solvable
  obtain ⟨x,hx⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hsolv c.hall hdHall
  let a : B ≃* d.witness.abelianGroup :=
    (subgroupOfEquivOfLe c.hall_le).symm.trans
      (((MulAut.conj x).subgroupMap (B.subgroupOf C)).trans
        ((MulEquiv.subgroupCongr hx.symm).trans (subgroupOfEquivOfLe hD)))
  have heq := Monoid.exponent_eq_of_mulEquiv a
  refine ⟨f,hf,c.large.trans_le hf,?_⟩
  let := d.witness.cyclic
  rw [heq,←d.witness.card,←IsCyclic.exponent_eq_card]
  exact Monoid.exponent_dvd_of_monoidHom (inclusion d.witness.cyclic_le)
    (inclusion_injective d.witness.cyclic_le)

omit c hn e ht htn hsep in
private theorem mersenne_degree_eq_of_nearby {f n : ℕ} (hn : 3 ≤ n)
    (hf : n-1 ≤ f) (hd : 2^f-1 ∣ 2^n-1) : f = n := by
  have hpow : 2^f ≤ 2^n := by
    have hp : 0 < 2^f := pow_pos (by decide) f
    have hq : 1 < 2^n := Nat.one_lt_two_pow (by omega)
    have hh := Nat.le_of_dvd (by omega : 0 < 2^n-1) hd
    omega
  have hfn : f ≤ n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  by_contra hne
  have hn' : n = f+1 := by omega
  have hf2 : 2 ≤ f := by omega
  have h4 : 4 ≤ 2^f := by
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf2)
  rw [hn',pow_succ] at hd
  have hlt : 0 < 2^f-1 := by omega
  have hsub : 2^f*2-1 = 2*(2^f-1)+1 := by omega
  rw [hsub] at hd
  have hd1 : 2^f-1 ∣ 1 := (Nat.dvd_add_iff_right (dvd_mul_left (2^f-1) 2)).mpr hd
  have he1 := Nat.le_of_dvd (by decide : 0 < 1) hd1
  omega

/-- The actual E.2.2 Cartan exponent equals the tensor field degree. This
uses the prescribed Hall carrier, rather than inferring generation equality
through a possibly solvable quotient kernel. -/
theorem original_even_hall_cartan_degree :
    2^n-1 ∣ Monoid.exponent B ∧ generationParameter H ≤ n := by
  obtain ⟨f,hf,_hf2,hdiv⟩ := original_hall_mersenne_exponent D c
  have hlo := original_even_generation_ge D c n hn e ht htn hsep
  have hd := original_even_hall_exponent_dvd_sub_one D c n hn e ht htn hsep
  have he : f = n := mersenne_degree_eq_of_nearby hn (hlo.trans hf) (hdiv.trans hd)
  exact ⟨he ▸ hdiv,he ▸ hf⟩

/-- The same original Hall subgroup has exactly the split-torus exponent. -/
theorem original_even_hall_exponent_eq_sub_one :
    Monoid.exponent B = 2^n-1 :=
  Nat.dvd_antisymm (original_even_hall_exponent_dvd_sub_one D c n hn e ht htn hsep)
    (original_even_hall_cartan_degree D c n hn e ht htn hsep).1



/-- The original central Hall group is cyclic: its nonzero fixed seed vector
makes one actual SL₂ factor faithful, without dropping an actor kernel. -/
theorem original_even_hall_isCyclic : IsCyclic B := by
  obtain ⟨q,hq,hker,_hl,_hr,α,f,heq⟩ :=
    original_even_seed_determinant D c n hn e ht htn hsep
  have hBR := original_even_hall_le_orbit D c n hn e ht htn hsep
  let r : B →* localOrbit T L := (H.subtype.comp B.subtype).codRestrict _
    (fun b => hBR (mem_map_of_mem H.subtype b.property))
  have hri : Function.Injective r := by
    intro b d h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : localOrbit T L => (z:G)) h
  have hqi : Function.Injective (q.comp r) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro b hb
    have hbcore : r b ∈ pCore 2 (localOrbit T L) := hker ▸ hb
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := localOrbit T L)) ⟨r b,hbcore⟩
    have hpow : b^(2^k) = 1 := by
      apply hri
      rw [map_pow,map_one]
      exact congrArg Subtype.val hk
    have ho := (HallGeometry.hall_odd D c).of_dvd_nat (orderOf_dvd_natCard b)
    exact mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (ho.coprime_two_right.pow_right k) dvd_rfl (orderOf_dvd_of_pow_eq_one hpow)))
  let τ := (NaturalTensor.marking α).toMonoidHom.comp (q.comp r)
  have hτ : Function.Injective τ := (NaturalTensor.marking α).injective.comp hqi
  obtain ⟨z,hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (original_even_seed_fixed_ne_bot D c n hn e ht htn hsep)
  let v : Additive D.seed := Additive.ofMul ⟨(z:G),z.property.1⟩
  have hv : f v ≠ 0 := by
    intro hh
    have hv0 : v = 0 := f.injective (hh.trans f.map_zero.symm)
    exact hzne (Subtype.ext (congrArg (fun w : Additive D.seed => (w.toMul:G)) hv0))
  let := c.abelian
  apply odd_abelian_fixed_isCyclic τ hτ (HallGeometry.hall_odd D c) (f v) hv
  intro b
  change representation (NaturalTensor.marking α (q (r b))) (f v) = f v
  rw [←heq]
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  have hZ : H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp c.central)
  have hzZ := original_even_seed_fixed_le_omegaCenter D c n hn e ht htn hsep z.property
  change (b:G)*(z:G)*(b:G)⁻¹ = (z:G)
  rw [←hZ b.val.property z hzZ,mul_inv_cancel_right]

/-- The actual cyclic Hall group has the same order as the split torus. -/
theorem original_even_hall_card : Nat.card B = 2^n-1 := by
  let := original_even_hall_isCyclic D c n hn e ht htn hsep
  rw [←IsCyclic.exponent_eq_card]
  exact original_even_hall_exponent_eq_sub_one D c n hn e ht htn hsep


/-- The E.2.2 Cartan itself is available at the exact tensor degree, on the
unchanged H and overlap, including permutation and reflected escape. -/
theorem original_even_hstar_cartan_data :
    ∃ (hP : ChapterB.IsMinimalParabolicOver (T.subtype c.hstar.1.1.2) ⊤),
      IsEGenerated n H ∧ generationParameter H ≤ n ∧
      ∃ d : IntrinsicHallCartanData (T.subtype c.hstar.1.1.2) hP n,
        ChapterB.minimalParabolicMax (T.subtype c.hstar.1.1.2) hP = D.maximalLocal.subgroupOf H ∧
        (d.witness.abelianGroup.map H.subtype : Set G) * (T : Set G) =
          (T : Set G) * (d.witness.abelianGroup.map H.subtype : Set G) ∧
        ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup H), Odd p →
          A ≤ d.witness.cyclicGroup → IsPGroup p A →
          ¬ H ⊓ normalizer (A.map H.subtype : Set G) ≤ D.maximalLocal := by
  obtain ⟨hP,f,hg,hf,d,he,hp,hx⟩ :=
    source_hstar_cartan_data_of_generation_gt_one D c.hstar c.large
  have hh := d.hall
  rw [he] at hh
  have hc := hh.card_eq c.hall
  rw [Nat.card_congr (subgroupOfEquivOfLe (he ▸ d.hall_le)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe c.hall_le).toEquiv] at hc
  have hd : 2^f-1 ∣ 2^n-1 := by
    rw [←original_even_hall_card D c n hn e ht htn hsep,←hc,←d.witness.card]
    exact card_dvd_of_le d.witness.cyclic_le
  have hef : f = n := mersenne_degree_eq_of_nearby hn
    ((original_even_generation_ge D c n hn e ht htn hsep).trans hf) hd
  subst f
  exact ⟨hP,hg,hf,d,he,hp,hx⟩

omit hn e ht htn hsep in
/-- The literal Hall alternative now carries actual split Cartan placement
and exact cyclic order for the remaining tensor. Its exclusion for n > 2
still needs the exchanged-actor fixed-space comparison. -/
theorem original_hall_conclusion_or_natural_tensor_cartan :
    (IsPGroup 3 B ∨ ∃ k : ℕ, Monoid.exponent B ∣ 2^k+1) ∨
      ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
        ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
          ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
            D.seed ≤ centralizer (L : Set G)) ∧
          OriginalEvenNaturalTensorAnalysis D ht n e ∧
          OriginalEvenSeedDeterminantCoordinates D ht n e ∧
          D.moduleSubgroup = D.seed ∧
          H ⊓ D.maximalLocal ≤ normalizer (D.seed : Set G) ∧
          B.map H.subtype ≤ localOrbit T L ∧ IsCyclic B ∧
          Nat.card B = 2^n-1 ∧ Monoid.exponent B = 2^n-1 ∧
          n-1 ≤ generationParameter H ∧ generationParameter H ≤ n ∧
          ∃ C : Subgroup G, B.map H.subtype ≤ C ∧ C ≤ sourceOrbitBorel T L ∧
            IsHallSubgroup Subgroup.OddHall.oddPrimes (C.subgroupOf (sourceOrbitBorel T L)) ∧
            Nonempty (C ≃* ((GaloisField 2 n)ˣ × (GaloisField 2 n)ˣ)) := by
  rcases original_hall_conclusion_or_natural_tensor_generation D c with hh |
    ⟨t,ht,htn,n,hn,e,hsep,ha,hdet,hlocal,_hE,_hm,_hr,_hJ,hgen⟩
  · exact Or.inl hh
  · refine Or.inr ⟨t,ht,htn,n,hn,e,hsep,ha,hdet,hlocal,
      original_even_overlap_normalizes_seed D c n hn e ht htn hsep,
      original_even_hall_le_orbit D c n hn e ht htn hsep,
      original_even_hall_isCyclic D c n hn e ht htn hsep,
      original_even_hall_card D c n hn e ht htn hsep,
      original_even_hall_exponent_eq_sub_one D c n hn e ht htn hsep,hgen,
      (original_even_hall_cartan_degree D c n hn e ht htn hsep).2,?_⟩
    obtain ⟨C,hC,hHall,hBC,_e',_q,d,hd,_hl,_hS,_hdiag⟩ :=
      original_even_hall_cartan_coordinates D c n hn e ht htn hsep
    exact ⟨C,hBC,hC,hHall,⟨MulEquiv.ofBijective d hd⟩⟩


end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules

module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Sections

/-!
# Gluing two marked dual orbit sections

Two distinct invariant three-dimensional dual factors with the same lower
subgroup meet precisely in that subgroup. The proof uses transitivity of the
literal dual SL3(2) action, through `MarkedDualSection.sup_eq_of_not_le`.
Each coordinate map then descends through the quotient by the other factor.
The product of these maps is surjective, has the prescribed relative kernel,
and preserves the original marking in its conjugation formula.

This is the algebraic assembly step of MS93 (4.5.4)(iii). Its actual orbit
factors and their independence are supplied by the consumer in `SecondLayer`;
recognition of the single factors remains an independent source obligation.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.5.4)(iii), printed pp.898--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer
open DistanceFour.Linear

private theorem factor {G : Type*} [Group G] {A B H : Subgroup G}
    (hn : A ≤ normalizer B) (hgen : A ⊔ B = H) (x : H) :
    ∃ (a : A) (b : B), (a : G) * b = x := by
  have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right A B hn, hgen]
    exact x.property
  obtain ⟨a, ha, b, hb, he⟩ := hx
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, he⟩

private theorem extend_factor {G T : Type*} [Group G] [Group T]
    {A B H : Subgroup G} (hA : A ≤ H) (hB : B ≤ H)
    (hn : A ≤ normalizer B) (hgen : A ⊔ B = H)
    (f : A →* T) (hf : ∀ a : A, (a : G) ∈ B → f a = 1) :
    ∃ q : H →* T,
      (∀ a : A, q ⟨a, hA a.property⟩ = f a) ∧
      (∀ b : B, q ⟨b, hB b.property⟩ = 1) := by
  let : (B.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (hgen.ge.trans (sup_le hn B.le_normalizer))
  let π := QuotientGroup.mk' (B.subgroupOf H)
  let r : A →* H ⧸ B.subgroupOf H := π.comp (inclusion hA)
  have hkill (b : B) : π ⟨b, hB b.property⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr b.property
  have hr : Function.Surjective r := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf H) z
    obtain ⟨a, b, hab⟩ := factor hn hgen x
    refine ⟨a, ?_⟩
    have hx : x = (⟨a, hA a.property⟩ : H) * ⟨b, hB b.property⟩ :=
      Subtype.ext hab.symm
    rw [hx, map_mul, hkill, mul_one]
    rfl
  have hk : r.ker ≤ f.ker := by
    intro a ha
    apply MonoidHom.mem_ker.mpr
    apply hf
    change inclusion hA a ∈ B.subgroupOf H
    exact (QuotientGroup.eq_one_iff (inclusion hA a)).mp (MonoidHom.mem_ker.mp ha)
  let d := r.liftOfSurjective hr ⟨f, hk⟩
  refine ⟨d.comp π, ?_, ?_⟩
  · intro a
    exact r.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hr) ⟨f, hk⟩ a
  · intro b
    change d (π _) = 1
    rw [hkill, map_one]

variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R} {common : CommonFacts R source geometry}

/-- Two distinct marked dual sections with the same lower subgroup have
exactly that subgroup as their intersection. -/
theorem inf_eq_of_not_le {A B N : Subgroup (FreeAmalgam R)}
    (s : MarkedDualSection source common A N)
    (t : MarkedDualSection source common B N) (hne : ¬ B ≤ A) : A ⊓ B = N := by
  apply le_antisymm _ (le_inf s.lower_le t.lower_le)
  by_contra hn
  have hnorm : Mbar R ≤ normalizer (A ⊓ B) :=
    (le_inf s.normalized t.normalized).trans inf_normalizer_le_normalizer_inf
  have hB := t.sup_eq_of_not_le inf_le_right hnorm hn
  exact hne (hB.ge.trans (sup_le inf_le_left s.lower_le))

/-- Gluing two generating marked dual sections constructs the full product
quotient, including its exact kernel and the unchanged source marking. -/
theorem pair_of_generating_sections {A B H N : Subgroup (FreeAmalgam R)}
    (s : MarkedDualSection source common A N)
    (t : MarkedDualSection source common B N)
    (hgen : A ⊔ B = H) (hne : ¬ B ≤ A) :
    Nonempty (MarkedPairSection source common H N true) := by
  have hA : A ≤ H := le_sup_left.trans hgen.le
  have hB : B ≤ H := le_sup_right.trans hgen.le
  have hAM : A ≤ Mbar R := by
    simpa only [alpha, stabilizer_m_base] using s.local_group
  have hBM : B ≤ Mbar R := by
    simpa only [alpha, stabilizer_m_base] using t.local_group
  have hAB : A ≤ normalizer B := hAM.trans t.normalized
  have hBA : B ≤ normalizer A := hBM.trans s.normalized
  have hinter := inf_eq_of_not_le s t hne
  have hsf (a : A) (ha : (a : FreeAmalgam R) ∈ B) : s.quotient a = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [s.kernel]
    exact hinter.le ⟨a.property, ha⟩
  have htf (b : B) (hb : (b : FreeAmalgam R) ∈ A) : t.quotient b = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [t.kernel]
    exact hinter.le ⟨hb, b.property⟩
  obtain ⟨f, hfA, hfB⟩ := extend_factor hA hB hAB hgen s.quotient hsf
  obtain ⟨g, hgB, hgA⟩ := extend_factor hB hA hBA (sup_comm B A |>.trans hgen)
    t.quotient htf
  let q : H →* Multiplicative (W × W) := {
    toFun x := Multiplicative.ofAdd ((f x).toAdd, (g x).toAdd)
    map_one' := by simp
    map_mul' x y := by
      apply Multiplicative.toAdd.injective
      change ((f (x * y)).toAdd, (g (x * y)).toAdd) =
        ((f x).toAdd + (f y).toAdd, (g x).toAdd + (g y).toAdd)
      simp only [map_mul]
      rfl }
  have hq (a : A) (b : B) :
      q ((⟨a, hA a.property⟩ : H) * ⟨b, hB b.property⟩) =
        Multiplicative.ofAdd ((s.quotient a).toAdd, (t.quotient b).toAdd) := by
    apply Multiplicative.toAdd.injective
    change ((f (_ * _)).toAdd, (g (_ * _)).toAdd) = _
    rw [f.map_mul, g.map_mul, hfA, hfB, hgA, hgB, mul_one, one_mul]
    rfl
  have honto : Function.Surjective q := by
    intro w
    obtain ⟨a, ha⟩ := s.onto (Multiplicative.ofAdd w.toAdd.1)
    obtain ⟨b, hb⟩ := t.onto (Multiplicative.ofAdd w.toAdd.2)
    refine ⟨(⟨a, hA a.property⟩ : H) * ⟨b, hB b.property⟩, ?_⟩
    rw [hq, ha, hb]
    rfl
  have hker : q.ker = N.subgroupOf H := by
    ext x
    obtain ⟨a, b, hab⟩ := factor hAB hgen x
    have hx : x = (⟨a, hA a.property⟩ : H) * ⟨b, hB b.property⟩ :=
      Subtype.ext hab.symm
    constructor
    · intro hxker
      have he := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hxker)
      rw [hx, hq] at he
      have ha : (a : FreeAmalgam R) ∈ N := by
        have hk : a ∈ s.quotient.ker := MonoidHom.mem_ker.mpr
          (Multiplicative.toAdd.injective (congrArg Prod.fst he))
        rw [s.kernel] at hk
        exact hk
      have hb : (b : FreeAmalgam R) ∈ N := by
        have hk : b ∈ t.quotient.ker := MonoidHom.mem_ker.mpr
          (Multiplicative.toAdd.injective (congrArg Prod.snd he))
        rw [t.kernel] at hk
        exact hk
      change (x : FreeAmalgam R) ∈ N
      rw [← hab]
      exact N.mul_mem ha hb
    · intro hxN
      let a' : A := ⟨x, s.lower_le hxN⟩
      have hs : s.quotient a' = 1 := MonoidHom.mem_ker.mp (by
        rw [s.kernel]; exact hxN)
      have hx' : x = (⟨a', hA a'.property⟩ : H) := rfl
      apply MonoidHom.mem_ker.mpr
      apply Multiplicative.toAdd.injective
      change ((f x).toAdd, (g x).toAdd) = (0, 0)
      rw [hx', hfA, hgA, hs]
      rfl
  refine ⟨⟨hgen.ge.trans (sup_le s.local_group t.local_group), s.lower_le.trans hA,
    ?_, q, honto, hker, ?_⟩⟩
  · rw [← hgen]
    exact (le_inf s.normalized t.normalized).trans
      (normalizer_inf_normalizer_le_normalizer_sup A B)
  · intro m x y hy
    obtain ⟨a, b, hab⟩ := factor hAB hgen x
    let a' : A := ⟨embedM R m * (a : FreeAmalgam R) * (embedM R m)⁻¹,
      le_normalizer_iff.mp s.normalized _ ⟨m, rfl⟩ _ a.property⟩
    let b' : B := ⟨embedM R m * (b : FreeAmalgam R) * (embedM R m)⁻¹,
      le_normalizer_iff.mp t.normalized _ ⟨m, rfl⟩ _ b.property⟩
    have hx : x = (⟨a, hA a.property⟩ : H) * ⟨b, hB b.property⟩ :=
      Subtype.ext hab.symm
    have hy' : y = (⟨a', hA a'.property⟩ : H) * ⟨b', hB b'.property⟩ := by
      apply Subtype.ext
      rw [hy, ← hab]
      simp [a', b', mul_assoc]
    rw [hy', hx, hq, hq]
    simp only [toAdd_ofAdd, reduceIte]
    exact Prod.ext (s.action m a a' rfl) (t.action m b b' rfl)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer

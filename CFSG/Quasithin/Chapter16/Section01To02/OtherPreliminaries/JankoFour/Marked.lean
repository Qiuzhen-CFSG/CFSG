module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.Reduction
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic

/-!
# Marked involution classes in the actual J₄ carrier

The certified max1 odd index promotes its exhaustive involution fusion to
Janko4.Model. The explicit seed-to-word conjugacy connects that fusion to the
full second centralizer. The first centralizer's Sylow subgroups are ambient
Sylow, while the second centralizer order has two-part only 2^19, compared
with the ambient Sylow order 2^21. Thus the first class is precisely the
class of two-central involutions.

The final equivalences restrict actual conjugation to the full fixed groups.
These local arguments require no global simplicity, perfectness or innerness.
`SylowCentral` is proved equivalent to the intrinsic `TwoCentral` marking
used in the later 16.5.6(4) consumer; no later section is imported here.

Source: Aschbacher–Smith 16.1.5(9), printed p.1172, and GLS3 Table 5.3i,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. No class identification follows merely
from a centralizer order: exhaustive actual fusion supplies the equivalences.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoFour
open Subgroup Theory.GroupTheory Janko4 Janko4.InvolutionCentralizers

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- An ambient Sylow two-subgroup contains and centralizes the marked element. -/
def SylowCentral (x : Model) : Prop :=
  ∃ S : Sylow 2 Model, x ∈ S ∧ (S : Subgroup Model) ≤ centralizer ({x} : Set Model)

theorem first_sylowCentral : SylowCentral a := by
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := centralizer ({a} : Set Model))
  obtain ⟨S, hS⟩ := OuterReduction.OddIndex.centralizer_sylow_is_ambient P
  refine ⟨S, ?_, ?_⟩
  · have ha := OuterReduction.OddIndex.centralizer_sylow_center P
    have hm := ha.ge (mem_zpowers a)
    change a ∈ (S : Subgroup Model)
    rw [hS]
    exact map_subtype_le _ hm
  · rw [hS]
    exact map_subtype_le _

theorem seed_not_sylowCentral : ¬ SylowCentral (Second.seed : Model) := by
  rintro ⟨S, _, hS⟩
  have hd := card_dvd_of_le hS
  change Nat.card S ∣ Nat.card Second.ambientCentralizer at hd
  rw [OuterReduction.OddIndex.ambient_sylow_card, Second.ambient_card] at hd
  norm_num at hd

theorem SylowCentral.of_isConj {x y : Model} (hx : SylowCentral x)
    (h : IsConj x y) : SylowCentral y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  obtain ⟨S, hx, hS⟩ := hx
  let e := MulAut.conj g
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ⟨x, hx, rfl⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  exact (e.map_mul s x).symm.trans
    ((congrArg e (mem_centralizer_singleton_iff.mp (hS hs))).trans (e.map_mul x s))

/-- The literal seed and the second global fusion word are conjugate, not equal. -/
theorem seed_isConj_second : IsConj (Second.seed : Model) ((a * b * a * b * b) ^ 5) := by
  obtain ⟨g, hg⟩ := Simplicity.Max1Fusion.seed_fuses_second matrixA_mul_self matrixB_pow_four
  have ha : Simplicity.a matrixA_mul_self = a := by apply toMatrix_injective; rfl
  have hb : Simplicity.b matrixB_pow_four = b := by apply toMatrix_injective; rfl
  rw [ha, hb] at hg
  have hw : Simplicity.word a b "ababb" = a * b * a * b * b := by
    simp [Simplicity.word, mul_assoc]
  rw [hw] at hg
  exact isConj_iff.mpr ⟨g, hg.symm⟩

/-- Exhaustive fusion on the original carrier, with the actual centralizer seeds. -/
theorem involution_fusion {x : Model} (hx : orderOf x = 2) :
    IsConj a x ∨ IsConj (Second.seed : Model) x := by
  rcases OuterReduction.involution_isConj_of_max1_odd_index
    OuterReduction.max1_odd_index_unconditional hx with h | h
  · exact Or.inl h
  · exact Or.inr (seed_isConj_second.trans h)

theorem isConj_first_iff_sylowCentral {x : Model} (hx : orderOf x = 2) :
    IsConj a x ↔ SylowCentral x := by
  constructor
  · exact first_sylowCentral.of_isConj
  · intro hc
    rcases involution_fusion hx with h | h
    · exact h
    · exact (seed_not_sylowCentral (hc.of_isConj h.symm)).elim

theorem isConj_seed_iff_not_sylowCentral {x : Model} (hx : orderOf x = 2) :
    IsConj (Second.seed : Model) x ↔ ¬ SylowCentral x := by
  constructor
  · intro h hc
    exact seed_not_sylowCentral (hc.of_isConj h.symm)
  · intro hc
    rcases involution_fusion hx with h | h
    · exact (hc (first_sylowCentral.of_isConj h)).elim
    · exact h

/-- Conjugation restricts to an isomorphism of the full fixed subgroups. -/
theorem fixed_equiv_of_isConj {x y : Model} (h : IsConj x y) :
    Nonempty ((MulAut.conj x).fixedSubgroup ≃* (MulAut.conj y).fixedSubgroup) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have he : MulAut.congr (MulAut.conj g) (MulAut.conj x) = MulAut.conj y := by
    rw [MulAut.congr_conj]
    exact congrArg MulAut.conj hg
  exact ⟨(MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj x)).trans
    (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup he))⟩

theorem central_fixed_equiv {x : Model} (hx : orderOf x = 2) (hc : SylowCentral x) :
    Nonempty ((MulAut.conj x).fixedSubgroup ≃* First.centralizer) := by
  obtain ⟨e⟩ := fixed_equiv_of_isConj ((isConj_first_iff_sylowCentral hx).mpr hc)
  exact ⟨e.symm.trans (MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj a))⟩

theorem noncentral_fixed_equiv {x : Model} (hx : orderOf x = 2) (hc : ¬ SylowCentral x) :
    Nonempty ((MulAut.conj x).fixedSubgroup ≃* Second.ambientCentralizer) := by
  obtain ⟨e⟩ := fixed_equiv_of_isConj ((isConj_seed_iff_not_sylowCentral hx).mpr hc)
  exact ⟨e.symm.trans (MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj (Second.seed : Model)))⟩

/-- The centralizer formulation equals the genuine Sylow-center marking. -/
theorem sylowCentral_iff_twoCentral {x : Model} :
    SylowCentral x ↔ DoubleCoverCentralizer.TwoCentral x := by
  constructor
  · rintro ⟨S, hx, hS⟩
    refine ⟨S, hx, mem_center_iff.mpr ?_⟩
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hS y.property))
  · rintro ⟨S, hx, hc⟩
    refine ⟨S, hx, ?_⟩
    intro y hy
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hc ⟨y, hy⟩))

/-- The literal first representative is genuinely two-central. -/
theorem first_twoCentral : DoubleCoverCentralizer.TwoCentral a :=
  sylowCentral_iff_twoCentral.mp first_sylowCentral

/-- The literal second seed is not two-central in the full model. -/
theorem seed_not_twoCentral : ¬ DoubleCoverCentralizer.TwoCentral
    (Second.seed : Model) :=
  fun h => seed_not_sylowCentral (sylowCentral_iff_twoCentral.mpr h)

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoFour

module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.Sections
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.OddBenderExclusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowObstructions
public import Theory.Mathieu.M23.Properties.SylowObstructions
public import Theory.SpecificGroups.PSL3Four.SylowObstructions
/-!
# Odd and Bender containing rows for exceptional sections

Every odd Theorem C Sylow has cyclic derived subgroup, a property preserved
by subgroup and quotient maps. The actual exceptional carriers have two
distinct commutator involutions, excluding their occurrence as any section.

For a Bender containing model the original Sylow-normalized local component
is the whole simple group. Its exceptional quotient makes the two-core
trivial. Noncommuting Sylow involutions exclude binary linear and unitary
rank one; divisibility by three excludes Suzuki.

Source: Aschbacher–Smith A.3.12, pp.47–48, applied to 13.6.27, p.934.
-/
public section
noncomputable section
open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups.HermitianForm
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
variable {G : Type*} [Group G]

/-- No exceptional two-core section occurs when every Sylow derived group is cyclic. -/
theorem not_section_of_cyclic_derived_sylows [Finite G]
    (hG : ∀ S : Sylow 2 G, IsCyclic (commutator S)) (B : Subgroup G)
    (hsection : IsModel (B ⧸ pCore 2 B)) : False := by
  have hquot : ∀ S : Sylow 2 (B ⧸ pCore 2 B), IsCyclic (commutator S) :=
    sylow_derived_cyclic_of_surjective (QuotientGroup.mk' (pCore 2 B))
      (QuotientGroup.mk'_surjective _)
      (sylow_derived_cyclic_of_injective B.subtype B.subtype_injective hG)
  rcases hsection with h | h | h
  all_goals obtain ⟨e⟩ := h
  · let S : Sylow 2 Sporadic.LeechRelated.J2.Carrier := Sylow.nonempty.some
    exact Sporadic.LeechRelated.J2.sylow_derived_not_cyclic S
      (sylow_derived_cyclic_of_surjective e.toMonoidHom e.surjective hquot S)
  · let S : Sylow 2 Sporadic.Mathieu.M23 := Sylow.nonempty.some
    exact Sporadic.Mathieu.m23_sylow_derived_not_cyclic S
      (sylow_derived_cyclic_of_surjective e.toMonoidHom e.surjective hquot S)
  · let S : Sylow 2 Matrix.PSL3Four.PSL := Sylow.nonempty.some
    exact Matrix.PSL3Four.sylow_derived_not_cyclic S
      (sylow_derived_cyclic_of_surjective e.toMonoidHom e.surjective hquot S)

/-- The odd rows are excluded for any subgroup, retaining its original two-core. -/
theorem not_section_of_odd_model [Finite G]
    (hG : ChapterA.Section02.IsTheoremCOddModel G) (B : Subgroup G)
    (hsection : IsModel (B ⧸ pCore 2 B)) : False :=
  not_section_of_cyclic_derived_sylows
    (AlternatingEight.odd_model_sylow_derived_cyclic hG) B hsection

private theorem not_bender_of_sylow_pair [Finite G] (hm : ClassificationModels.IsBenderModel G)
    (S : Sylow 2 G) (hp : ∃ x y : S, x^2=1 ∧ y^2=1 ∧ x*y≠y*x)
    (hc : 3 ∣ Nat.card G) : False := by
  obtain ⟨x,y,hx,hy,hxy⟩ := hp
  cases hm with
  | linear n hn hmodel =>
    obtain ⟨K,_,_,hK,⟨eK⟩⟩ := hmodel
    let := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (by
      simpa only [Nat.card_eq_fintype_card] using hK)
    let := Theory.PSL2.binary_sylow_commutative_of_injective eK.toMonoidHom eK.injective S
    exact hxy (IsMulCommutative.is_comm.comm x y)
  | unitary n hn hmodel =>
    obtain ⟨K,_,_,J,hK,hconj,⟨eK⟩⟩ := hmodel
    have hfixed : Nat.card {a : K // J.conj a = a} = 2 ^ n :=
      FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
    obtain ⟨d⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hK hfixed
    let J' := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
    have hOmega := (SylowOmega.omega_of_projective_equiv J' hn hK hfixed rfl
      (eK.trans d) S).1
    have hxc : (x : G) ∈ (center S).map (S : Subgroup G).subtype :=
      (omegaOneAmbient_le_iff _ _).mp hOmega.le x x.property (congrArg Subtype.val hx)
    obtain ⟨z,hz,hzx⟩ := hxc
    have hz' : z = x := Subtype.ext hzx
    subst z
    exact hxy (mem_center_iff.mp hz y).symm
  | suzuki m hm he =>
    obtain ⟨d⟩ := he
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega)
      (Nat.card_congr d.toEquiv ▸ hc)

/-- None of the three actual exceptional carriers is a Bender model. -/
theorem not_bender_model [Finite G] (hsection : IsModel G)
    (hm : ClassificationModels.IsBenderModel G) : False := by
  have hc : 3 ∣ Nat.card G := (by decide : 3 ∣ 20160).trans hsection.card_dvd
  rcases hsection with h | h | h
  all_goals obtain ⟨e⟩ := h
  · let S : Sylow 2 Sporadic.LeechRelated.J2.Carrier := Sylow.nonempty.some
    exact not_bender_of_sylow_pair (hm.of_mulEquiv e.symm) S
      (Sporadic.LeechRelated.J2.exists_noncommuting_sylow_involutions S)
      (Nat.card_congr e.toEquiv ▸ hc)
  · let S : Sylow 2 Sporadic.Mathieu.M23 := Sylow.nonempty.some
    exact not_bender_of_sylow_pair (hm.of_mulEquiv e.symm) S
      (Sporadic.Mathieu.m23_exists_noncommuting_sylow_involutions S)
      (Nat.card_congr e.toEquiv ▸ hc)
  · let S : Sylow 2 Matrix.PSL3Four.PSL := Sylow.nonempty.some
    exact not_bender_of_sylow_pair (hm.of_mulEquiv e.symm) S
      (Matrix.PSL3Four.exists_noncommuting_sylow_involutions S)
      (Nat.card_congr e.toEquiv ▸ hc)

/-- The actual Sylow-normalized exceptional local section excludes Bender containing rows. -/
theorem not_section_of_bender_model [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hsection : IsModel (B ⧸ pCore 2 B))
    (hm : ClassificationModels.IsBenderModel G) : False := by
  have ht := AlternatingEight.eq_top_of_bender_model S B hB hn hm
  let eB : B ≃* G := (MulEquiv.subgroupCongr ht).trans topEquiv
  let : IsSimpleGroup B := eB.isSimpleGroup
  have hcore : pCore 2 B = ⊥ := by
    rcases (inferInstance : (pCore 2 B).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · have hd := hsection.card_dvd
      rw [hc] at hd
      simp at hd
  let q : B ≃* B ⧸ pCore 2 B := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hcore.symm)
  exact not_bender_model (hsection.of_equiv q) (hm.of_mulEquiv eB)
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional

module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionDiagram
public import Theory.SpecificGroups.Suzuki.LinearSeparation
public import Theory.SpecificGroups.PSL2.BinarySylowEmbedding
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel.Basic

/-!
# Excluding Suzuki and unitary quotients in the diagram branch

The canonical right factor in either marked diagram row has quotient
PSL₂(2ᶠ), with f > 1. Its parameter remains independent of the original
left field degree. Binary PSL₂ has order divisible by three, while the
positive Suzuki models do not. Every two-subgroup of every quotient of
binary PSL₂ is abelian; Huppert's actual unitary root group has nontrivial
commutator subgroup. Transport through the original Hermitian form and
the genuine SU₃-to-PSU₃ projection therefore excludes the special unitary
alternative, in particular SU₃(4) in the U₅(4) row.

Together with the nonshort obstruction, the source selector now rules out
the linear-three, symplectic-four, Ree-four and unitary-five rows for a
diagram-selected factor. This does not remove U₅(4) from the global theorem:
that row can still occur when the right factor is the whole residual.
The G₂, triality and unitary-four exclusions and compatible amalgam and
ambient completion recognition remain with this task. Original uniqueness
has its independent producer; the Chapter 12 extension uses the same factor,
quotient, source overlap core and odd Cartans.

Source: Aschbacher–Smith, 5.2.6, printed pp.650–651; Huppert II.8.2(a),
II.10.12, and Huppert–Blackburn III XI.3.3 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open scoped IsMulCommutative
open CFSG.Quasithin BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

private theorem binary_image_twoSubgroup_commutative
    {F Y : Type*} [Field F] [Finite F] [CharP F 2] [Group Y] [Finite Y]
    (f : PSL(2,F) →* Y) (hf : Function.Surjective f)
    (R : Subgroup Y) (hR : IsPGroup 2 R) : IsMulCommutative R := by
  obtain ⟨P,hRP⟩ := hR.exists_le_sylow
  obtain ⟨Q,hQ⟩ := Sylow.mapSurjective_surjective hf 2 P
  let : IsMulCommutative Q := Theory.PSL2.binary_sylow_commutative_of_injective
    (MonoidHom.id _) Function.injective_id Q
  have hc : IsMulCommutative ((Q : Subgroup PSL(2,F)).map f) := map_isMulCommutative _ _
  have he : (Q : Subgroup PSL(2,F)).map f = (P : Subgroup Y) :=
    congrArg (fun S : Sylow 2 Y => (S : Subgroup Y)) hQ
  let : IsMulCommutative P := he ▸ hc
  refine ⟨⟨fun x y => ?_⟩⟩
  exact Subtype.ext (congrArg (fun z : P => (z : Y))
    (mul_comm (⟨x,hRP x.property⟩ : P) ⟨y,hRP y.property⟩))

private theorem binary_no_standard_unitary_image
    {F E : Type*} [Field F] [Finite F] [CharP F 2] [Field E] [Finite E]
    (J : HermitianForm 3 E) {m : ℕ} (hm : 0 < m)
    (hc : Nat.card E = (2^m)^2) (hj : ∀ x, J.conj x = x^(2^m))
    (hs : J.form = !![0,0,1;0,1,0;1,0,0])
    (f : PSL(2,F) →* ProjectiveSpecialUnitaryMatrixGroup J) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨_,rho,pinf,_,_,_,⟨R,D,_,_,_,_,_,_,hR,_,hd,_⟩,_⟩ :=
    BenderSuzuki.External.huppert_II_10_12 J (2^m) hc
      (ChapterF.Source.Unitary.fixed_card J m hm hc hj) hs
  have hp : IsPGroup 2 R := IsPGroup.of_card
    (show Nat.card R = 2^(m*3) by simpa only [pow_mul] using hR)
  have hcomm := binary_image_twoSubgroup_commutative f hf R hp
  rw [(commutator_eq_bot_iff R).mpr hcomm] at hd
  have hlarge : 1 < 2^m := Nat.one_lt_pow (by omega) (by decide)
  rw [card_bot] at hd
  omega

/-- The actual binary linear quotient excludes every positive Suzuki parameter. -/
theorem binary_quotient_not_suzuki {X : Type*} [Group X]
    {n : ℕ} (hlin : ClassicalGroup.IsPSL X 2 (2^n))
    {m : ℕ} (hm : 0 < m) : ¬ Nonempty (X ≃* SuzukiMatrixGroup m) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hlin
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  rintro ⟨s⟩
  exact not_nonempty_psl2_char_two_equiv_suzuki F hm ⟨e.symm.trans s⟩

/-- SU₃ has a nonabelian two-subgroup in its projective image, whereas
every two-subgroup of every image of binary PSL₂ is abelian. -/
theorem binary_quotient_not_special_unitary {X : Type*} [Group X]
    {n m : ℕ} (hlin : ClassicalGroup.IsPSL X 2 (2^n))
    (hm : 0 < m) : ¬ ChapterF.Source.IsSU X 3 (2^m) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hlin
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  rintro ⟨E,_,_,J,hE,hj,⟨s⟩⟩
  obtain ⟨C,hC⟩ := ChapterF.Source.Unitary.FormTransport.exists_standard_basis J m hm hE hj
  let d := ChapterF.Source.Unitary.FormTransport.specialEquiv J C hC
  let q := ChapterF.Source.Unitary.suProjection (ChapterF.Source.Unitary.FormTransport.standardForm J)
  let f := q.comp (d.toMonoidHom.comp (s.toMonoidHom.comp e.symm.toMonoidHom))
  exact binary_no_standard_unitary_image
    (ChapterF.Source.Unitary.FormTransport.standardForm J) hm hE hj rfl f
    ((ChapterF.Source.Unitary.suProjection_surjective _).comp
      (d.surjective.comp (s.surjective.comp e.symm.surjective)))

variable {G : Type*} [Group G] [Finite G]

/-- On the same selected diagram factor, the binary quotient rules out
the Suzuki and SU₃(4) local alternatives; nonshortness rules out the two
natural-block alternatives. This is local exclusion, not recognition. -/
theorem diagram_source_rightFactor_obstructions
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hs : RightDiagramSource T L H) :
    ∃ (R : Subgroup G) (f : ℕ), RightFactor T L H A B R ∧ Group.IsPerfect R ∧
      1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
      ¬ ChapterC.IsShort R ∧
      (∀ m : ℕ, 0 < m → ¬ Nonempty ((R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup m)) ∧
      ¬ ChapterF.Source.IsSU (R ⧸ pCore 2 R) 3 4 := by
  obtain ⟨R,f,hr,hp,hnot,hf,hlin⟩ :=
    diagram_source_rightFactor_linear_not_short h hH hpar hthree c hN hs
  refine ⟨R,f,hr,hp,hf,hlin,hnot,fun _ hm => binary_quotient_not_suzuki hlin hm,?_⟩
  exact binary_quotient_not_special_unitary hlin (m := 2) (by decide)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

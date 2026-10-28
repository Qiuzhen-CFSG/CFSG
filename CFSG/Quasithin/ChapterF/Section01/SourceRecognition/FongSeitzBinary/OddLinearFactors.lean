module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.ProfileRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularUnitaryCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiAllLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.DihedralLocal
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Elementary
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.SimpleCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OriginalActorQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OddLinearRootCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi

/-!
# Elementary roots and original linear factors on odd polygons

An elementary canonical root gives the exact local-kernel containment.
Its faithful Sylow image excludes Suzuki and both unitary scalar
conventions: in these models omega lies in Frattini, whereas a nontrivial
elementary Sylow has trivial Frattini. The D10 factor is handled by its
full Sz(2) cover. Thus the original factor is linear, and conversely every
original linear factor gives an elementary root, including degree one.

Odd opposition transports this conclusion to the opposite original factor.
The root cardinalities identify the binary degrees exactly. Both original
core preimages follow from the same full amalgam marking. No endpoint
perfectness or field-size restriction is imposed.

Source: Fong--Seitz I (2B), (3B), (5C), pp.9,13,25--26, with the actual
odd-dihedral split-root opposition; DGS, Groups and Graphs, Theorem D,
p.224. TriangleStructure.LinearRadicals uses the result to construct the
triangle core inputs, rather than assuming a local-type label.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

private theorem elementary_root_frattini_exclusion (i : Fin 2)
    (hE : IsElementaryAbelian 2 (simpleRoot Q split i))
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    {Y : Type*} [Group Y] (μ : localGroup Q split i ≃* Y)
    (hphi : ∀ T : Sylow 2 Y, omegaOneAmbient (T : Subgroup Y) ≤
      (frattini T).map (T : Subgroup Y).subtype) : False := by
  let : Finite Y := Finite.of_surjective μ μ.surjective
  let U := GTwoSource.localSylow Q split i
  let T := U.mapSurjective (f := μ.toMonoidHom) μ.surjective
  let a : simpleRoot Q split i ≃* T :=
    (GTwoSource.simpleRootLocalSylowEquiv Q split i hV).trans
      ((U : Subgroup _).equivMapOfInjective μ.toMonoidHom μ.injective)
  let := hE
  let : IsElementaryAbelian 2 T := IsElementaryAbelian.of_injective
    a.symm.toMonoidHom a.symm.injective
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  have hh := hphi T
  rw [omegaOneAmbient_eq_self, frattini_eq_bot_of_isElementaryAbelian (p := 2),
    Subgroup.map_bot] at hh
  apply simpleRoot_ne_bot Q split i
  apply eq_bot_iff.mpr
  intro r hr
  have he : a ⟨r,hr⟩ = 1 := Subtype.ext (hh (a ⟨r,hr⟩).property)
  exact congrArg Subtype.val (a.injective (he.trans a.map_one.symm))

include e h in
/-- An elementary canonical root forces an actual linear original factor.
The dihedral-ten branch is excluded through its full Sz(2) cover. -/
theorem linear_factor_of_elementary_root (i : Fin 2)
    (hE : IsElementaryAbelian 2 (simpleRoot Q split i)) :
    ∃ n, 0 < n ∧ ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n) := by
  have hV := (QuadrangleStructure.regularity_of_elementary_root Q e h split i hE).1
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have suzuki_excluded {m : ℕ} (ν : localGroup Q split i ≃* SuzukiMatrixGroup m) : False := by
    apply elementary_root_frattini_exclusion Q split i hE hV ν
    intro R
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact smallSuzuki_omega_le_frattini R
    · rw [← suzukiSylow_commutator_eq_omega hm (MulEquiv.refl _) R,
        ← map_subtype_commutator]
      let : Fact (IsPGroup 2 R) := ⟨R.isPGroup'⟩
      exact map_mono (commutator_le_frattini_of_isPGroup (p := 2) (R := R))
  cases h.quotient i with
  | linear n hn hm => exact ⟨n,hn,hm⟩
  | suzuki m hm =>
    exact (suzuki_excluded (suzukiAllLocalEquiv Q e h split i T hT hm.some)).elim
  | dihedral hm =>
    exact (suzuki_excluded (dihedralSuzukiLocalEquiv Q e h split i T hT hm.some)).elim
  | projective_unitary n hn hm =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hm
    obtain ⟨ν,_⟩ := regular_unitary_cover_of_factor Q e h split J hn hcard hconj i hV (Or.inr ⟨μ⟩)
    exact (elementary_root_frattini_exclusion Q split i hE hV ν
      (HermitianForm.SylowFrattini.projective_omega_le_frattini J hn hcard hconj)).elim
  | special_unitary n hn hm =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hm
    obtain ⟨ν,_⟩ := regular_unitary_cover_of_factor Q e h split J hn hcard hconj i hV (Or.inl ⟨μ⟩)
    exact (elementary_root_frattini_exclusion Q split i hE hV ν
      (HermitianForm.SylowFrattini.projective_omega_le_frattini J hn hcard hconj)).elim

include e h in
/-- The original linear quotient supplies an elementary canonical root,
without perfectness and including the binary field. -/
theorem elementary_root_of_linear_factor (i : Fin 2) {n : ℕ}
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) :
    IsElementaryAbelian 2 (simpleRoot Q split i) := by
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hi
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hV := linear_remainder_le_kernel_of_model Q e h split i ⟨F,hF,hfin,hcard,⟨μ⟩⟩
  obtain ⟨f,hf,hk,_⟩ := linear_actor_quotient_of_factor Q e h split i μ
  let A := (S ⊔ L i).subgroupOf (parabolic L S i)
  let : A.Normal := QuadrangleStructure.marked_sylow_factor_normal Q e h split i
  obtain ⟨_,ν,_,_⟩ := QuadrangleStructure.marked_linear_localGroup Q e h split i
    (UnitarySource.actorReflection Q split i) hV A (subgroupOf_mono _ le_sup_left) f hf hk
  exact simpleRoot_elementary_of_linear Q split i ν

include e h in
/-- Elementary roots characterize the original linear factor within the
full F.1.1 catalogue, retaining both unitary scalar conventions and D10. -/
theorem elementary_root_iff_linear_factor (i : Fin 2) :
    IsElementaryAbelian 2 (simpleRoot Q split i) ↔
      ∃ n, 0 < n ∧ ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n) := by
  constructor
  · exact linear_factor_of_elementary_root Q e h split i
  · rintro ⟨n,_,hi⟩
    exact elementary_root_of_linear_factor Q e h split i hi

include e h split in
/-- Odd opposition transports a single original linear factor to the other
endpoint with exactly the same binary field degree. Neither factor is
assumed perfect. -/
theorem odd_linear_factors_same_degree (hm : Odd (rotationOrder Q))
    (i j : Fin 2) (hij : i ≠ j) {n : ℕ}
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) :
    ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^n) := by
  have hEi := elementary_root_of_linear_factor Q e h split i hi
  have hEj : IsElementaryAbelian 2 (simpleRoot Q split j) := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · let : IsElementaryAbelian 2 (simpleRoot Q split 0) := hEi
      exact IsElementaryAbelian.of_injective
        (simpleRootOppositionEquiv Q split hm).symm.toMonoidHom
        (simpleRootOppositionEquiv Q split hm).symm.injective
    · let : IsElementaryAbelian 2 (simpleRoot Q split 1) := hEi
      exact IsElementaryAbelian.of_injective
        (simpleRootOppositionEquiv Q split hm).toMonoidHom
        (simpleRootOppositionEquiv Q split hm).injective
    · exact (hij rfl).elim
  obtain ⟨m,hmpos,hj⟩ := linear_factor_of_elementary_root Q e h split j hEj
  have root_card (k : Fin 2) {a : ℕ}
      (hk : ClassicalGroup.IsPSL ((L k) ⧸ pCore 2 (L k)) 2 (2^a)) :
      Nat.card (simpleRoot Q split k) = 2^a := by
    obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hk
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    let := h.finite_local k
    obtain ⟨T,hT⟩ := h.sylow k
    exact (simpleRoot_card_linear Q e h split k T hT μ).trans hcard
  have hc : Nat.card (simpleRoot Q split i) = Nat.card (simpleRoot Q split j) := by
    have hc := Nat.card_congr (simpleRootOppositionEquiv Q split hm).toEquiv
    fin_cases i <;> fin_cases j
    · rfl
    · exact hc
    · exact hc.symm
    · rfl
  rw [root_card i hi,root_card j hj] at hc
  have he : n=m := (Nat.pow_right_injective (by decide : 1 < 2)) hc
  simpa only [he] using hj

include e h in
/-- A linear endpoint on an odd polygon gives both exact original core
preimages, without the old perfectness premise. -/
theorem odd_linear_regularity (hm : Odd (rotationOrder Q))
    (i : Fin 2) {n : ℕ}
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) :
    ∀ j : Fin 2, simpleRemainder Q split j ≤ localKernel Q j ∧
      (simpleRemainder Q split j).comap (endpointMap Q e j) =
        pCore 2 (parabolic L S j) := by
  intro j
  have hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^n) := by
    by_cases he : i=j
    · exact he ▸ hi
    · exact odd_linear_factors_same_degree Q e h split hm i j he hi
  have hV := linear_remainder_le_kernel_of_model Q e h split j hj
  exact ⟨hV,remainder_comap_of_containment Q e split j hV⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

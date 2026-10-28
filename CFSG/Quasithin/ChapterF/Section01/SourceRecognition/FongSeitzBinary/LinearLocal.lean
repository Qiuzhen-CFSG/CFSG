module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.LinearPanelModel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.CubicLocal

/-!
# Fong--Seitz (2B) for the original even linear endpoints

The supplied original quotient Lᵢ/O₂(Lᵢ) is identified with PSL₂ over its
actual finite field. Its Sylow-normalizer cosets identify with the natural
projective line. The explicit affine calculation therefore makes the local
Borel doubly transitive off its base coset. The SAME local-factor map and
endpoint marking transport this action to the full standard-parabolic panel.

The normal two-group regularity theorem now puts U intersect U^sᵢ in the
actual panel kernel. Its pullback is the original endpoint two-core. The
smaller root-generated group consequently identifies with the existing
whole-root local cover, retaining every original quotient representative.
The result holds at either marked endpoint and includes PSL₂(2); no
perfectness of the original factor is required.

Source: Fong--Seitz I (2A)--(2B), pp.7--9, and (5C), pp.25--26;
Aschbacher--Smith F.1.1--3, pp.259--260. The independent apartment/exchange
owner supplies the finite marked quotient and split datum. Nonlinear local
models, local-cover classification and seven-row marked recognition remain
separate obligations; the type VI exception is not discarded.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

set_option backward.isDefEq.respectTransparency false in
private theorem linear_normalizer_two_transitive_off (T : Sylow 2 PSL(2,F)) :
    TwoTransitiveOff (sylowNormalizer T)
      (QuotientGroup.mk 1 : PSL(2,F) ⧸ sylowNormalizer T) := by
  obtain ⟨x,hx⟩ := Linear.normalizer_eq_point_stabilizer F T
  change TwoTransitiveOff (normalizer (T : Set PSL(2,F)))
    (QuotientGroup.mk 1 : PSL(2,F) ⧸ normalizer (T : Set PSL(2,F)))
  rw [hx]
  have hb : Function.Bijective (MulAction.ofQuotientStabilizer PSL(2,F) x) := by
    refine ⟨MulAction.injective_ofQuotientStabilizer _ _, ?_⟩
    intro y
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(2,F) x y
    exact ⟨QuotientGroup.mk g,hg⟩
  let ec := Equiv.ofBijective _ hb
  apply TwoTransitiveOff.pullback (B := MulAction.stabilizer PSL(2,F) x)
    (o := (QuotientGroup.mk 1 : PSL(2,F) ⧸ MulAction.stabilizer PSL(2,F) x))
    (MonoidHom.id PSL(2,F)) ec (by simp)
    (MulAction.ofQuotientStabilizer_smul _ _) (by exact one_smul PSL(2,F) x)
    (LinearPanel.point_two_transitive_off x)

set_option backward.isDefEq.respectTransparency false in
/-- The original local Borel acts doubly transitively on its nonbase cosets,
through its actual two-core quotient and supplied linear model. -/
theorem localBorel_two_transitive_off_linear (i : Fin 2) [Finite (L i)]
    (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    TwoTransitiveOff ((borel (L i) S).subgroupOf (L i))
      (QuotientGroup.mk 1 : (L i) ⧸ (borel (L i) S).subgroupOf (L i)) := by
  let C := sylowNormalizer ((quotientSylow T).mapSurjective (f := μ.toMonoidHom) μ.surjective)
  let B := (borel (L i) S).subgroupOf (L i)
  let f := μ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (L i)))
  let ec := localBorelModelCosetEquiv (L i) S T hT μ
  have hzero : ec (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by
    rw [localBorelModelCosetEquiv_mk,map_one,map_one]
  have hcomap : C.comap f = B := by
    ext l
    change f l ∈ C ↔ l ∈ B
    have heq : (QuotientGroup.mk (f l) : PSL(2,F) ⧸ C) = QuotientGroup.mk 1 ↔
        (QuotientGroup.mk l : (L i) ⧸ B) = QuotientGroup.mk 1 := by
      have hre : ec (QuotientGroup.mk l) = QuotientGroup.mk (f l) :=
        localBorelModelCosetEquiv_mk (L i) S T hT μ l
      rw [← hzero, ← hre]
      exact ec.injective.eq_iff
    simpa only [QuotientGroup.eq, mul_one, inv_mem_iff] using heq
  have hmap : B.map f = C := by
    rw [← hcomap,map_comap_eq_self_of_surjective
      (μ.surjective.comp (QuotientGroup.mk'_surjective _))]
  exact TwoTransitiveOff.pullback f ec hmap
    (localBorelModelCosetEquiv_smul (L i) S T hT μ) hzero
    (linear_normalizer_two_transitive_off _)

variable (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h

/-- Both original endpoint markings carry the linear Borel action to the
full marked panel; no perfectness assumption is needed. -/
theorem linear_borel_two_transitive_off (i : Fin 2) [Finite (L i)]
    (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    TwoTransitiveOff (Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple i}))
      (QuotientGroup.mk 1 : Panel Q i) := by
  apply TwoTransitiveOff.pushforward (factorInEndpoint Q e i) (localBorelPanel Q e h i)
    (B := (borel (L i) S).subgroupOf (L i)) ?_
    (localBorelPanel_smul Q e h i) ?_
    (localBorel_two_transitive_off_linear i T hT μ)
  · apply map_le_iff_le_comap.mpr
    change (borel (L i) S).subgroupOf (L i) ≤ Q.tits.B.comap (factorMap Q e i)
    rw [factor_borel_comap Q e h i]
  · rw [localBorelPanel_mk,map_one]

/-- The full linear branch of Fong--Seitz (2B), including PSL₂(2), for
this SAME original endpoint and quotient map. -/
theorem linear_remainder_le_kernel (i : Fin 2) [Finite (L i)]
    (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    simpleRemainder Q split i ≤ localKernel Q i :=
  remainder_le_kernel_of_two_transitive_off Q split i
    (linear_borel_two_transitive_off Q e h i T hT μ)

/-- Extract the genuine local-model field, retaining all binary parameters. -/
theorem linear_remainder_le_kernel_of_model (i : Fin 2) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  let := h.finite_local i
  obtain ⟨K,hK,hfin,hcard,⟨μ⟩⟩ := hmodel
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨T,hT⟩ := h.sylow i
  exact linear_remainder_le_kernel Q e h split i T hT μ

omit h in
/-- Pulling back the regular remainder gives the ORIGINAL endpoint two-core,
not the possibly larger full permutation kernel. -/
theorem remainder_comap_of_containment (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i) := by
  rw [remainder_eq_unipotent_inf_kernel Q split i hV]
  change (LocalCover.radical Q split i).comap (endpointMap Q e i) = _
  rw [PanelKernel.radical_eq_parabolic_twoCore Q split i,
    ← pCore_map_iso 2 (endpoint Q e i), map_map]
  change ((pCore 2 (parabolic L S i)).map (endpointMap Q e i)).comap (endpointMap Q e i) = _
  have hinj : Function.Injective (endpointMap Q e i) :=
    (Q.tits.standardParabolic {Q.simple i}).subtype_injective.comp (endpoint Q e i).injective
  exact comap_map_eq_self_of_injective hinj _

/-- The original linear endpoint identifies its canonical remainder with its two-core. -/
theorem linear_remainder_comap (i : Fin 2) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) :
    (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i) :=
  remainder_comap_of_containment Q e split i
    (linear_remainder_le_kernel_of_model Q e h split i hmodel)

/-- The smaller root-generated group gives the actual whole-root cover on
every even linear branch, with the (2B) premise discharged. -/
def originalLinearRootCover (i : Fin 2) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalRankOne Q e split i ≃*
      originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i :=
  originalRootCoverEquiv Q e h split i
    (linear_remainder_le_kernel_of_model Q e h split i hmodel)

@[simp] theorem originalLinearRootCover_apply (i : Fin 2) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n))
    (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalLinearRootCover Q e h split i hmodel r = QuotientGroup.mk'
      (originalRadicalInClosure Q e split i)
        (inclusion (originalRankOne_le_localClosure Q e split i) r) :=
  originalRootCoverEquiv_apply Q e h split i
    (linear_remainder_le_kernel_of_model Q e h split i hmodel) r

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.CubicLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootLocalCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearRootCoordinates

/-!
# The cubic source remainder and its original root group

An original PSL2(2) quotient makes the local Borel panel have three
points, without a perfectness assumption. Its canonical root has order
two. The index-two argument now discharges Fong--Seitz (2B), and the
same endpoint marking pulls the remainder back to the actual original
parabolic two-core. The root-generated group acts as the full symmetric
group on the same panel, with every action value and local-cover quotient
representative preserved.

Source: Fong--Seitz I (2B), p.9, and the binary linear case of (5C)(b),
pp.25--26; Aschbacher--Smith F.1.1--3, pp.259--260. The finite marked
quotient and its split datum are still supplied by the independent
apartment/exchange construction. These local results do not assert a
seven-row amalgam comparison or eliminate the degree-nine type VI case.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
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
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)

include e h

theorem simpleRoot_card_binary
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2) :
    Nat.card (simpleRoot Q split i) = 2 := by
  let := h.finite_local i
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by simpa only [Nat.card_eq_fintype_card, pow_one] using hcard)
  obtain ⟨T,hT⟩ := h.sylow i
  exact (simpleRoot_card_linear Q e h split i T hT μ).trans hcard

theorem binary_remainder_le_kernel
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2) :
    simpleRemainder Q split i ≤ localKernel Q i :=
  PanelKernel.remainder_le_kernel_of_root_card_two Q split i
    (simpleRoot_card_binary Q e h split i hmodel)

omit h in
/-- Identification with the ORIGINAL endpoint two-core, not the full panel kernel. -/
theorem remainder_comap_of_root_card_two
    (hc : Nat.card (simpleRoot Q split i) = 2) :
    (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i) := by
  rw [remainder_eq_unipotent_inf_kernel Q split i
    (PanelKernel.remainder_le_kernel_of_root_card_two Q split i hc)]
  change (LocalCover.radical Q split i).comap (endpointMap Q e i) = _
  rw [PanelKernel.radical_eq_parabolic_twoCore Q split i,
    ← pCore_map_iso 2 (endpoint Q e i), map_map]
  change ((pCore 2 (parabolic L S i)).map (endpointMap Q e i)).comap (endpointMap Q e i) = _
  have hinj : Function.Injective (endpointMap Q e i) :=
    (Q.tits.standardParabolic {Q.simple i}).subtype_injective.comp (endpoint Q e i).injective
  exact comap_map_eq_self_of_injective hinj _

theorem binary_remainder_comap
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2) :
    (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i) :=
  remainder_comap_of_root_card_two Q e split i (simpleRoot_card_binary Q e h split i hmodel)

/-- The original binary root group acts as the full symmetric group of its literal panel. -/
def originalBinaryRootEquiv
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2) :
    originalRankOne Q e split i ≃* Equiv.Perm (Panel Q i) :=
  (originalRankOneEquiv Q e split i).trans (PanelKernel.cubicRootEquiv Q split i
    (simpleRoot_card_binary Q e h split i hmodel))

@[simp] theorem originalBinaryRootEquiv_apply
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (r : originalRankOne Q e split i) :
    originalBinaryRootEquiv Q e h split i hmodel r =
      (originalRootProjection Q e split i r : Equiv.Perm (Panel Q i)) := by
  rw [originalBinaryRootEquiv, MulEquiv.trans_apply, PanelKernel.cubicRootEquiv_apply,
    originalRootProjection_apply]

/-- Every point is acted on by the same original endpoint marking. -/
theorem originalBinaryRootEquiv_point
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (r : originalRankOne Q e split i) (c : Panel Q i) :
    originalBinaryRootEquiv Q e h split i hmodel r c = endpoint Q e i r.val • c := by
  rw [originalBinaryRootEquiv_apply,originalRootProjection_apply,localAction_eq_panelAction]
  change (⟨(originalRankOneEquiv Q e split i r : X ⧸ Q.D), _⟩ :
    Q.tits.standardParabolic {Q.simple i}) • c = endpoint Q e i r.val • c
  congr 1
  apply Subtype.ext
  exact originalRankOneEquiv_apply Q e split i r

/-- Both lifts of the same binary source use the full earlier local-cover quotient. -/
def originalBinaryRootCover
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalRankOne Q e split i ≃*
      originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i :=
  originalRootCoverEquiv Q e h split i (binary_remainder_le_kernel Q e h split i hmodel)

@[simp] theorem originalBinaryRootCover_apply
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 2)
    (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    originalBinaryRootCover Q e h split i hmodel r = QuotientGroup.mk'
      (originalRadicalInClosure Q e split i)
        (inclusion (originalRankOne_le_localClosure Q e split i) r) :=
  originalRootCoverEquiv_apply Q e h split i
    (binary_remainder_le_kernel Q e h split i hmodel) r

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

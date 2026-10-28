module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TriangleStructure.NaturalRadicals
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TriangleStructure.LinearRadicals
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitarySpecialRadical

/-!
# Natural coordinates on the original triangle cores

The two-root geometry gives a natural SL₂ action on the whole triangle
radical. Restricting the full endpoint marking to its intrinsic two-core
transports those coordinates to the original source. The conjugation
formula keeps the same endpoint map and the actual root-generated actor.
SL₂ transitivity then makes all nonidentity elements of each original core
conjugate by representatives of that actor.

One original linear factor suffices: odd opposition identifies both factors
over the same binary degree and supplies their regularity. Both endpoint
orientations and the field of order two are included, without assuming
perfectness, irreducibility or an earlier natural-action record. These are
inputs for the projective-plane step; no final A₂ comparison is asserted.
Source: Fong--Seitz I (3E), printed p.14, and DGS, Groups and Graphs (1985),
(5.12), (10.5), printed pp.113--114,156; AS F.1.1--3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TriangleStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include h in
private theorem core_coordinates_transport
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 3)
    (hV : ∀ j, simpleRemainder Q split j ≤ localKernel Q j)
    (hE : ∀ j, IsElementaryAbelian 2 (simpleRoot Q split j))
    (j : Fin 2) (μ : rankOne Q split j ≃* SL(2,F)) :
    ∃ c : (parabolic L S j).pCoreIn 2 ≃* Multiplicative (Fin 2 → F),
      ∀ (a : parabolic L S j) (r : rankOne Q split j),
        endpointMap Q e j a = r → ∀ v : (parabolic L S j).pCoreIn 2,
          ∃ w : (parabolic L S j).pCoreIn 2,
            (w : G) = (a : G)*(v : G)*(a : G)⁻¹ ∧
            (c w).toAdd = Matrix.mulVec (μ r).val (c v).toAdd := by
  let := Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.remainder_elementary
    Q split hm hV hE j
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨d,hd⟩ := Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.radical_natural_coordinates
    Q split hm hV hE j μ
  let ec := QuadrangleStructure.markedCoreEquiv Q e h split j (hV j)
  let dc : simpleRemainder Q split j ≃* Multiplicative (Fin 2 → F) :=
    d.toAddEquiv.toMultiplicative
  let c := ec.trans dc
  have hle : (parabolic L S j).pCoreIn 2 ≤ parabolic L S j := pCoreIn_le _ _
  have hec (v : (parabolic L S j).pCoreIn 2) :
      (ec v : X ⧸ Q.D) = endpointMap Q e j ⟨v,hle v.property⟩ := by
    rw [QuadrangleStructure.markedCoreEquiv_apply]
    exact (endpoint_sylow Q e h j ⟨v,h.parabolic_core_le_S j v.property⟩).symm
  refine ⟨c,?_⟩
  intro a r ha v
  let z := radicalAction Q split j (hV j) r (ec v)
  let w := ec.symm z
  have hw : ec w = z := ec.apply_symm_apply z
  refine ⟨w,?_,?_⟩
  · have hmap : endpointMap Q e j ⟨w,hle w.property⟩ =
        endpointMap Q e j (a*⟨v,hle v.property⟩*a⁻¹) := by
      rw [←hec,hw,radicalAction_apply,hec,map_mul,map_mul,map_inv,ha]
    have hinj : Function.Injective (endpointMap Q e j) :=
      (Q.tits.standardParabolic {Q.simple j}).subtype_injective.comp (endpoint Q e j).injective
    exact congrArg Subtype.val (hinj hmap)
  · change d (Additive.ofMul (ec w)) = Matrix.mulVec (μ r).val (d (Additive.ofMul (ec v)))
    rw [hw]
    exact hd r (Additive.ofMul (ec v))

include e h split in
/-- One original linear factor in a triangle constructs natural coordinates
on either original full parabolic core. Every acting representative retains
the same endpoint map. No core structure or natural-action premise is supplied. -/
theorem original_natural_cores (hm : rotationOrder Q = 3)
    (i : Fin 2) {n : ℕ}
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) (j : Fin 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2^n ∧
      ∃ (μ : rankOne Q split j ≃* SL(2,F))
        (c : (parabolic L S j).pCoreIn 2 ≃* Multiplicative (Fin 2 → F)),
        ∀ (a : parabolic L S j) (r : rankOne Q split j),
          endpointMap Q e j a = r → ∀ v : (parabolic L S j).pCoreIn 2,
            ∃ w : (parabolic L S j).pCoreIn 2,
              (w : G) = (a : G)*(v : G)*(a : G)⁻¹ ∧
              (c w).toAdd = Matrix.mulVec (μ r).val (c v).toAdd := by
  have hV (k : Fin 2) := (odd_linear_regularity Q e h split (hm ▸ (by decide : Odd 3)) i hi k).1
  have hE (k : Fin 2) := elementary_root_of_linear_factor Q e h split k
    (original_linear_factors Q e h split hm i hi k)
  obtain ⟨F,hF,hfin,hcard,⟨ν⟩⟩ := original_linear_factors Q e h split hm i hi j
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨f,hf,hk,_⟩ := linear_actor_quotient_of_factor Q e h split j ν
  let A := (S ⊔ L j).subgroupOf (parabolic L S j)
  let : A.Normal := QuadrangleStructure.marked_sylow_factor_normal Q e h split j
  obtain ⟨μ,_⟩ := QuadrangleStructure.marked_linear_rankOne Q e h split j
    (UnitarySource.actorReflection Q split j) (hV j) A (subgroupOf_mono _ le_sup_left) f hf hk
  obtain ⟨c,hc⟩ := core_coordinates_transport Q e h split hm hV hE j μ
  exact ⟨F,hF,hfin,inferInstance,hcard,μ,c,hc⟩

include e h split in
/-- Every nonidentity element of an original triangle core is conjugate to
any other by a representative of the actual root-generated rank-one group. -/
theorem original_core_nonidentity_conjugate (hm : rotationOrder Q = 3)
    (i : Fin 2) {n : ℕ}
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) (j : Fin 2)
    (x y : (parabolic L S j).pCoreIn 2) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : parabolic L S j, endpointMap Q e j a ∈ rankOne Q split j ∧
      (a : G)*(x : G)*(a : G)⁻¹ = (y : G) := by
  obtain ⟨F,hF,hfin,hchar,hcard,μ,c,hc⟩ := original_natural_cores Q e h split hm i hi j
  have hnonzero (z : (parabolic L S j).pCoreIn 2) (hz : z ≠ 1) : (c z).toAdd ≠ 0 := by
    intro he
    exact hz (c.injective ((show c z = 1 from he).trans c.map_one.symm))
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F (c x).toAdd (c y).toAdd
    (hnonzero x hx) (hnonzero y hy)
  let r := μ.symm g
  let a := (endpoint Q e j).symm ⟨r,rankOne_le_parabolic Q split j r.property⟩
  have ha : endpointMap Q e j a = r :=
    congrArg Subtype.val ((endpoint Q e j).apply_symm_apply _)
  obtain ⟨z,hz,hcz⟩ := hc a r ha x
  have hzy : z = y := by
    apply c.injective
    change (c z).toAdd = (c y).toAdd
    rw [hcz,show μ r = g from μ.apply_symm_apply g]
    exact hg
  exact ⟨a,ha ▸ r.property,hz.symm.trans (congrArg Subtype.val hzy)⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TriangleStructure

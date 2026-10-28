module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.Point
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Triangle
public import Theory.AtlasPort.OtherSporadic.Families.Alternating.Stabilizers

/-!
# The point-centralizer intersection in the model amalgam

Fixed matrices over the actual four-element fixed subfield identify the
intersection with its upper triangular group times the field actor. Its
order is 24. Inside A₅ × C₂, an order-24 subgroup is a point stabilizer
times C₂: its order-twelve projection contains a Sylow four-group and lies
in its normalizer. The five-point action identifies that stabilizer with A₄.
Thus the literal intersection has type A₄ × C₂.

The subgroup-location argument follows the existing `Seventeen/Triangle`
proof. The final four-letter identification reuses the licensed ATLAS
stabilizer API; its attribution remains in the imported module.

Source: Baumeister, *A geometry for groups of J₃-type* (2007), p.498,
the model instance of Lemma 2.7(iii) used in Corollary 2.10.
-/

public noncomputable section
open Subgroup MulAction Matrix
open BenderSuzuki.Converse Theory.PSL2 Theory.PSL2.BinaryFourFieldExtension
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
abbrev FixedField := FixedBy.subfield F fieldInvolution

def fixedMatrixHom : SL2 FixedField →* BinaryGroup 4 :=
  (quotientMap F).comp (SpecialLinearGroup.map FixedField.subtype)

theorem fixedMatrixHom_injective : Function.Injective fixedMatrixHom := by
  intro A B h
  have hh := quotientMap_injective F h
  apply Subtype.ext
  ext i j
  exact congrArg (fun M : SL2 F => M.val i j) hh

theorem fixedMatrixHom_mem (A : SL2 FixedField) : fixedMatrixHom A ∈ Fixed := by
  rw [MulAut.mem_fixedSubgroup]
  change fieldAut fieldInvolution (quotientMap F _) = quotientMap F _
  rw [fieldAut_apply_quotientMap]
  apply congrArg (quotientMap F)
  apply Subtype.ext
  ext i j
  exact (A.val i j).property

def fixedMatrixEquiv : SL2 FixedField ≃* Fixed :=
  MulEquiv.ofBijective (fixedMatrixHom.codRestrict Fixed fixedMatrixHom_mem) (by
    constructor
    · intro A B h
      exact fixedMatrixHom_injective (congrArg Subtype.val h)
    · intro x
      obtain ⟨A, hA⟩ := quotientMap_surjective F x.val
      have hf : SpecialLinearGroup.map fieldInvolution.toRingHom A = A := by
        apply quotientMap_injective F
        rw [← fieldAut_apply_quotientMap, hA]
        exact (MulAut.mem_fixedSubgroup _ _).mp x.property
      have hentry (i j : Fin 2) : fieldInvolution (A.val i j) = A.val i j :=
        congrArg (fun M : SL2 F => M.val i j) hf
      let Bmat : Matrix (Fin 2) (Fin 2) FixedField := fun i j => ⟨A.val i j, hentry i j⟩
      let B : SL2 FixedField := ⟨Bmat, by
        apply FixedField.subtype.injective
        exact (FixedField.subtype.map_det Bmat).trans A.property⟩
      exact ⟨B, Subtype.ext hA⟩)

theorem fixedMatrix_mem_borel (A : SL2 FixedField) :
    fixedMatrixHom A ∈ PBorel F ↔ A ∈ Borel FixedField := by
  rw [PBorel_eq_map, mem_Borel_iff]
  constructor
  · rintro ⟨B, hB, he⟩
    have hh : B = SpecialLinearGroup.map FixedField.subtype A := quotientMap_injective F he
    have hz := (mem_Borel_iff B).mp hB
    rw [hh] at hz
    exact Subtype.ext hz
  · intro h
    refine ⟨SpecialLinearGroup.map FixedField.subtype A, ?_, rfl⟩
    apply (mem_Borel_iff _).mpr
    exact congrArg Subtype.val h

def pointTriangleHom : (Borel FixedField × Actor) →* Model where
  toFun x := ⟨fixedMatrixHom x.1, x.2⟩
  map_one' := by apply SemidirectProduct.ext <;> simp
  map_mul' x y := by
    apply SemidirectProduct.ext
    · change fixedMatrixHom (x.1.val * y.1.val) =
        fixedMatrixHom x.1.val * action x.2 (fixedMatrixHom y.1.val)
      rw [actor_fixes x.2 ⟨_, fixedMatrixHom_mem y.1.val⟩, map_mul]
    · rfl

theorem pointTriangleHom_injective : Function.Injective pointTriangleHom := by
  intro x y h
  apply Prod.ext
  · exact Subtype.ext (fixedMatrixHom_injective (congrArg (fun z : Model => z.left) h))
  · exact congrArg (fun z : Model => z.right) h

theorem pointTriangleHom_range : pointTriangleHom.range = point ⊓ Triangle := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(mem_point _).mpr ((fixedMatrix_mem_borel _).mpr y.1.property),
      (mem_triangle _).mpr (fixedMatrixHom_mem _)⟩
  · intro hx
    obtain ⟨A, hA⟩ := fixedMatrixEquiv.surjective ⟨x.left, (mem_triangle _).mp hx.2⟩
    have he : fixedMatrixHom A = x.left := congrArg Subtype.val hA
    have hB : A ∈ Borel FixedField := (fixedMatrix_mem_borel A).mp (he.symm ▸ (mem_point _).mp hx.1)
    exact ⟨(⟨A,hB⟩, x.right), SemidirectProduct.ext he rfl⟩

def pointTriangleCoordinates : (point ⊓ Triangle : Subgroup Model) ≃* (Borel FixedField × Actor) :=
  ((MonoidHom.ofInjective pointTriangleHom_injective).trans
    (MulEquiv.subgroupCongr pointTriangleHom_range)).symm

theorem fixed_borel_card : Nat.card (Borel FixedField) = 12 := by
  have hp : Nat.card (P1 FixedField) = 5 := by
    rw [Projectivization.card_of_finrank_two FixedField (Fin 2 → FixedField) (by simp), fixedField_card]
  have hg : Nat.card (SL2 FixedField) = 60 := by
    rw [Atlas.card_sl_two, fixedField_card]
    norm_num
  have hi : (Borel FixedField).index = 5 := by
    rw [Borel, index_stabilizer_of_transitive, hp]
  have hc := (Borel FixedField).card_mul_index
  rw [hi,hg] at hc
  omega

theorem point_triangle_card : Nat.card (point ⊓ Triangle : Subgroup Model) = 24 := by
  rw [Nat.card_congr pointTriangleCoordinates.toEquiv, Nat.card_prod,
    fixed_borel_card, Nat.card_zpowers, fieldInvolution_order]

private theorem a5_card : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.card_fin, Nat.factorial]

private theorem a5_twelve_stabilizer (P : Subgroup A5) (hc : Nat.card P = 12) :
    ∃ i : Fin 5, P = stabilizer A5 i := by
  let Q : Sylow 2 P := default
  have hQ : Nat.card Q = 4 := by
    rw [Q.card_eq_multiplicity, hc]
    decide +kernel
  let R : Sylow 2 A5 := Sylow.ofCard ((Q : Subgroup P).map P.subtype) (by
    rw [card_map_of_injective P.subtype_injective, hQ, a5_card]
    decide +kernel)
  have hRP : (R : Subgroup A5) ≤ P := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hp : P ≠ ⊤ := by
    intro he
    rw [he, Subgroup.card_top, a5_card] at hc
    omega
  have hPN := Theory.SpecificGroups.Alternating.FiveSylowMaximal.overgroup_le_sylow_normalizer R P hRP hp
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
  refine ⟨i, eq_of_le_of_card_ge (hi ▸ hPN) ?_⟩
  have hs : ∀ j : Fin 5, Nat.card (stabilizer A5 j) = 12 := by
    intro j
    rw [Nat.card_eq_fintype_card]
    revert j
    decide +kernel
  rw [hs,hc]

private theorem triangle_point_subgroup (P : Subgroup TriangleGroup) (hc : Nat.card P = 24) :
    ∃ i : Fin 5, P = (stabilizer A5 i).prod (⊤ : Subgroup C2) := by
  let Q := P.map (MonoidHom.fst A5 C2)
  have h24 : Nat.card Q ∣ 24 := hc ▸ card_map_dvd P (MonoidHom.fst A5 C2)
  have h60 : Nat.card Q ∣ 60 := by simpa only [a5_card] using Q.card_subgroup_dvd_card
  have h12 : Nat.card Q ∣ 12 := Nat.dvd_gcd h24 h60
  have hle : P ≤ Q.prod (⊤ : Subgroup C2) := fun x hx => ⟨mem_map.mpr ⟨x,hx,rfl⟩,mem_top _⟩
  have hb := card_le_of_le hle
  have h2 : Nat.card C2 = 2 := by
    norm_num [C2, Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  have hprod : Nat.card (Q.prod (⊤ : Subgroup C2)) = Nat.card Q * Nat.card C2 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, card_top]
  rw [hprod,h2] at hb
  have hp : Nat.card Q = 12 := by
    have hu := Nat.le_of_dvd (by decide : 0 < 12) h12
    rw [hc] at hb
    omega
  obtain ⟨i,hi⟩ := a5_twelve_stabilizer Q hp
  refine ⟨i, eq_of_le_of_card_ge (hi ▸ hle) ?_⟩
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, card_top, h2, ← hi, hp, hc]

private def a5StabilizerEquiv (i : Fin 5) : stabilizer A5 i ≃* alternatingGroup (Fin 4) := by
  let e : Fin 1 ↪ Fin 5 := ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩
  have he : stabilizer A5 i = Atlas.Families.Alternating.PointwiseStabilizer e := by
    ext g
    rw [Atlas.Families.Alternating.mem_pointwiseStabilizer]
    change (g.val i = i) ↔ ∀ j : Fin 1, g.val (e j) = e j
    exact ⟨fun h _ => h, fun h => h 0⟩
  exact (MulEquiv.subgroupCongr he).trans (Atlas.Families.Alternating.stabilizerEquiv e)

def overlap13 : (point ⊓ Triangle : Subgroup Model) ≃*
    (alternatingGroup (Fin 4) × Multiplicative (ZMod 2)) := by
  let P := (point ⊓ Triangle).subgroupOf Triangle
  let eP := subgroupOfEquivOfLe (inf_le_right : point ⊓ Triangle ≤ Triangle)
  let Q := P.map triangleEquiv.toMonoidHom
  have hQ : Nat.card Q = 24 := by
    rw [card_map_of_injective triangleEquiv.injective, Nat.card_congr eP.toEquiv, point_triangle_card]
  let i := (triangle_point_subgroup Q hQ).choose
  have hi := (triangle_point_subgroup Q hQ).choose_spec
  exact eP.symm.trans ((equivMapOfInjective P triangleEquiv.toMonoidHom triangleEquiv.injective).trans
    ((MulEquiv.subgroupCongr hi).trans ((Subgroup.prodEquiv _ _).trans
      (MulEquiv.prodCongr (a5StabilizerEquiv i) (Subgroup.topEquiv)))))

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
